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
uint8_t v___x_2007__boxed_324_; size_t v_i_boxed_325_; size_t v_stop_boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v___x_2007__boxed_324_ = lean_unbox(v___x_320_);
v_i_boxed_325_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_stop_boxed_326_ = lean_unbox_usize(v_stop_323_);
lean_dec(v_stop_323_);
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_319_, v___x_2007__boxed_324_, v_as_321_, v_i_boxed_325_, v_stop_boxed_326_);
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
uint8_t v___y_4233__boxed_636_; uint8_t v_suppressElabErrors_boxed_637_; uint8_t v_res_638_; lean_object* v_r_639_; 
v___y_4233__boxed_636_ = lean_unbox(v___y_633_);
v_suppressElabErrors_boxed_637_ = lean_unbox(v_suppressElabErrors_634_);
v_res_638_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v___y_4233__boxed_636_, v_suppressElabErrors_boxed_637_, v_x_635_);
lean_dec(v_x_635_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* v_ref_641_, lean_object* v_msgData_642_, uint8_t v_severity_643_, uint8_t v_isSilent_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
uint8_t v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; uint8_t v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_687_; uint8_t v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; uint8_t v___y_691_; lean_object* v___y_692_; uint8_t v___y_693_; lean_object* v___y_694_; lean_object* v___y_712_; uint8_t v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; uint8_t v___y_717_; uint8_t v___y_718_; lean_object* v___y_719_; lean_object* v___y_723_; uint8_t v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; uint8_t v___y_728_; uint8_t v___y_729_; uint8_t v___x_734_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; uint8_t v___y_739_; lean_object* v___y_740_; uint8_t v___y_741_; uint8_t v___y_742_; uint8_t v___y_744_; uint8_t v___x_759_; 
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
lean_inc(v_openDecls_662_);
lean_inc(v_currNamespace_661_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_currNamespace_661_);
lean_ctor_set(v___x_675_, 1, v_openDecls_662_);
v___x_676_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___y_655_);
lean_inc_ref(v___y_656_);
lean_inc_ref(v___y_652_);
v___x_677_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_677_, 0, v___y_652_);
lean_ctor_set(v___x_677_, 1, v___y_654_);
lean_ctor_set(v___x_677_, 2, v___y_653_);
lean_ctor_set(v___x_677_, 3, v___y_656_);
lean_ctor_set(v___x_677_, 4, v___x_676_);
lean_ctor_set_uint8(v___x_677_, sizeof(void*)*5, v___y_651_);
lean_ctor_set_uint8(v___x_677_, sizeof(void*)*5 + 1, v___y_657_);
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
lean_inc_ref_n(v___y_690_, 2);
v___x_701_ = l_Lean_FileMap_toPosition(v___y_690_, v___y_692_);
lean_dec(v___y_692_);
v___x_702_ = l_Lean_FileMap_toPosition(v___y_690_, v___y_694_);
lean_dec(v___y_694_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
v___x_704_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_691_ == 0)
{
lean_del_object(v___x_699_);
lean_dec_ref(v___y_687_);
v___y_651_ = v___y_688_;
v___y_652_ = v___y_689_;
v___y_653_ = v___x_703_;
v___y_654_ = v___x_701_;
v___y_655_ = v_a_697_;
v___y_656_ = v___x_704_;
v___y_657_ = v___y_693_;
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
v___y_651_ = v___y_688_;
v___y_652_ = v___y_689_;
v___y_653_ = v___x_703_;
v___y_654_ = v___x_701_;
v___y_655_ = v_a_697_;
v___y_656_ = v___x_704_;
v___y_657_ = v___y_693_;
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
v___x_720_ = l_Lean_Syntax_getTailPos_x3f(v___y_716_, v___y_713_);
lean_dec(v___y_716_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_inc(v___y_719_);
v___y_687_ = v___y_712_;
v___y_688_ = v___y_713_;
v___y_689_ = v___y_715_;
v___y_690_ = v___y_714_;
v___y_691_ = v___y_717_;
v___y_692_ = v___y_719_;
v___y_693_ = v___y_718_;
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
v___y_688_ = v___y_713_;
v___y_689_ = v___y_715_;
v___y_690_ = v___y_714_;
v___y_691_ = v___y_717_;
v___y_692_ = v___y_719_;
v___y_693_ = v___y_718_;
v___y_694_ = v_val_721_;
goto v___jp_686_;
}
}
v___jp_722_:
{
lean_object* v_ref_730_; lean_object* v___x_731_; 
v_ref_730_ = l_Lean_replaceRef(v_ref_641_, v___y_725_);
v___x_731_ = l_Lean_Syntax_getPos_x3f(v_ref_730_, v___y_724_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___y_712_ = v___y_723_;
v___y_713_ = v___y_724_;
v___y_714_ = v___y_727_;
v___y_715_ = v___y_726_;
v___y_716_ = v_ref_730_;
v___y_717_ = v___y_728_;
v___y_718_ = v___y_729_;
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
v___y_713_ = v___y_724_;
v___y_714_ = v___y_727_;
v___y_715_ = v___y_726_;
v___y_716_ = v_ref_730_;
v___y_717_ = v___y_728_;
v___y_718_ = v___y_729_;
v___y_719_ = v_val_733_;
goto v___jp_711_;
}
}
v___jp_735_:
{
if (v___y_742_ == 0)
{
v___y_723_ = v___y_740_;
v___y_724_ = v___y_741_;
v___y_725_ = v___y_736_;
v___y_726_ = v___y_738_;
v___y_727_ = v___y_737_;
v___y_728_ = v___y_739_;
v___y_729_ = v_severity_643_;
goto v___jp_722_;
}
else
{
v___y_723_ = v___y_740_;
v___y_724_ = v___y_741_;
v___y_725_ = v___y_736_;
v___y_726_ = v___y_738_;
v___y_727_ = v___y_737_;
v___y_728_ = v___y_739_;
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
v___y_736_ = v_ref_748_;
v___y_737_ = v_fileMap_746_;
v___y_738_ = v_fileName_745_;
v___y_739_ = v_suppressElabErrors_749_;
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
v___y_736_ = v_ref_748_;
v___y_737_ = v_fileMap_746_;
v___y_738_ = v_fileName_745_;
v___y_739_ = v_suppressElabErrors_749_;
v___y_740_ = v___f_752_;
v___y_741_ = v___y_744_;
v___y_742_ = v___x_756_;
goto v___jp_735_;
}
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; 
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
lean_dec_ref(v___y_767_);
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
v___x_782_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_781_, v_msgData_773_, v_severity_774_, v_isSilent_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
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
lean_dec_ref(v___y_788_);
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
lean_dec_ref(v___y_806_);
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
lean_dec_ref(v_a_924_);
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
v___x_933_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
lean_ctor_set(v___x_933_, 2, v___x_932_);
lean_ctor_set(v___x_933_, 3, v___x_932_);
lean_ctor_set(v___x_933_, 4, v___x_931_);
lean_ctor_set(v___x_933_, 5, v___x_931_);
lean_ctor_set(v___x_933_, 6, v___x_931_);
lean_ctor_set(v___x_933_, 7, v___x_931_);
lean_ctor_set(v___x_933_, 8, v___x_931_);
lean_ctor_set(v___x_933_, 9, v___x_931_);
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
lean_dec_ref(v_a_1013_);
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
lean_object* v_fileName_1212_; lean_object* v_fileMap_1213_; lean_object* v_options_1214_; lean_object* v_currRecDepth_1215_; lean_object* v_maxRecDepth_1216_; lean_object* v_ref_1217_; lean_object* v_currNamespace_1218_; lean_object* v_openDecls_1219_; lean_object* v_initHeartbeats_1220_; lean_object* v_maxHeartbeats_1221_; lean_object* v_quotContext_1222_; lean_object* v_currMacroScope_1223_; uint8_t v_diag_1224_; lean_object* v_cancelTk_x3f_1225_; uint8_t v_suppressElabErrors_1226_; lean_object* v_inheritedTraceOptions_1227_; lean_object* v_ref_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
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
v_ref_1228_ = l_Lean_replaceRef(v_ref_1205_, v_ref_1217_);
lean_inc_ref(v_inheritedTraceOptions_1227_);
lean_inc(v_cancelTk_x3f_1225_);
lean_inc(v_currMacroScope_1223_);
lean_inc(v_quotContext_1222_);
lean_inc(v_maxHeartbeats_1221_);
lean_inc(v_initHeartbeats_1220_);
lean_inc(v_openDecls_1219_);
lean_inc(v_currNamespace_1218_);
lean_inc(v_maxRecDepth_1216_);
lean_inc(v_currRecDepth_1215_);
lean_inc_ref(v_options_1214_);
lean_inc_ref(v_fileMap_1213_);
lean_inc_ref(v_fileName_1212_);
v___x_1229_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1229_, 0, v_fileName_1212_);
lean_ctor_set(v___x_1229_, 1, v_fileMap_1213_);
lean_ctor_set(v___x_1229_, 2, v_options_1214_);
lean_ctor_set(v___x_1229_, 3, v_currRecDepth_1215_);
lean_ctor_set(v___x_1229_, 4, v_maxRecDepth_1216_);
lean_ctor_set(v___x_1229_, 5, v_ref_1228_);
lean_ctor_set(v___x_1229_, 6, v_currNamespace_1218_);
lean_ctor_set(v___x_1229_, 7, v_openDecls_1219_);
lean_ctor_set(v___x_1229_, 8, v_initHeartbeats_1220_);
lean_ctor_set(v___x_1229_, 9, v_maxHeartbeats_1221_);
lean_ctor_set(v___x_1229_, 10, v_quotContext_1222_);
lean_ctor_set(v___x_1229_, 11, v_currMacroScope_1223_);
lean_ctor_set(v___x_1229_, 12, v_cancelTk_x3f_1225_);
lean_ctor_set(v___x_1229_, 13, v_inheritedTraceOptions_1227_);
lean_ctor_set_uint8(v___x_1229_, sizeof(void*)*14, v_diag_1224_);
lean_ctor_set_uint8(v___x_1229_, sizeof(void*)*14 + 1, v_suppressElabErrors_1226_);
v___x_1230_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1206_, v___y_1207_, v___y_1208_, v___x_1229_, v___y_1210_);
lean_dec_ref(v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1231_, lean_object* v_msg_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1231_, v_msg_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v_ref_1231_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1239_, lean_object* v_msg_1240_, lean_object* v_declHint_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; lean_object* v_a_1248_; lean_object* v___x_1249_; 
v___x_1247_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1240_, v_declHint_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref(v___x_1247_);
v___x_1249_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1239_, v_a_1248_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1250_, lean_object* v_msg_1251_, lean_object* v_declHint_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1250_, v_msg_1251_, v_declHint_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v_ref_1250_);
return v_res_1258_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1261_ = l_Lean_stringToMessageData(v___x_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1262_, lean_object* v_constName_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1269_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1270_ = 0;
lean_inc(v_constName_1263_);
v___x_1271_ = l_Lean_MessageData_ofConstName(v_constName_1263_, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1269_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1262_, v___x_1274_, v_constName_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1276_, lean_object* v_constName_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1276_, v_constName_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v_ref_1276_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_constName_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_ref_1290_; lean_object* v___x_1291_; 
v_ref_1290_ = lean_ctor_get(v___y_1287_, 5);
v___x_1291_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1290_, v_constName_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* v_constName_1299_, uint8_t v_skipRealize_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; lean_object* v_env_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_st_ref_get(v___y_1304_);
v_env_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc_ref(v_env_1307_);
lean_dec(v___x_1306_);
lean_inc(v_constName_1299_);
v___x_1308_ = l_Lean_Environment_findAsync_x3f(v_env_1307_, v_constName_1299_, v_skipRealize_1300_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1299_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
return v___x_1309_;
}
else
{
lean_object* v_val_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec(v_constName_1299_);
v_val_1310_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1308_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_val_1310_);
lean_dec(v___x_1308_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set_tag(v___x_1312_, 0);
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_val_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* v_constName_1318_, lean_object* v_skipRealize_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
uint8_t v_skipRealize_boxed_1325_; lean_object* v_res_1326_; 
v_skipRealize_boxed_1325_ = lean_unbox(v_skipRealize_1319_);
v_res_1326_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1318_, v_skipRealize_boxed_1325_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* v_declName_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; lean_object* v_env_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1330_ = lean_st_ref_get(v___y_1328_);
v_env_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc_ref(v_env_1331_);
lean_dec(v___x_1330_);
v___x_1332_ = lean_get_reducibility_status(v_env_1331_, v_declName_1327_);
v___x_1333_ = lean_box(v___x_1332_);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_declName_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1335_, v___y_1336_);
lean_dec(v___y_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* v_declName_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1361_; 
v___x_1345_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1339_, v___y_1343_);
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1361_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1361_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
uint8_t v___x_1350_; 
v___x_1350_ = lean_unbox(v_a_1346_);
lean_dec(v_a_1346_);
if (v___x_1350_ == 0)
{
uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = 1;
v___x_1352_ = lean_box(v___x_1351_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1352_);
v___x_1354_ = v___x_1348_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
else
{
uint8_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1356_ = 0;
v___x_1357_ = lean_box(v___x_1356_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1357_);
v___x_1359_ = v___x_1348_;
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
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* v_declName_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1368_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
v___x_1371_ = l_Lean_stringToMessageData(v___x_1370_);
return v___x_1371_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
v___x_1374_ = l_Lean_stringToMessageData(v___x_1373_);
return v___x_1374_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
v___x_1377_ = l_Lean_stringToMessageData(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
v___x_1380_ = l_Lean_stringToMessageData(v___x_1379_);
return v___x_1380_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* v_params_1384_, lean_object* v_id_1385_, lean_object* v_declName_1386_, lean_object* v_kind_1387_, uint8_t v_minIndexable_1388_, uint8_t v_suggest_1389_, uint8_t v_warn_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v___y_1397_; lean_object* v_thm_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; uint8_t v___x_1452_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___x_1649_; 
v___x_1452_ = 0;
lean_inc(v_declName_1386_);
v___x_1649_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1386_, v___x_1452_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; uint8_t v_kind_1651_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v___x_1649_);
v_kind_1651_ = lean_ctor_get_uint8(v_a_1650_, sizeof(void*)*3);
lean_dec(v_a_1650_);
switch(v_kind_1651_)
{
case 1:
{
v___y_1580_ = v_a_1391_;
v___y_1581_ = v_a_1392_;
v___y_1582_ = v_a_1393_;
v___y_1583_ = v_a_1394_;
goto v___jp_1579_;
}
case 2:
{
v___y_1580_ = v_a_1391_;
v___y_1581_ = v_a_1392_;
v___y_1582_ = v_a_1393_;
v___y_1583_ = v_a_1394_;
goto v___jp_1579_;
}
case 6:
{
v___y_1580_ = v_a_1391_;
v___y_1581_ = v_a_1392_;
v___y_1582_ = v_a_1393_;
v___y_1583_ = v_a_1394_;
goto v___jp_1579_;
}
case 0:
{
lean_object* v___x_1652_; 
lean_dec(v_id_1385_);
lean_inc(v_declName_1386_);
v___x_1652_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1386_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; uint8_t v___x_1654_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = lean_unbox(v_a_1653_);
lean_dec(v_a_1653_);
if (v___x_1654_ == 0)
{
v___y_1510_ = v_a_1391_;
v___y_1511_ = v_a_1392_;
v___y_1512_ = v_a_1393_;
v___y_1513_ = v_a_1394_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_kind_1387_);
lean_dec_ref(v_params_1384_);
v___x_1655_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1656_ = l_Lean_MessageData_ofConstName(v_declName_1386_, v___x_1452_);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1659_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
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
lean_dec(v_kind_1387_);
lean_dec(v_declName_1386_);
lean_dec_ref(v_params_1384_);
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
lean_dec(v_kind_1387_);
lean_dec(v_id_1385_);
lean_dec_ref(v_params_1384_);
v___x_1677_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1678_ = l_Lean_MessageData_ofConstName(v_declName_1386_, v___x_1452_);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1681_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
return v___x_1682_;
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec(v_kind_1387_);
lean_dec(v_declName_1386_);
lean_dec(v_id_1385_);
lean_dec_ref(v_params_1384_);
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
v___jp_1396_:
{
lean_object* v_config_1398_; lean_object* v_extensions_1399_; lean_object* v_extra_1400_; lean_object* v_extraInj_1401_; lean_object* v_extraFacts_1402_; lean_object* v_symPrios_1403_; lean_object* v_norm_1404_; lean_object* v_normProcs_1405_; lean_object* v_anchorRefs_x3f_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1415_; 
v_config_1398_ = lean_ctor_get(v_params_1384_, 0);
v_extensions_1399_ = lean_ctor_get(v_params_1384_, 1);
v_extra_1400_ = lean_ctor_get(v_params_1384_, 2);
v_extraInj_1401_ = lean_ctor_get(v_params_1384_, 3);
v_extraFacts_1402_ = lean_ctor_get(v_params_1384_, 4);
v_symPrios_1403_ = lean_ctor_get(v_params_1384_, 5);
v_norm_1404_ = lean_ctor_get(v_params_1384_, 6);
v_normProcs_1405_ = lean_ctor_get(v_params_1384_, 7);
v_anchorRefs_x3f_1406_ = lean_ctor_get(v_params_1384_, 8);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_params_1384_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1408_ = v_params_1384_;
v_isShared_1409_ = v_isSharedCheck_1415_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_anchorRefs_x3f_1406_);
lean_inc(v_normProcs_1405_);
lean_inc(v_norm_1404_);
lean_inc(v_symPrios_1403_);
lean_inc(v_extraFacts_1402_);
lean_inc(v_extraInj_1401_);
lean_inc(v_extra_1400_);
lean_inc(v_extensions_1399_);
lean_inc(v_config_1398_);
lean_dec(v_params_1384_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1415_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1410_ = l_Lean_PersistentArray_push___redArg(v_extra_1400_, v___y_1397_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 2, v___x_1410_);
v___x_1412_ = v___x_1408_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_config_1398_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_extensions_1399_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1414_, 3, v_extraInj_1401_);
lean_ctor_set(v_reuseFailAlloc_1414_, 4, v_extraFacts_1402_);
lean_ctor_set(v_reuseFailAlloc_1414_, 5, v_symPrios_1403_);
lean_ctor_set(v_reuseFailAlloc_1414_, 6, v_norm_1404_);
lean_ctor_set(v_reuseFailAlloc_1414_, 7, v_normProcs_1405_);
lean_ctor_set(v_reuseFailAlloc_1414_, 8, v_anchorRefs_x3f_1406_);
v___x_1412_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
return v___x_1413_;
}
}
}
v___jp_1416_:
{
if (v_warn_1390_ == 0)
{
lean_dec(v_declName_1386_);
v___y_1397_ = v_thm_1417_;
goto v___jp_1396_;
}
else
{
lean_object* v_extensions_1422_; lean_object* v_patterns_1423_; lean_object* v_origin_1424_; lean_object* v_cnstrs_1425_; uint8_t v___x_1426_; 
v_extensions_1422_ = lean_ctor_get(v_params_1384_, 1);
v_patterns_1423_ = lean_ctor_get(v_thm_1417_, 3);
v_origin_1424_ = lean_ctor_get(v_thm_1417_, 5);
v_cnstrs_1425_ = lean_ctor_get(v_thm_1417_, 7);
v___x_1426_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1422_, v_origin_1424_, v_patterns_1423_, v_cnstrs_1425_);
if (v___x_1426_ == 0)
{
lean_dec(v_declName_1386_);
v___y_1397_ = v_thm_1417_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1427_; 
v___x_1427_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1422_, v_declName_1386_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_dec_ref(v___x_1427_);
v___y_1397_ = v_thm_1417_;
goto v___jp_1396_;
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec_ref(v_thm_1417_);
lean_dec_ref(v_params_1384_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
}
v___jp_1436_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1448_ = l_Lean_PersistentArray_push___redArg(v___y_1442_, v___y_1440_);
v___x_1449_ = l_Lean_PersistentArray_push___redArg(v___x_1448_, v___y_1437_);
v___x_1450_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1450_, 0, v___y_1447_);
lean_ctor_set(v___x_1450_, 1, v___y_1439_);
lean_ctor_set(v___x_1450_, 2, v___x_1449_);
lean_ctor_set(v___x_1450_, 3, v___y_1446_);
lean_ctor_set(v___x_1450_, 4, v___y_1438_);
lean_ctor_set(v___x_1450_, 5, v___y_1441_);
lean_ctor_set(v___x_1450_, 6, v___y_1445_);
lean_ctor_set(v___x_1450_, 7, v___y_1444_);
lean_ctor_set(v___x_1450_, 8, v___y_1443_);
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
v___jp_1453_:
{
lean_object* v___x_1458_; 
v___x_1458_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1388_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v___x_1459_; 
lean_dec_ref(v___x_1458_);
lean_inc(v_declName_1386_);
v___x_1459_ = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(v_declName_1386_, v___x_1452_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1492_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1492_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1492_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
if (lean_obj_tag(v_a_1460_) == 1)
{
lean_object* v_val_1464_; lean_object* v_config_1465_; lean_object* v_extensions_1466_; lean_object* v_extra_1467_; lean_object* v_extraInj_1468_; lean_object* v_extraFacts_1469_; lean_object* v_symPrios_1470_; lean_object* v_norm_1471_; lean_object* v_normProcs_1472_; lean_object* v_anchorRefs_x3f_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_declName_1386_);
v_val_1464_ = lean_ctor_get(v_a_1460_, 0);
lean_inc(v_val_1464_);
lean_dec_ref(v_a_1460_);
v_config_1465_ = lean_ctor_get(v_params_1384_, 0);
v_extensions_1466_ = lean_ctor_get(v_params_1384_, 1);
v_extra_1467_ = lean_ctor_get(v_params_1384_, 2);
v_extraInj_1468_ = lean_ctor_get(v_params_1384_, 3);
v_extraFacts_1469_ = lean_ctor_get(v_params_1384_, 4);
v_symPrios_1470_ = lean_ctor_get(v_params_1384_, 5);
v_norm_1471_ = lean_ctor_get(v_params_1384_, 6);
v_normProcs_1472_ = lean_ctor_get(v_params_1384_, 7);
v_anchorRefs_x3f_1473_ = lean_ctor_get(v_params_1384_, 8);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_params_1384_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1475_ = v_params_1384_;
v_isShared_1476_ = v_isSharedCheck_1485_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_anchorRefs_x3f_1473_);
lean_inc(v_normProcs_1472_);
lean_inc(v_norm_1471_);
lean_inc(v_symPrios_1470_);
lean_inc(v_extraFacts_1469_);
lean_inc(v_extraInj_1468_);
lean_inc(v_extra_1467_);
lean_inc(v_extensions_1466_);
lean_inc(v_config_1465_);
lean_dec(v_params_1384_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1485_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1477_ = l_Array_toPArray_x27___redArg(v_val_1464_);
lean_dec(v_val_1464_);
v___x_1478_ = l_Lean_PersistentArray_append___redArg(v_extra_1467_, v___x_1477_);
lean_dec_ref(v___x_1477_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 2, v___x_1478_);
v___x_1480_ = v___x_1475_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_config_1465_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_extensions_1466_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_extraInj_1468_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_extraFacts_1469_);
lean_ctor_set(v_reuseFailAlloc_1484_, 5, v_symPrios_1470_);
lean_ctor_set(v_reuseFailAlloc_1484_, 6, v_norm_1471_);
lean_ctor_set(v_reuseFailAlloc_1484_, 7, v_normProcs_1472_);
lean_ctor_set(v_reuseFailAlloc_1484_, 8, v_anchorRefs_x3f_1473_);
v___x_1480_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1482_; 
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1480_);
v___x_1482_ = v___x_1462_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_del_object(v___x_1462_);
lean_dec(v_a_1460_);
lean_dec_ref(v_params_1384_);
v___x_1486_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__1, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
v___x_1487_ = l_Lean_MessageData_ofConstName(v_declName_1386_, v___x_1452_);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1490_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1491_;
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec(v_declName_1386_);
lean_dec_ref(v_params_1384_);
v_a_1493_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1459_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1459_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_declName_1386_);
lean_dec_ref(v_params_1384_);
v_a_1501_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1458_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1458_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
v___jp_1509_:
{
uint8_t v___x_1514_; 
v___x_1514_ = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(v_kind_1387_);
if (v___x_1514_ == 0)
{
uint8_t v___x_1515_; 
v___x_1515_ = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(v_kind_1387_);
lean_dec(v_kind_1387_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v_params_1384_);
v___x_1516_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1517_ = l_Lean_MessageData_ofConstName(v_declName_1386_, v___x_1452_);
v___x_1518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1516_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__5, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
v___x_1520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1518_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1520_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
else
{
v___y_1454_ = v___y_1510_;
v___y_1455_ = v___y_1511_;
v___y_1456_ = v___y_1512_;
v___y_1457_ = v___y_1513_;
goto v___jp_1453_;
}
}
else
{
lean_dec(v_kind_1387_);
v___y_1454_ = v___y_1510_;
v___y_1455_ = v___y_1511_;
v___y_1456_ = v___y_1512_;
v___y_1457_ = v___y_1513_;
goto v___jp_1453_;
}
}
v___jp_1530_:
{
lean_object* v_symPrios_1535_; lean_object* v___x_1536_; 
v_symPrios_1535_ = lean_ctor_get(v_params_1384_, 5);
lean_inc_ref(v_symPrios_1535_);
lean_inc(v_declName_1386_);
v___x_1536_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1386_, v_kind_1387_, v_symPrios_1535_, v___x_1452_, v_minIndexable_1388_, v___y_1531_, v___y_1533_, v___y_1532_, v___y_1534_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref(v___x_1536_);
v_thm_1417_ = v_a_1537_;
v___y_1418_ = v___y_1531_;
v___y_1419_ = v___y_1533_;
v___y_1420_ = v___y_1532_;
v___y_1421_ = v___y_1534_;
goto v___jp_1416_;
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec(v_declName_1386_);
lean_dec_ref(v_params_1384_);
v_a_1538_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1536_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1536_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
v___jp_1546_:
{
if (v_suggest_1389_ == 0)
{
lean_dec(v_id_1385_);
v___y_1531_ = v___y_1547_;
v___y_1532_ = v___y_1549_;
v___y_1533_ = v___y_1548_;
v___y_1534_ = v___y_1550_;
goto v___jp_1530_;
}
else
{
lean_object* v_options_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v_options_1551_ = lean_ctor_get(v___y_1549_, 2);
v___x_1552_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1553_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v_symPrios_1554_; lean_object* v___x_1555_; 
lean_dec(v_kind_1387_);
v_symPrios_1554_ = lean_ctor_get(v_params_1384_, 5);
lean_inc_ref(v_symPrios_1554_);
lean_inc(v_declName_1386_);
v___x_1555_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1385_, v_declName_1386_, v_symPrios_1554_, v_minIndexable_1388_, v_suggest_1389_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1555_);
v_thm_1417_ = v_a_1556_;
v___y_1418_ = v___y_1547_;
v___y_1419_ = v___y_1548_;
v___y_1420_ = v___y_1549_;
v___y_1421_ = v___y_1550_;
goto v___jp_1416_;
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_declName_1386_);
lean_dec_ref(v_params_1384_);
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
lean_dec(v_id_1385_);
v___y_1531_ = v___y_1547_;
v___y_1532_ = v___y_1549_;
v___y_1533_ = v___y_1548_;
v___y_1534_ = v___y_1550_;
goto v___jp_1530_;
}
}
}
v___jp_1565_:
{
lean_object* v___x_1570_; 
v___x_1570_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1388_, v___y_1568_, v___y_1567_, v___y_1569_, v___y_1566_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_dec_ref(v___x_1570_);
v___y_1547_ = v___y_1568_;
v___y_1548_ = v___y_1567_;
v___y_1549_ = v___y_1569_;
v___y_1550_ = v___y_1566_;
goto v___jp_1546_;
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_kind_1387_);
lean_dec(v_declName_1386_);
lean_dec(v_id_1385_);
lean_dec_ref(v_params_1384_);
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
if (lean_obj_tag(v_kind_1387_) == 2)
{
uint8_t v_gen_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_id_1385_);
v_gen_1584_ = lean_ctor_get_uint8(v_kind_1387_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_kind_1387_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1586_ = v_kind_1387_;
v_isShared_1587_ = v_isSharedCheck_1648_;
goto v_resetjp_1585_;
}
else
{
lean_dec(v_kind_1387_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1648_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; 
v___x_1588_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1388_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_config_1589_; lean_object* v_extensions_1590_; lean_object* v_extra_1591_; lean_object* v_extraInj_1592_; lean_object* v_extraFacts_1593_; lean_object* v_symPrios_1594_; lean_object* v_norm_1595_; lean_object* v_normProcs_1596_; lean_object* v_anchorRefs_x3f_1597_; lean_object* v___x_1599_; 
lean_dec_ref(v___x_1588_);
v_config_1589_ = lean_ctor_get(v_params_1384_, 0);
lean_inc_ref(v_config_1589_);
v_extensions_1590_ = lean_ctor_get(v_params_1384_, 1);
lean_inc_ref(v_extensions_1590_);
v_extra_1591_ = lean_ctor_get(v_params_1384_, 2);
lean_inc_ref(v_extra_1591_);
v_extraInj_1592_ = lean_ctor_get(v_params_1384_, 3);
lean_inc_ref(v_extraInj_1592_);
v_extraFacts_1593_ = lean_ctor_get(v_params_1384_, 4);
lean_inc_ref(v_extraFacts_1593_);
v_symPrios_1594_ = lean_ctor_get(v_params_1384_, 5);
lean_inc_ref(v_symPrios_1594_);
v_norm_1595_ = lean_ctor_get(v_params_1384_, 6);
lean_inc_ref(v_norm_1595_);
v_normProcs_1596_ = lean_ctor_get(v_params_1384_, 7);
lean_inc_ref(v_normProcs_1596_);
v_anchorRefs_x3f_1597_ = lean_ctor_get(v_params_1384_, 8);
lean_inc(v_anchorRefs_x3f_1597_);
lean_dec_ref(v_params_1384_);
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
lean_inc(v_declName_1386_);
v___x_1600_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1386_, v___x_1599_, v_symPrios_1594_, v___x_1452_, v___x_1452_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1602_, 0, v_gen_1584_);
lean_inc_ref(v_symPrios_1594_);
lean_inc(v_declName_1386_);
v___x_1603_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1386_, v___x_1602_, v_symPrios_1594_, v___x_1452_, v___x_1452_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1603_) == 0)
{
if (v_warn_1390_ == 0)
{
lean_object* v_a_1604_; 
lean_dec(v_declName_1386_);
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1603_);
v___y_1437_ = v_a_1604_;
v___y_1438_ = v_extraFacts_1593_;
v___y_1439_ = v_extensions_1590_;
v___y_1440_ = v_a_1601_;
v___y_1441_ = v_symPrios_1594_;
v___y_1442_ = v_extra_1591_;
v___y_1443_ = v_anchorRefs_x3f_1597_;
v___y_1444_ = v_normProcs_1596_;
v___y_1445_ = v_norm_1595_;
v___y_1446_ = v_extraInj_1592_;
v___y_1447_ = v_config_1589_;
goto v___jp_1436_;
}
else
{
lean_object* v_a_1605_; lean_object* v_patterns_1606_; lean_object* v_origin_1607_; lean_object* v_cnstrs_1608_; uint8_t v___x_1609_; 
v_a_1605_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1603_);
v_patterns_1606_ = lean_ctor_get(v_a_1601_, 3);
v_origin_1607_ = lean_ctor_get(v_a_1601_, 5);
v_cnstrs_1608_ = lean_ctor_get(v_a_1601_, 7);
v___x_1609_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1590_, v_origin_1607_, v_patterns_1606_, v_cnstrs_1608_);
if (v___x_1609_ == 0)
{
lean_dec(v_declName_1386_);
v___y_1437_ = v_a_1605_;
v___y_1438_ = v_extraFacts_1593_;
v___y_1439_ = v_extensions_1590_;
v___y_1440_ = v_a_1601_;
v___y_1441_ = v_symPrios_1594_;
v___y_1442_ = v_extra_1591_;
v___y_1443_ = v_anchorRefs_x3f_1597_;
v___y_1444_ = v_normProcs_1596_;
v___y_1445_ = v_norm_1595_;
v___y_1446_ = v_extraInj_1592_;
v___y_1447_ = v_config_1589_;
goto v___jp_1436_;
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
lean_dec(v_declName_1386_);
v___y_1437_ = v_a_1605_;
v___y_1438_ = v_extraFacts_1593_;
v___y_1439_ = v_extensions_1590_;
v___y_1440_ = v_a_1601_;
v___y_1441_ = v_symPrios_1594_;
v___y_1442_ = v_extra_1591_;
v___y_1443_ = v_anchorRefs_x3f_1597_;
v___y_1444_ = v_normProcs_1596_;
v___y_1445_ = v_norm_1595_;
v___y_1446_ = v_extraInj_1592_;
v___y_1447_ = v_config_1589_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1590_, v_declName_1386_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_dec_ref(v___x_1614_);
v___y_1437_ = v_a_1605_;
v___y_1438_ = v_extraFacts_1593_;
v___y_1439_ = v_extensions_1590_;
v___y_1440_ = v_a_1601_;
v___y_1441_ = v_symPrios_1594_;
v___y_1442_ = v_extra_1591_;
v___y_1443_ = v_anchorRefs_x3f_1597_;
v___y_1444_ = v_normProcs_1596_;
v___y_1445_ = v_norm_1595_;
v___y_1446_ = v_extraInj_1592_;
v___y_1447_ = v_config_1589_;
goto v___jp_1436_;
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
lean_dec(v_declName_1386_);
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
lean_dec(v_declName_1386_);
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
lean_dec(v_declName_1386_);
lean_dec_ref(v_params_1384_);
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
switch(lean_obj_tag(v_kind_1387_))
{
case 0:
{
v___y_1566_ = v___y_1583_;
v___y_1567_ = v___y_1581_;
v___y_1568_ = v___y_1580_;
v___y_1569_ = v___y_1582_;
goto v___jp_1565_;
}
case 1:
{
v___y_1566_ = v___y_1583_;
v___y_1567_ = v___y_1581_;
v___y_1568_ = v___y_1580_;
v___y_1569_ = v___y_1582_;
goto v___jp_1565_;
}
default: 
{
v___y_1547_ = v___y_1580_;
v___y_1548_ = v___y_1581_;
v___y_1549_ = v___y_1582_;
v___y_1550_ = v___y_1583_;
goto v___jp_1546_;
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
lean_dec_ref(v_anchorRefs_x3f_1824_);
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
v_revert_1869_ = lean_ctor_get_uint8(v_config_1868_, sizeof(void*)*12 + 29);
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
v___x_1899_ = lean_st_ref_set(v___y_1880_, v___x_1898_);
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
lean_object* v_fileName_1939_; lean_object* v_fileMap_1940_; lean_object* v_options_1941_; lean_object* v_currRecDepth_1942_; lean_object* v_maxRecDepth_1943_; lean_object* v_ref_1944_; lean_object* v_currNamespace_1945_; lean_object* v_openDecls_1946_; lean_object* v_initHeartbeats_1947_; lean_object* v_maxHeartbeats_1948_; lean_object* v_quotContext_1949_; lean_object* v_currMacroScope_1950_; uint8_t v_diag_1951_; lean_object* v_cancelTk_x3f_1952_; uint8_t v_suppressElabErrors_1953_; lean_object* v_inheritedTraceOptions_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_2022_; 
v_fileName_1939_ = lean_ctor_get(v___y_1936_, 0);
v_fileMap_1940_ = lean_ctor_get(v___y_1936_, 1);
v_options_1941_ = lean_ctor_get(v___y_1936_, 2);
v_currRecDepth_1942_ = lean_ctor_get(v___y_1936_, 3);
v_maxRecDepth_1943_ = lean_ctor_get(v___y_1936_, 4);
v_ref_1944_ = lean_ctor_get(v___y_1936_, 5);
v_currNamespace_1945_ = lean_ctor_get(v___y_1936_, 6);
v_openDecls_1946_ = lean_ctor_get(v___y_1936_, 7);
v_initHeartbeats_1947_ = lean_ctor_get(v___y_1936_, 8);
v_maxHeartbeats_1948_ = lean_ctor_get(v___y_1936_, 9);
v_quotContext_1949_ = lean_ctor_get(v___y_1936_, 10);
v_currMacroScope_1950_ = lean_ctor_get(v___y_1936_, 11);
v_diag_1951_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*14);
v_cancelTk_x3f_1952_ = lean_ctor_get(v___y_1936_, 12);
v_suppressElabErrors_1953_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1954_ = lean_ctor_get(v___y_1936_, 13);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___y_1936_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_1956_ = v___y_1936_;
v_isShared_1957_ = v_isSharedCheck_2022_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_inheritedTraceOptions_1954_);
lean_inc(v_cancelTk_x3f_1952_);
lean_inc(v_currMacroScope_1950_);
lean_inc(v_quotContext_1949_);
lean_inc(v_maxHeartbeats_1948_);
lean_inc(v_initHeartbeats_1947_);
lean_inc(v_openDecls_1946_);
lean_inc(v_currNamespace_1945_);
lean_inc(v_ref_1944_);
lean_inc(v_maxRecDepth_1943_);
lean_inc(v_currRecDepth_1942_);
lean_inc(v_options_1941_);
lean_inc(v_fileMap_1940_);
lean_inc(v_fileName_1939_);
lean_dec(v___y_1936_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_2022_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v_ref_1958_; lean_object* v___x_1960_; 
v_ref_1958_ = l_Lean_replaceRef(v_p_1928_, v_ref_1944_);
lean_dec(v_ref_1944_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 5, v_ref_1958_);
v___x_1960_ = v___x_1956_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_fileName_1939_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_fileMap_1940_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v_options_1941_);
lean_ctor_set(v_reuseFailAlloc_2021_, 3, v_currRecDepth_1942_);
lean_ctor_set(v_reuseFailAlloc_2021_, 4, v_maxRecDepth_1943_);
lean_ctor_set(v_reuseFailAlloc_2021_, 5, v_ref_1958_);
lean_ctor_set(v_reuseFailAlloc_2021_, 6, v_currNamespace_1945_);
lean_ctor_set(v_reuseFailAlloc_2021_, 7, v_openDecls_1946_);
lean_ctor_set(v_reuseFailAlloc_2021_, 8, v_initHeartbeats_1947_);
lean_ctor_set(v_reuseFailAlloc_2021_, 9, v_maxHeartbeats_1948_);
lean_ctor_set(v_reuseFailAlloc_2021_, 10, v_quotContext_1949_);
lean_ctor_set(v_reuseFailAlloc_2021_, 11, v_currMacroScope_1950_);
lean_ctor_set(v_reuseFailAlloc_2021_, 12, v_cancelTk_x3f_1952_);
lean_ctor_set(v_reuseFailAlloc_2021_, 13, v_inheritedTraceOptions_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_2021_, sizeof(void*)*14, v_diag_1951_);
lean_ctor_set_uint8(v_reuseFailAlloc_2021_, sizeof(void*)*14 + 1, v_suppressElabErrors_1953_);
v___x_1960_ = v_reuseFailAlloc_2021_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_Elab_Term_elabTerm(v_term_1929_, v___x_1930_, v___x_1931_, v___x_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___x_1960_, v___y_1937_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; uint8_t v___x_1963_; lean_object* v___x_1964_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v___x_1961_);
v___x_1963_ = 1;
v___x_1964_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1963_, v___x_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___x_1960_, v___y_1937_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v___x_1965_; lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v___x_1964_);
v___x_1965_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_1962_, v___y_1935_);
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_2004_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2004_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
uint8_t v___x_1970_; 
v___x_1970_ = l_Lean_Expr_hasSyntheticSorry(v_a_1966_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1971_ = l_Lean_Expr_eta(v_a_1966_);
v___x_1972_ = l_Lean_Expr_hasMVar(v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
lean_dec_ref(v___x_1960_);
v___x_1973_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0));
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v___x_1971_);
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1975_);
v___x_1977_ = v___x_1968_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
else
{
lean_object* v___x_1979_; 
lean_del_object(v___x_1968_);
v___x_1979_ = l_Lean_Meta_abstractMVars(v___x_1971_, v___x_1931_, v___y_1934_, v___y_1935_, v___x_1960_, v___y_1937_);
lean_dec_ref(v___x_1960_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1991_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1991_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1991_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v_paramNames_1984_; lean_object* v_expr_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v_paramNames_1984_ = lean_ctor_get(v_a_1980_, 0);
lean_inc_ref(v_paramNames_1984_);
v_expr_1985_ = lean_ctor_get(v_a_1980_, 2);
lean_inc_ref(v_expr_1985_);
lean_dec(v_a_1980_);
v___x_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1986_, 0, v_paramNames_1984_);
lean_ctor_set(v___x_1986_, 1, v_expr_1985_);
v___x_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1987_);
v___x_1989_ = v___x_1982_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
v_a_1992_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1979_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1979_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
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
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
lean_dec(v_a_1966_);
lean_dec_ref(v___x_1960_);
v___x_2000_ = lean_box(0);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_2000_);
v___x_2002_ = v___x_1968_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_a_1962_);
lean_dec_ref(v___x_1960_);
v_a_2005_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1964_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1964_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v___x_1960_);
v_a_2013_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1961_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1961_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v_p_2023_, lean_object* v_term_2024_, lean_object* v___x_2025_, lean_object* v___x_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
uint8_t v___x_13864__boxed_2034_; lean_object* v_res_2035_; 
v___x_13864__boxed_2034_ = lean_unbox(v___x_2026_);
v_res_2035_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v_p_2023_, v_term_2024_, v___x_2025_, v___x_13864__boxed_2034_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v_p_2023_);
return v_res_2035_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2));
v___x_2041_ = l_Lean_stringToMessageData(v___x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_params_2042_, lean_object* v_p_2043_, lean_object* v_fst_2044_, lean_object* v_snd_2045_, uint8_t v___x_2046_, uint8_t v_minIndexable_2047_, lean_object* v_kind_2048_, lean_object* v_idx_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_symPrios_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; 
v_symPrios_2055_ = lean_ctor_get(v_params_2042_, 5);
lean_inc_ref(v_symPrios_2055_);
lean_dec_ref(v_params_2042_);
v___x_2056_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1));
v___x_2057_ = lean_name_append_index_after(v___x_2056_, v_idx_2049_);
v___x_2058_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v_p_2043_);
v___x_2059_ = 0;
v___x_2060_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2058_, v_fst_2044_, v_snd_2045_, v_kind_2048_, v_symPrios_2055_, v___x_2046_, v___x_2059_, v_minIndexable_2047_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2071_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2071_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2071_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
if (lean_obj_tag(v_a_2061_) == 1)
{
lean_object* v_val_2065_; lean_object* v___x_2067_; 
v_val_2065_ = lean_ctor_get(v_a_2061_, 0);
lean_inc(v_val_2065_);
lean_dec_ref(v_a_2061_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v_val_2065_);
v___x_2067_ = v___x_2063_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_val_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_del_object(v___x_2063_);
lean_dec(v_a_2061_);
v___x_2069_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3);
v___x_2070_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2069_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
return v___x_2070_;
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
v_a_2072_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2060_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2060_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_params_2080_, lean_object* v_p_2081_, lean_object* v_fst_2082_, lean_object* v_snd_2083_, lean_object* v___x_2084_, lean_object* v_minIndexable_2085_, lean_object* v_kind_2086_, lean_object* v_idx_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
uint8_t v___x_14038__boxed_2093_; uint8_t v_minIndexable_boxed_2094_; lean_object* v_res_2095_; 
v___x_14038__boxed_2093_ = lean_unbox(v___x_2084_);
v_minIndexable_boxed_2094_ = lean_unbox(v_minIndexable_2085_);
v_res_2095_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_params_2080_, v_p_2081_, v_fst_2082_, v_snd_2083_, v___x_14038__boxed_2093_, v_minIndexable_boxed_2094_, v_kind_2086_, v_idx_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
return v_res_2095_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_box(1);
v___x_2097_ = l_Lean_MessageData_ofFormat(v___x_2096_);
return v___x_2097_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2));
v___x_2102_ = l_Lean_MessageData_ofFormat(v___x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(lean_object* v_x_2103_, lean_object* v_x_2104_){
_start:
{
if (lean_obj_tag(v_x_2104_) == 0)
{
return v_x_2103_;
}
else
{
lean_object* v_head_2105_; lean_object* v_tail_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2128_; 
v_head_2105_ = lean_ctor_get(v_x_2104_, 0);
v_tail_2106_ = lean_ctor_get(v_x_2104_, 1);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_x_2104_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2108_ = v_x_2104_;
v_isShared_2109_ = v_isSharedCheck_2128_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_tail_2106_);
lean_inc(v_head_2105_);
lean_dec(v_x_2104_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2128_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v_before_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2126_; 
v_before_2110_ = lean_ctor_get(v_head_2105_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_head_2105_);
if (v_isSharedCheck_2126_ == 0)
{
lean_object* v_unused_2127_; 
v_unused_2127_ = lean_ctor_get(v_head_2105_, 1);
lean_dec(v_unused_2127_);
v___x_2112_ = v_head_2105_;
v_isShared_2113_ = v_isSharedCheck_2126_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_before_2110_);
lean_dec(v_head_2105_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2126_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 7);
lean_ctor_set(v___x_2112_, 1, v___x_2114_);
lean_ctor_set(v___x_2112_, 0, v_x_2103_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_x_2103_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2117_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3);
if (v_isShared_2109_ == 0)
{
lean_ctor_set_tag(v___x_2108_, 7);
lean_ctor_set(v___x_2108_, 1, v___x_2117_);
lean_ctor_set(v___x_2108_, 0, v___x_2116_);
v___x_2119_ = v___x_2108_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2120_ = l_Lean_MessageData_ofSyntax(v_before_2110_);
v___x_2121_ = l_Lean_indentD(v___x_2120_);
v___x_2122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2119_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v_x_2103_ = v___x_2122_;
v_x_2104_ = v_tail_2106_;
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
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1));
v___x_2133_ = l_Lean_MessageData_ofFormat(v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(lean_object* v_msgData_2134_, lean_object* v_macroStack_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_options_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v_options_2138_ = lean_ctor_get(v___y_2136_, 2);
v___x_2139_ = l_Lean_Elab_pp_macroStack;
v___x_2140_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2138_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
lean_dec(v_macroStack_2135_);
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v_msgData_2134_);
return v___x_2141_;
}
else
{
if (lean_obj_tag(v_macroStack_2135_) == 0)
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v_msgData_2134_);
return v___x_2142_;
}
else
{
lean_object* v_head_2143_; lean_object* v_after_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2159_; 
v_head_2143_ = lean_ctor_get(v_macroStack_2135_, 0);
lean_inc(v_head_2143_);
v_after_2144_ = lean_ctor_get(v_head_2143_, 1);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_head_2143_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; 
v_unused_2160_ = lean_ctor_get(v_head_2143_, 0);
lean_dec(v_unused_2160_);
v___x_2146_ = v_head_2143_;
v_isShared_2147_ = v_isSharedCheck_2159_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_after_2144_);
lean_dec(v_head_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2159_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2147_ == 0)
{
lean_ctor_set_tag(v___x_2146_, 7);
lean_ctor_set(v___x_2146_, 1, v___x_2148_);
lean_ctor_set(v___x_2146_, 0, v_msgData_2134_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_msgData_2134_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v_msgData_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2151_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = l_Lean_MessageData_ofSyntax(v_after_2144_);
v___x_2154_ = l_Lean_indentD(v___x_2153_);
v_msgData_2155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2155_, 0, v___x_2152_);
lean_ctor_set(v_msgData_2155_, 1, v___x_2154_);
v___x_2156_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(v_msgData_2155_, v_macroStack_2135_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2161_, lean_object* v_macroStack_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2161_, v_macroStack_2162_, v___y_2163_);
lean_dec_ref(v___y_2163_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(lean_object* v_msg_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v_ref_2174_; lean_object* v___x_2175_; lean_object* v_a_2176_; lean_object* v_macroStack_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2188_; 
v_ref_2174_ = lean_ctor_get(v___y_2171_, 5);
v___x_2175_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2166_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref(v___x_2175_);
v_macroStack_2177_ = lean_ctor_get(v___y_2167_, 1);
v___x_2178_ = l_Lean_Elab_getBetterRef(v_ref_2174_, v_macroStack_2177_);
lean_inc(v_macroStack_2177_);
v___x_2179_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_a_2176_, v_macroStack_2177_, v___y_2171_);
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2178_);
lean_ctor_set(v___x_2184_, 1, v_a_2180_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 1);
lean_ctor_set(v___x_2182_, 0, v___x_2184_);
v___x_2186_ = v___x_2182_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v_msg_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2197_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2200_ = l_Lean_stringToMessageData(v___x_2199_);
return v___x_2200_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2203_ = l_Lean_stringToMessageData(v___x_2202_);
return v___x_2203_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2206_ = l_Lean_stringToMessageData(v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7));
v___x_2211_ = l_Lean_stringToMessageData(v___x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2212_, lean_object* v_p_2213_, lean_object* v_mod_x3f_2214_, lean_object* v_term_2215_, uint8_t v_minIndexable_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2287_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v_kind_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v_fileName_2522_; lean_object* v_fileMap_2523_; lean_object* v_options_2524_; lean_object* v_currRecDepth_2525_; lean_object* v_maxRecDepth_2526_; lean_object* v_ref_2527_; lean_object* v_currNamespace_2528_; lean_object* v_openDecls_2529_; lean_object* v_initHeartbeats_2530_; lean_object* v_maxHeartbeats_2531_; lean_object* v_quotContext_2532_; lean_object* v_currMacroScope_2533_; uint8_t v_diag_2534_; lean_object* v_cancelTk_x3f_2535_; uint8_t v_suppressElabErrors_2536_; lean_object* v_inheritedTraceOptions_2537_; lean_object* v_ref_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v_fileName_2522_ = lean_ctor_get(v_a_2221_, 0);
v_fileMap_2523_ = lean_ctor_get(v_a_2221_, 1);
v_options_2524_ = lean_ctor_get(v_a_2221_, 2);
v_currRecDepth_2525_ = lean_ctor_get(v_a_2221_, 3);
v_maxRecDepth_2526_ = lean_ctor_get(v_a_2221_, 4);
v_ref_2527_ = lean_ctor_get(v_a_2221_, 5);
v_currNamespace_2528_ = lean_ctor_get(v_a_2221_, 6);
v_openDecls_2529_ = lean_ctor_get(v_a_2221_, 7);
v_initHeartbeats_2530_ = lean_ctor_get(v_a_2221_, 8);
v_maxHeartbeats_2531_ = lean_ctor_get(v_a_2221_, 9);
v_quotContext_2532_ = lean_ctor_get(v_a_2221_, 10);
v_currMacroScope_2533_ = lean_ctor_get(v_a_2221_, 11);
v_diag_2534_ = lean_ctor_get_uint8(v_a_2221_, sizeof(void*)*14);
v_cancelTk_x3f_2535_ = lean_ctor_get(v_a_2221_, 12);
v_suppressElabErrors_2536_ = lean_ctor_get_uint8(v_a_2221_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2537_ = lean_ctor_get(v_a_2221_, 13);
v_ref_2538_ = l_Lean_replaceRef(v_p_2213_, v_ref_2527_);
lean_inc_ref(v_inheritedTraceOptions_2537_);
lean_inc(v_cancelTk_x3f_2535_);
lean_inc(v_currMacroScope_2533_);
lean_inc(v_quotContext_2532_);
lean_inc(v_maxHeartbeats_2531_);
lean_inc(v_initHeartbeats_2530_);
lean_inc(v_openDecls_2529_);
lean_inc(v_currNamespace_2528_);
lean_inc(v_maxRecDepth_2526_);
lean_inc(v_currRecDepth_2525_);
lean_inc_ref(v_options_2524_);
lean_inc_ref(v_fileMap_2523_);
lean_inc_ref(v_fileName_2522_);
v___x_2539_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2539_, 0, v_fileName_2522_);
lean_ctor_set(v___x_2539_, 1, v_fileMap_2523_);
lean_ctor_set(v___x_2539_, 2, v_options_2524_);
lean_ctor_set(v___x_2539_, 3, v_currRecDepth_2525_);
lean_ctor_set(v___x_2539_, 4, v_maxRecDepth_2526_);
lean_ctor_set(v___x_2539_, 5, v_ref_2538_);
lean_ctor_set(v___x_2539_, 6, v_currNamespace_2528_);
lean_ctor_set(v___x_2539_, 7, v_openDecls_2529_);
lean_ctor_set(v___x_2539_, 8, v_initHeartbeats_2530_);
lean_ctor_set(v___x_2539_, 9, v_maxHeartbeats_2531_);
lean_ctor_set(v___x_2539_, 10, v_quotContext_2532_);
lean_ctor_set(v___x_2539_, 11, v_currMacroScope_2533_);
lean_ctor_set(v___x_2539_, 12, v_cancelTk_x3f_2535_);
lean_ctor_set(v___x_2539_, 13, v_inheritedTraceOptions_2537_);
lean_ctor_set_uint8(v___x_2539_, sizeof(void*)*14, v_diag_2534_);
lean_ctor_set_uint8(v___x_2539_, sizeof(void*)*14 + 1, v_suppressElabErrors_2536_);
v___x_2540_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2212_, v___x_2539_, v_a_2222_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_dec_ref(v___x_2540_);
if (lean_obj_tag(v_mod_x3f_2214_) == 1)
{
lean_object* v_val_2541_; lean_object* v___x_2542_; 
v_val_2541_ = lean_ctor_get(v_mod_x3f_2214_, 0);
lean_inc(v_val_2541_);
v___x_2542_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2541_, v___x_2539_, v_a_2222_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref(v___x_2542_);
switch(lean_obj_tag(v_a_2543_))
{
case 0:
{
lean_object* v_k_2561_; 
v_k_2561_ = lean_ctor_get(v_a_2543_, 0);
lean_inc(v_k_2561_);
lean_dec_ref(v_a_2543_);
if (lean_obj_tag(v_k_2561_) == 9)
{
lean_dec_ref(v_mod_x3f_2214_);
lean_dec(v_term_2215_);
lean_dec(v_p_2213_);
lean_dec_ref(v_params_2212_);
v___y_2545_ = v_a_2217_;
v___y_2546_ = v_a_2218_;
v___y_2547_ = v_a_2219_;
v___y_2548_ = v_a_2220_;
v___y_2549_ = v___x_2539_;
v___y_2550_ = v_a_2222_;
goto v___jp_2544_;
}
else
{
v_kind_2449_ = v_k_2561_;
v___y_2450_ = v_a_2217_;
v___y_2451_ = v_a_2218_;
v___y_2452_ = v_a_2219_;
v___y_2453_ = v_a_2220_;
v___y_2454_ = v___x_2539_;
v___y_2455_ = v_a_2222_;
goto v___jp_2448_;
}
}
case 1:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec_ref(v_a_2543_);
lean_dec_ref(v_mod_x3f_2214_);
lean_dec(v_term_2215_);
lean_dec(v_p_2213_);
lean_dec_ref(v_params_2212_);
v___x_2562_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2563_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2562_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v___x_2539_, v_a_2222_);
lean_dec_ref(v___x_2539_);
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
case 3:
{
v___y_2515_ = v_a_2217_;
v___y_2516_ = v_a_2218_;
v___y_2517_ = v_a_2219_;
v___y_2518_ = v_a_2220_;
v___y_2519_ = v___x_2539_;
v___y_2520_ = v_a_2222_;
goto v___jp_2514_;
}
case 5:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v_a_2543_);
lean_dec_ref(v_mod_x3f_2214_);
lean_dec(v_term_2215_);
lean_dec(v_p_2213_);
lean_dec_ref(v_params_2212_);
v___x_2572_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2573_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2572_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v___x_2539_, v_a_2222_);
lean_dec_ref(v___x_2539_);
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
case 8:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec_ref(v_a_2543_);
lean_dec_ref(v_mod_x3f_2214_);
lean_dec(v_term_2215_);
lean_dec(v_p_2213_);
lean_dec_ref(v_params_2212_);
v___x_2582_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2583_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2582_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v___x_2539_, v_a_2222_);
lean_dec_ref(v___x_2539_);
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
default: 
{
lean_dec(v_a_2543_);
lean_dec_ref(v_mod_x3f_2214_);
lean_dec(v_term_2215_);
lean_dec(v_p_2213_);
lean_dec_ref(v_params_2212_);
v___y_2545_ = v_a_2217_;
v___y_2546_ = v_a_2218_;
v___y_2547_ = v_a_2219_;
v___y_2548_ = v_a_2220_;
v___y_2549_ = v___x_2539_;
v___y_2550_ = v_a_2222_;
goto v___jp_2544_;
}
}
v___jp_2544_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
v___x_2551_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2552_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2551_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref(v___y_2549_);
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
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec_ref(v_mod_x3f_2214_);
lean_dec_ref(v___x_2539_);
lean_dec(v_term_2215_);
lean_dec(v_p_2213_);
lean_dec_ref(v_params_2212_);
v_a_2592_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2542_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2542_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
v___y_2515_ = v_a_2217_;
v___y_2516_ = v_a_2218_;
v___y_2517_ = v_a_2219_;
v___y_2518_ = v_a_2220_;
v___y_2519_ = v___x_2539_;
v___y_2520_ = v_a_2222_;
goto v___jp_2514_;
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec_ref(v___x_2539_);
lean_dec(v_term_2215_);
lean_dec(v_mod_x3f_2214_);
lean_dec(v_p_2213_);
lean_dec_ref(v_params_2212_);
v_a_2600_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2540_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2540_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
v___jp_2224_:
{
lean_object* v___x_2241_; 
lean_inc(v___y_2240_);
lean_inc(v___y_2238_);
lean_inc_ref(v___y_2237_);
v___x_2241_ = lean_apply_7(v___y_2229_, v___y_2236_, v___y_2233_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, lean_box(0));
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2251_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2251_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2251_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2246_ = l_Lean_PersistentArray_push___redArg(v___y_2226_, v_a_2242_);
v___x_2247_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2247_, 0, v___y_2235_);
lean_ctor_set(v___x_2247_, 1, v___y_2231_);
lean_ctor_set(v___x_2247_, 2, v___x_2246_);
lean_ctor_set(v___x_2247_, 3, v___y_2230_);
lean_ctor_set(v___x_2247_, 4, v___y_2228_);
lean_ctor_set(v___x_2247_, 5, v___y_2227_);
lean_ctor_set(v___x_2247_, 6, v___y_2234_);
lean_ctor_set(v___x_2247_, 7, v___y_2225_);
lean_ctor_set(v___x_2247_, 8, v___y_2232_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2247_);
v___x_2249_ = v___x_2244_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec_ref(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec_ref(v___y_2225_);
v_a_2252_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2241_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2241_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
v___jp_2260_:
{
lean_object* v___x_2277_; 
v___x_2277_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2216_, v___y_2266_, v___y_2274_, v___y_2271_, v___y_2264_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_dec_ref(v___x_2277_);
v___y_2225_ = v___y_2268_;
v___y_2226_ = v___y_2261_;
v___y_2227_ = v___y_2269_;
v___y_2228_ = v___y_2270_;
v___y_2229_ = v___y_2262_;
v___y_2230_ = v___y_2272_;
v___y_2231_ = v___y_2263_;
v___y_2232_ = v___y_2273_;
v___y_2233_ = v___y_2275_;
v___y_2234_ = v___y_2265_;
v___y_2235_ = v___y_2276_;
v___y_2236_ = v___y_2267_;
v___y_2237_ = v___y_2266_;
v___y_2238_ = v___y_2274_;
v___y_2239_ = v___y_2271_;
v___y_2240_ = v___y_2264_;
goto v___jp_2224_;
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v___y_2261_);
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
v___jp_2286_:
{
lean_object* v_config_2288_; lean_object* v_extensions_2289_; lean_object* v_extra_2290_; lean_object* v_extraInj_2291_; lean_object* v_extraFacts_2292_; lean_object* v_symPrios_2293_; lean_object* v_norm_2294_; lean_object* v_normProcs_2295_; lean_object* v_anchorRefs_x3f_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2305_; 
v_config_2288_ = lean_ctor_get(v_params_2212_, 0);
v_extensions_2289_ = lean_ctor_get(v_params_2212_, 1);
v_extra_2290_ = lean_ctor_get(v_params_2212_, 2);
v_extraInj_2291_ = lean_ctor_get(v_params_2212_, 3);
v_extraFacts_2292_ = lean_ctor_get(v_params_2212_, 4);
v_symPrios_2293_ = lean_ctor_get(v_params_2212_, 5);
v_norm_2294_ = lean_ctor_get(v_params_2212_, 6);
v_normProcs_2295_ = lean_ctor_get(v_params_2212_, 7);
v_anchorRefs_x3f_2296_ = lean_ctor_get(v_params_2212_, 8);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_params_2212_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2298_ = v_params_2212_;
v_isShared_2299_ = v_isSharedCheck_2305_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_anchorRefs_x3f_2296_);
lean_inc(v_normProcs_2295_);
lean_inc(v_norm_2294_);
lean_inc(v_symPrios_2293_);
lean_inc(v_extraFacts_2292_);
lean_inc(v_extraInj_2291_);
lean_inc(v_extra_2290_);
lean_inc(v_extensions_2289_);
lean_inc(v_config_2288_);
lean_dec(v_params_2212_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2305_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2292_, v___y_2287_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 4, v___x_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_config_2288_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v_extensions_2289_);
lean_ctor_set(v_reuseFailAlloc_2304_, 2, v_extra_2290_);
lean_ctor_set(v_reuseFailAlloc_2304_, 3, v_extraInj_2291_);
lean_ctor_set(v_reuseFailAlloc_2304_, 4, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2304_, 5, v_symPrios_2293_);
lean_ctor_set(v_reuseFailAlloc_2304_, 6, v_norm_2294_);
lean_ctor_set(v_reuseFailAlloc_2304_, 7, v_normProcs_2295_);
lean_ctor_set(v_reuseFailAlloc_2304_, 8, v_anchorRefs_x3f_2296_);
v___x_2302_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
}
}
v___jp_2306_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2316_ = lean_array_get_size(v___y_2307_);
lean_dec_ref(v___y_2307_);
v___x_2317_ = lean_unsigned_to_nat(0u);
v___x_2318_ = lean_nat_dec_eq(v___x_2316_, v___x_2317_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v___y_2309_);
lean_dec_ref(v_params_2212_);
v___x_2319_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2320_ = l_Lean_indentExpr(v___y_2308_);
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2321_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec_ref(v___y_2314_);
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
else
{
lean_dec_ref(v___y_2314_);
lean_dec_ref(v___y_2308_);
v___y_2287_ = v___y_2309_;
goto v___jp_2286_;
}
}
v___jp_2331_:
{
uint8_t v___x_2343_; 
v___x_2343_ = l_Lean_Expr_isForall(v___y_2333_);
if (v___x_2343_ == 0)
{
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
if (lean_obj_tag(v_mod_x3f_2214_) == 0)
{
v___y_2307_ = v___y_2332_;
v___y_2308_ = v___y_2333_;
v___y_2309_ = v___y_2334_;
v___y_2310_ = v___y_2337_;
v___y_2311_ = v___y_2338_;
v___y_2312_ = v___y_2339_;
v___y_2313_ = v___y_2340_;
v___y_2314_ = v___y_2341_;
v___y_2315_ = v___y_2342_;
goto v___jp_2306_;
}
else
{
lean_dec_ref(v_mod_x3f_2214_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec_ref(v___y_2334_);
lean_dec_ref(v___y_2332_);
lean_dec_ref(v_params_2212_);
v___x_2344_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2345_ = l_Lean_indentExpr(v___y_2333_);
v___x_2346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2346_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec_ref(v___y_2341_);
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
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
else
{
v___y_2307_ = v___y_2332_;
v___y_2308_ = v___y_2333_;
v___y_2309_ = v___y_2334_;
v___y_2310_ = v___y_2337_;
v___y_2311_ = v___y_2338_;
v___y_2312_ = v___y_2339_;
v___y_2313_ = v___y_2340_;
v___y_2314_ = v___y_2341_;
v___y_2315_ = v___y_2342_;
goto v___jp_2306_;
}
}
}
else
{
lean_object* v_extra_2356_; 
lean_dec_ref(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v_mod_x3f_2214_);
v_extra_2356_ = lean_ctor_get(v_params_2212_, 2);
lean_inc_ref(v_extra_2356_);
if (lean_obj_tag(v___y_2336_) == 2)
{
lean_object* v_config_2357_; lean_object* v_extensions_2358_; lean_object* v_extraInj_2359_; lean_object* v_extraFacts_2360_; lean_object* v_symPrios_2361_; lean_object* v_norm_2362_; lean_object* v_normProcs_2363_; lean_object* v_anchorRefs_x3f_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2419_; 
v_config_2357_ = lean_ctor_get(v_params_2212_, 0);
v_extensions_2358_ = lean_ctor_get(v_params_2212_, 1);
v_extraInj_2359_ = lean_ctor_get(v_params_2212_, 3);
v_extraFacts_2360_ = lean_ctor_get(v_params_2212_, 4);
v_symPrios_2361_ = lean_ctor_get(v_params_2212_, 5);
v_norm_2362_ = lean_ctor_get(v_params_2212_, 6);
v_normProcs_2363_ = lean_ctor_get(v_params_2212_, 7);
v_anchorRefs_x3f_2364_ = lean_ctor_get(v_params_2212_, 8);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_params_2212_);
if (v_isSharedCheck_2419_ == 0)
{
lean_object* v_unused_2420_; 
v_unused_2420_ = lean_ctor_get(v_params_2212_, 2);
lean_dec(v_unused_2420_);
v___x_2366_ = v_params_2212_;
v_isShared_2367_ = v_isSharedCheck_2419_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_anchorRefs_x3f_2364_);
lean_inc(v_normProcs_2363_);
lean_inc(v_norm_2362_);
lean_inc(v_symPrios_2361_);
lean_inc(v_extraFacts_2360_);
lean_inc(v_extraInj_2359_);
lean_inc(v_extensions_2358_);
lean_inc(v_config_2357_);
lean_dec(v_params_2212_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2419_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_size_2368_; uint8_t v_gen_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2418_; 
v_size_2368_ = lean_ctor_get(v_extra_2356_, 2);
v_gen_2369_ = lean_ctor_get_uint8(v___y_2336_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___y_2336_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2371_ = v___y_2336_;
v_isShared_2372_ = v_isSharedCheck_2418_;
goto v_resetjp_2370_;
}
else
{
lean_dec(v___y_2336_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2418_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; 
v___x_2373_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2216_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v___x_2375_; 
lean_dec_ref(v___x_2373_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set_tag(v___x_2371_, 0);
v___x_2375_ = v___x_2371_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2409_, 0, v_gen_2369_);
v___x_2375_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2376_; 
lean_inc_ref(v___y_2335_);
lean_inc(v___y_2342_);
lean_inc_ref(v___y_2341_);
lean_inc(v___y_2340_);
lean_inc_ref(v___y_2339_);
lean_inc(v_size_2368_);
v___x_2376_ = lean_apply_7(v___y_2335_, v___x_2375_, v_size_2368_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, lean_box(0));
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref(v___x_2376_);
v___x_2378_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2378_, 0, v_gen_2369_);
lean_inc(v___y_2342_);
lean_inc(v___y_2340_);
lean_inc_ref(v___y_2339_);
lean_inc(v_size_2368_);
v___x_2379_ = lean_apply_7(v___y_2335_, v___x_2378_, v_size_2368_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, lean_box(0));
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2392_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2392_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2392_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2384_ = l_Lean_PersistentArray_push___redArg(v_extra_2356_, v_a_2377_);
v___x_2385_ = l_Lean_PersistentArray_push___redArg(v___x_2384_, v_a_2380_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 2, v___x_2385_);
v___x_2387_ = v___x_2366_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_config_2357_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v_extensions_2358_);
lean_ctor_set(v_reuseFailAlloc_2391_, 2, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2391_, 3, v_extraInj_2359_);
lean_ctor_set(v_reuseFailAlloc_2391_, 4, v_extraFacts_2360_);
lean_ctor_set(v_reuseFailAlloc_2391_, 5, v_symPrios_2361_);
lean_ctor_set(v_reuseFailAlloc_2391_, 6, v_norm_2362_);
lean_ctor_set(v_reuseFailAlloc_2391_, 7, v_normProcs_2363_);
lean_ctor_set(v_reuseFailAlloc_2391_, 8, v_anchorRefs_x3f_2364_);
v___x_2387_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
lean_object* v___x_2389_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2387_);
v___x_2389_ = v___x_2382_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v_a_2377_);
lean_del_object(v___x_2366_);
lean_dec(v_anchorRefs_x3f_2364_);
lean_dec_ref(v_normProcs_2363_);
lean_dec_ref(v_norm_2362_);
lean_dec_ref(v_symPrios_2361_);
lean_dec_ref(v_extraFacts_2360_);
lean_dec_ref(v_extraInj_2359_);
lean_dec_ref(v_extensions_2358_);
lean_dec_ref(v_config_2357_);
lean_dec_ref(v_extra_2356_);
v_a_2393_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2379_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2379_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_del_object(v___x_2366_);
lean_dec(v_anchorRefs_x3f_2364_);
lean_dec_ref(v_normProcs_2363_);
lean_dec_ref(v_norm_2362_);
lean_dec_ref(v_symPrios_2361_);
lean_dec_ref(v_extraFacts_2360_);
lean_dec_ref(v_extraInj_2359_);
lean_dec_ref(v_extensions_2358_);
lean_dec_ref(v_config_2357_);
lean_dec_ref(v_extra_2356_);
lean_dec_ref(v___y_2341_);
lean_dec_ref(v___y_2335_);
v_a_2401_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2376_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2376_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_del_object(v___x_2371_);
lean_del_object(v___x_2366_);
lean_dec(v_anchorRefs_x3f_2364_);
lean_dec_ref(v_normProcs_2363_);
lean_dec_ref(v_norm_2362_);
lean_dec_ref(v_symPrios_2361_);
lean_dec_ref(v_extraFacts_2360_);
lean_dec_ref(v_extraInj_2359_);
lean_dec_ref(v_extensions_2358_);
lean_dec_ref(v_config_2357_);
lean_dec_ref(v_extra_2356_);
lean_dec_ref(v___y_2341_);
lean_dec_ref(v___y_2335_);
v_a_2410_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2373_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2373_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
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
lean_object* v_config_2421_; lean_object* v_extensions_2422_; lean_object* v_extraInj_2423_; lean_object* v_extraFacts_2424_; lean_object* v_symPrios_2425_; lean_object* v_norm_2426_; lean_object* v_normProcs_2427_; lean_object* v_anchorRefs_x3f_2428_; lean_object* v_size_2429_; 
v_config_2421_ = lean_ctor_get(v_params_2212_, 0);
lean_inc_ref(v_config_2421_);
v_extensions_2422_ = lean_ctor_get(v_params_2212_, 1);
lean_inc_ref(v_extensions_2422_);
v_extraInj_2423_ = lean_ctor_get(v_params_2212_, 3);
lean_inc_ref(v_extraInj_2423_);
v_extraFacts_2424_ = lean_ctor_get(v_params_2212_, 4);
lean_inc_ref(v_extraFacts_2424_);
v_symPrios_2425_ = lean_ctor_get(v_params_2212_, 5);
lean_inc_ref(v_symPrios_2425_);
v_norm_2426_ = lean_ctor_get(v_params_2212_, 6);
lean_inc_ref(v_norm_2426_);
v_normProcs_2427_ = lean_ctor_get(v_params_2212_, 7);
lean_inc_ref(v_normProcs_2427_);
v_anchorRefs_x3f_2428_ = lean_ctor_get(v_params_2212_, 8);
lean_inc(v_anchorRefs_x3f_2428_);
lean_dec_ref(v_params_2212_);
v_size_2429_ = lean_ctor_get(v_extra_2356_, 2);
lean_inc(v_size_2429_);
v___y_2261_ = v_extra_2356_;
v___y_2262_ = v___y_2335_;
v___y_2263_ = v_extensions_2422_;
v___y_2264_ = v___y_2342_;
v___y_2265_ = v_norm_2426_;
v___y_2266_ = v___y_2339_;
v___y_2267_ = v___y_2336_;
v___y_2268_ = v_normProcs_2427_;
v___y_2269_ = v_symPrios_2425_;
v___y_2270_ = v_extraFacts_2424_;
v___y_2271_ = v___y_2341_;
v___y_2272_ = v_extraInj_2423_;
v___y_2273_ = v_anchorRefs_x3f_2428_;
v___y_2274_ = v___y_2340_;
v___y_2275_ = v_size_2429_;
v___y_2276_ = v_config_2421_;
goto v___jp_2260_;
}
case 1:
{
lean_object* v_config_2430_; lean_object* v_extensions_2431_; lean_object* v_extraInj_2432_; lean_object* v_extraFacts_2433_; lean_object* v_symPrios_2434_; lean_object* v_norm_2435_; lean_object* v_normProcs_2436_; lean_object* v_anchorRefs_x3f_2437_; lean_object* v_size_2438_; 
v_config_2430_ = lean_ctor_get(v_params_2212_, 0);
lean_inc_ref(v_config_2430_);
v_extensions_2431_ = lean_ctor_get(v_params_2212_, 1);
lean_inc_ref(v_extensions_2431_);
v_extraInj_2432_ = lean_ctor_get(v_params_2212_, 3);
lean_inc_ref(v_extraInj_2432_);
v_extraFacts_2433_ = lean_ctor_get(v_params_2212_, 4);
lean_inc_ref(v_extraFacts_2433_);
v_symPrios_2434_ = lean_ctor_get(v_params_2212_, 5);
lean_inc_ref(v_symPrios_2434_);
v_norm_2435_ = lean_ctor_get(v_params_2212_, 6);
lean_inc_ref(v_norm_2435_);
v_normProcs_2436_ = lean_ctor_get(v_params_2212_, 7);
lean_inc_ref(v_normProcs_2436_);
v_anchorRefs_x3f_2437_ = lean_ctor_get(v_params_2212_, 8);
lean_inc(v_anchorRefs_x3f_2437_);
lean_dec_ref(v_params_2212_);
v_size_2438_ = lean_ctor_get(v_extra_2356_, 2);
lean_inc(v_size_2438_);
v___y_2261_ = v_extra_2356_;
v___y_2262_ = v___y_2335_;
v___y_2263_ = v_extensions_2431_;
v___y_2264_ = v___y_2342_;
v___y_2265_ = v_norm_2435_;
v___y_2266_ = v___y_2339_;
v___y_2267_ = v___y_2336_;
v___y_2268_ = v_normProcs_2436_;
v___y_2269_ = v_symPrios_2434_;
v___y_2270_ = v_extraFacts_2433_;
v___y_2271_ = v___y_2341_;
v___y_2272_ = v_extraInj_2432_;
v___y_2273_ = v_anchorRefs_x3f_2437_;
v___y_2274_ = v___y_2340_;
v___y_2275_ = v_size_2438_;
v___y_2276_ = v_config_2430_;
goto v___jp_2260_;
}
default: 
{
lean_object* v_config_2439_; lean_object* v_extensions_2440_; lean_object* v_extraInj_2441_; lean_object* v_extraFacts_2442_; lean_object* v_symPrios_2443_; lean_object* v_norm_2444_; lean_object* v_normProcs_2445_; lean_object* v_anchorRefs_x3f_2446_; lean_object* v_size_2447_; 
v_config_2439_ = lean_ctor_get(v_params_2212_, 0);
lean_inc_ref(v_config_2439_);
v_extensions_2440_ = lean_ctor_get(v_params_2212_, 1);
lean_inc_ref(v_extensions_2440_);
v_extraInj_2441_ = lean_ctor_get(v_params_2212_, 3);
lean_inc_ref(v_extraInj_2441_);
v_extraFacts_2442_ = lean_ctor_get(v_params_2212_, 4);
lean_inc_ref(v_extraFacts_2442_);
v_symPrios_2443_ = lean_ctor_get(v_params_2212_, 5);
lean_inc_ref(v_symPrios_2443_);
v_norm_2444_ = lean_ctor_get(v_params_2212_, 6);
lean_inc_ref(v_norm_2444_);
v_normProcs_2445_ = lean_ctor_get(v_params_2212_, 7);
lean_inc_ref(v_normProcs_2445_);
v_anchorRefs_x3f_2446_ = lean_ctor_get(v_params_2212_, 8);
lean_inc(v_anchorRefs_x3f_2446_);
lean_dec_ref(v_params_2212_);
v_size_2447_ = lean_ctor_get(v_extra_2356_, 2);
lean_inc(v_size_2447_);
v___y_2225_ = v_normProcs_2445_;
v___y_2226_ = v_extra_2356_;
v___y_2227_ = v_symPrios_2443_;
v___y_2228_ = v_extraFacts_2442_;
v___y_2229_ = v___y_2335_;
v___y_2230_ = v_extraInj_2441_;
v___y_2231_ = v_extensions_2440_;
v___y_2232_ = v_anchorRefs_x3f_2446_;
v___y_2233_ = v_size_2447_;
v___y_2234_ = v_norm_2444_;
v___y_2235_ = v_config_2439_;
v___y_2236_ = v___y_2336_;
v___y_2237_ = v___y_2339_;
v___y_2238_ = v___y_2340_;
v___y_2239_ = v___y_2341_;
v___y_2240_ = v___y_2342_;
goto v___jp_2224_;
}
}
}
}
}
v___jp_2448_:
{
lean_object* v___x_2456_; uint8_t v___x_2457_; lean_object* v___x_2458_; lean_object* v___f_2459_; lean_object* v___x_2460_; 
v___x_2456_ = lean_box(0);
v___x_2457_ = 1;
v___x_2458_ = lean_box(v___x_2457_);
lean_inc(v_p_2213_);
v___f_2459_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2459_, 0, v_p_2213_);
lean_closure_set(v___f_2459_, 1, v_term_2215_);
lean_closure_set(v___f_2459_, 2, v___x_2456_);
lean_closure_set(v___f_2459_, 3, v___x_2458_);
v___x_2460_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2459_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2505_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2505_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2505_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
if (lean_obj_tag(v_a_2461_) == 1)
{
lean_object* v_val_2465_; lean_object* v_fst_2466_; lean_object* v_snd_2467_; lean_object* v___x_2468_; 
lean_del_object(v___x_2463_);
v_val_2465_ = lean_ctor_get(v_a_2461_, 0);
lean_inc(v_val_2465_);
lean_dec_ref(v_a_2461_);
v_fst_2466_ = lean_ctor_get(v_val_2465_, 0);
lean_inc(v_fst_2466_);
v_snd_2467_ = lean_ctor_get(v_val_2465_, 1);
lean_inc_n(v_snd_2467_, 2);
lean_dec(v_val_2465_);
lean_inc(v___y_2455_);
lean_inc_ref(v___y_2454_);
lean_inc(v___y_2453_);
lean_inc_ref(v___y_2452_);
v___x_2468_ = lean_infer_type(v_snd_2467_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2470_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc_n(v_a_2469_, 2);
lean_dec_ref(v___x_2468_);
v___x_2470_ = l_Lean_Meta_isProp(v_a_2469_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___f_2474_; uint8_t v___x_2475_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref(v___x_2470_);
v___x_2472_ = lean_box(v___x_2457_);
v___x_2473_ = lean_box(v_minIndexable_2216_);
lean_inc(v_snd_2467_);
lean_inc(v_fst_2466_);
lean_inc_ref(v_params_2212_);
v___f_2474_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 13, 6);
lean_closure_set(v___f_2474_, 0, v_params_2212_);
lean_closure_set(v___f_2474_, 1, v_p_2213_);
lean_closure_set(v___f_2474_, 2, v_fst_2466_);
lean_closure_set(v___f_2474_, 3, v_snd_2467_);
lean_closure_set(v___f_2474_, 4, v___x_2472_);
lean_closure_set(v___f_2474_, 5, v___x_2473_);
v___x_2475_ = lean_unbox(v_a_2471_);
lean_dec(v_a_2471_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v___f_2474_);
lean_dec(v_a_2469_);
lean_dec(v_snd_2467_);
lean_dec(v_fst_2466_);
lean_dec(v_kind_2449_);
lean_dec(v_mod_x3f_2214_);
lean_dec_ref(v_params_2212_);
v___x_2476_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2477_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2476_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec_ref(v___y_2454_);
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
else
{
v___y_2332_ = v_fst_2466_;
v___y_2333_ = v_a_2469_;
v___y_2334_ = v_snd_2467_;
v___y_2335_ = v___f_2474_;
v___y_2336_ = v_kind_2449_;
v___y_2337_ = v___y_2450_;
v___y_2338_ = v___y_2451_;
v___y_2339_ = v___y_2452_;
v___y_2340_ = v___y_2453_;
v___y_2341_ = v___y_2454_;
v___y_2342_ = v___y_2455_;
goto v___jp_2331_;
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v_a_2469_);
lean_dec(v_snd_2467_);
lean_dec(v_fst_2466_);
lean_dec_ref(v___y_2454_);
lean_dec(v_kind_2449_);
lean_dec(v_mod_x3f_2214_);
lean_dec(v_p_2213_);
lean_dec_ref(v_params_2212_);
v_a_2486_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2470_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2470_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec(v_snd_2467_);
lean_dec(v_fst_2466_);
lean_dec_ref(v___y_2454_);
lean_dec(v_kind_2449_);
lean_dec(v_mod_x3f_2214_);
lean_dec(v_p_2213_);
lean_dec_ref(v_params_2212_);
v_a_2494_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2468_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2468_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
else
{
lean_object* v___x_2503_; 
lean_dec(v_a_2461_);
lean_dec_ref(v___y_2454_);
lean_dec(v_kind_2449_);
lean_dec(v_mod_x3f_2214_);
lean_dec(v_p_2213_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v_params_2212_);
v___x_2503_ = v___x_2463_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_params_2212_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec_ref(v___y_2454_);
lean_dec(v_kind_2449_);
lean_dec(v_mod_x3f_2214_);
lean_dec(v_p_2213_);
lean_dec_ref(v_params_2212_);
v_a_2506_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2460_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2460_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
v___jp_2514_:
{
lean_object* v___x_2521_; 
v___x_2521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_kind_2449_ = v___x_2521_;
v___y_2450_ = v___y_2515_;
v___y_2451_ = v___y_2516_;
v___y_2452_ = v___y_2517_;
v___y_2453_ = v___y_2518_;
v___y_2454_ = v___y_2519_;
v___y_2455_ = v___y_2520_;
goto v___jp_2448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2608_, lean_object* v_p_2609_, lean_object* v_mod_x3f_2610_, lean_object* v_term_2611_, lean_object* v_minIndexable_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
uint8_t v_minIndexable_boxed_2620_; lean_object* v_res_2621_; 
v_minIndexable_boxed_2620_ = lean_unbox(v_minIndexable_2612_);
v_res_2621_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2608_, v_p_2609_, v_mod_x3f_2610_, v_term_2611_, v_minIndexable_boxed_2620_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
lean_dec(v_a_2618_);
lean_dec_ref(v_a_2617_);
lean_dec(v_a_2616_);
lean_dec_ref(v_a_2615_);
lean_dec(v_a_2614_);
lean_dec_ref(v_a_2613_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object* v_00_u03b1_2622_, lean_object* v_msg_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v_00_u03b1_2632_, lean_object* v_msg_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v_00_u03b1_2632_, v_msg_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object* v_msgData_2642_, lean_object* v_macroStack_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2642_, v_macroStack_2643_, v___y_2648_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object* v_msgData_2652_, lean_object* v_macroStack_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(v_msgData_2652_, v_macroStack_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2662_, lean_object* v_val_2663_, lean_object* v_____r_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; lean_object* v_ext_2673_; lean_object* v_toEnvExtension_2674_; lean_object* v_env_2675_; lean_object* v_config_2676_; lean_object* v_extensions_2677_; lean_object* v_extra_2678_; lean_object* v_extraInj_2679_; lean_object* v_extraFacts_2680_; lean_object* v_symPrios_2681_; lean_object* v_norm_2682_; lean_object* v_normProcs_2683_; lean_object* v_anchorRefs_x3f_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2697_; 
v___x_2672_ = lean_st_ref_get(v___y_2670_);
v_ext_2673_ = lean_ctor_get(v_val_2663_, 1);
v_toEnvExtension_2674_ = lean_ctor_get(v_ext_2673_, 0);
v_env_2675_ = lean_ctor_get(v___x_2672_, 0);
lean_inc_ref(v_env_2675_);
lean_dec(v___x_2672_);
v_config_2676_ = lean_ctor_get(v_params_2662_, 0);
v_extensions_2677_ = lean_ctor_get(v_params_2662_, 1);
v_extra_2678_ = lean_ctor_get(v_params_2662_, 2);
v_extraInj_2679_ = lean_ctor_get(v_params_2662_, 3);
v_extraFacts_2680_ = lean_ctor_get(v_params_2662_, 4);
v_symPrios_2681_ = lean_ctor_get(v_params_2662_, 5);
v_norm_2682_ = lean_ctor_get(v_params_2662_, 6);
v_normProcs_2683_ = lean_ctor_get(v_params_2662_, 7);
v_anchorRefs_x3f_2684_ = lean_ctor_get(v_params_2662_, 8);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_params_2662_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2686_ = v_params_2662_;
v_isShared_2687_ = v_isSharedCheck_2697_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_anchorRefs_x3f_2684_);
lean_inc(v_normProcs_2683_);
lean_inc(v_norm_2682_);
lean_inc(v_symPrios_2681_);
lean_inc(v_extraFacts_2680_);
lean_inc(v_extraInj_2679_);
lean_inc(v_extra_2678_);
lean_inc(v_extensions_2677_);
lean_inc(v_config_2676_);
lean_dec(v_params_2662_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2697_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_asyncMode_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
v_asyncMode_2688_ = lean_ctor_get(v_toEnvExtension_2674_, 2);
v___x_2689_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2690_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2689_, v_val_2663_, v_env_2675_, v_asyncMode_2688_);
v___x_2691_ = lean_array_push(v_extensions_2677_, v___x_2690_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 1, v___x_2691_);
v___x_2693_ = v___x_2686_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_config_2676_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2691_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_extra_2678_);
lean_ctor_set(v_reuseFailAlloc_2696_, 3, v_extraInj_2679_);
lean_ctor_set(v_reuseFailAlloc_2696_, 4, v_extraFacts_2680_);
lean_ctor_set(v_reuseFailAlloc_2696_, 5, v_symPrios_2681_);
lean_ctor_set(v_reuseFailAlloc_2696_, 6, v_norm_2682_);
lean_ctor_set(v_reuseFailAlloc_2696_, 7, v_normProcs_2683_);
lean_ctor_set(v_reuseFailAlloc_2696_, 8, v_anchorRefs_x3f_2684_);
v___x_2693_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
return v___x_2695_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2698_, lean_object* v_val_2699_, lean_object* v_____r_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2698_, v_val_2699_, v_____r_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec_ref(v_val_2699_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2709_, lean_object* v_id_2710_, uint8_t v_minIndexable_2711_, lean_object* v_as_x27_2712_, lean_object* v_b_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
if (lean_obj_tag(v_as_x27_2712_) == 0)
{
lean_object* v___x_2719_; 
lean_dec(v_id_2710_);
v___x_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2719_, 0, v_b_2713_);
return v___x_2719_;
}
else
{
lean_object* v_head_2720_; lean_object* v_tail_2721_; lean_object* v_fileName_2722_; lean_object* v_fileMap_2723_; lean_object* v_options_2724_; lean_object* v_currRecDepth_2725_; lean_object* v_maxRecDepth_2726_; lean_object* v_ref_2727_; lean_object* v_currNamespace_2728_; lean_object* v_openDecls_2729_; lean_object* v_initHeartbeats_2730_; lean_object* v_maxHeartbeats_2731_; lean_object* v_quotContext_2732_; lean_object* v_currMacroScope_2733_; uint8_t v_diag_2734_; lean_object* v_cancelTk_x3f_2735_; uint8_t v_suppressElabErrors_2736_; lean_object* v_inheritedTraceOptions_2737_; uint8_t v___x_2738_; lean_object* v___x_2739_; lean_object* v_ref_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_head_2720_ = lean_ctor_get(v_as_x27_2712_, 0);
v_tail_2721_ = lean_ctor_get(v_as_x27_2712_, 1);
v_fileName_2722_ = lean_ctor_get(v___y_2716_, 0);
v_fileMap_2723_ = lean_ctor_get(v___y_2716_, 1);
v_options_2724_ = lean_ctor_get(v___y_2716_, 2);
v_currRecDepth_2725_ = lean_ctor_get(v___y_2716_, 3);
v_maxRecDepth_2726_ = lean_ctor_get(v___y_2716_, 4);
v_ref_2727_ = lean_ctor_get(v___y_2716_, 5);
v_currNamespace_2728_ = lean_ctor_get(v___y_2716_, 6);
v_openDecls_2729_ = lean_ctor_get(v___y_2716_, 7);
v_initHeartbeats_2730_ = lean_ctor_get(v___y_2716_, 8);
v_maxHeartbeats_2731_ = lean_ctor_get(v___y_2716_, 9);
v_quotContext_2732_ = lean_ctor_get(v___y_2716_, 10);
v_currMacroScope_2733_ = lean_ctor_get(v___y_2716_, 11);
v_diag_2734_ = lean_ctor_get_uint8(v___y_2716_, sizeof(void*)*14);
v_cancelTk_x3f_2735_ = lean_ctor_get(v___y_2716_, 12);
v_suppressElabErrors_2736_ = lean_ctor_get_uint8(v___y_2716_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2737_ = lean_ctor_get(v___y_2716_, 13);
v___x_2738_ = 0;
v___x_2739_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_2740_ = l_Lean_replaceRef(v_p_2709_, v_ref_2727_);
lean_inc_ref(v_inheritedTraceOptions_2737_);
lean_inc(v_cancelTk_x3f_2735_);
lean_inc(v_currMacroScope_2733_);
lean_inc(v_quotContext_2732_);
lean_inc(v_maxHeartbeats_2731_);
lean_inc(v_initHeartbeats_2730_);
lean_inc(v_openDecls_2729_);
lean_inc(v_currNamespace_2728_);
lean_inc(v_maxRecDepth_2726_);
lean_inc(v_currRecDepth_2725_);
lean_inc_ref(v_options_2724_);
lean_inc_ref(v_fileMap_2723_);
lean_inc_ref(v_fileName_2722_);
v___x_2741_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2741_, 0, v_fileName_2722_);
lean_ctor_set(v___x_2741_, 1, v_fileMap_2723_);
lean_ctor_set(v___x_2741_, 2, v_options_2724_);
lean_ctor_set(v___x_2741_, 3, v_currRecDepth_2725_);
lean_ctor_set(v___x_2741_, 4, v_maxRecDepth_2726_);
lean_ctor_set(v___x_2741_, 5, v_ref_2740_);
lean_ctor_set(v___x_2741_, 6, v_currNamespace_2728_);
lean_ctor_set(v___x_2741_, 7, v_openDecls_2729_);
lean_ctor_set(v___x_2741_, 8, v_initHeartbeats_2730_);
lean_ctor_set(v___x_2741_, 9, v_maxHeartbeats_2731_);
lean_ctor_set(v___x_2741_, 10, v_quotContext_2732_);
lean_ctor_set(v___x_2741_, 11, v_currMacroScope_2733_);
lean_ctor_set(v___x_2741_, 12, v_cancelTk_x3f_2735_);
lean_ctor_set(v___x_2741_, 13, v_inheritedTraceOptions_2737_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*14, v_diag_2734_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*14 + 1, v_suppressElabErrors_2736_);
lean_inc(v_head_2720_);
lean_inc(v_id_2710_);
v___x_2742_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2713_, v_id_2710_, v_head_2720_, v___x_2739_, v_minIndexable_2711_, v___x_2738_, v___x_2738_, v___y_2714_, v___y_2715_, v___x_2741_, v___y_2717_);
lean_dec_ref(v___x_2741_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref(v___x_2742_);
v_as_x27_2712_ = v_tail_2721_;
v_b_2713_ = v_a_2743_;
goto _start;
}
else
{
lean_dec(v_id_2710_);
return v___x_2742_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_2745_, lean_object* v_id_2746_, lean_object* v_minIndexable_2747_, lean_object* v_as_x27_2748_, lean_object* v_b_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
uint8_t v_minIndexable_boxed_2755_; lean_object* v_res_2756_; 
v_minIndexable_boxed_2755_ = lean_unbox(v_minIndexable_2747_);
v_res_2756_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_2745_, v_id_2746_, v_minIndexable_boxed_2755_, v_as_x27_2748_, v_b_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v_as_x27_2748_);
lean_dec(v_p_2745_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
if (lean_obj_tag(v_a_2758_) == 0)
{
lean_object* v___x_2760_; 
v___x_2760_ = l_List_reverse___redArg(v_a_2759_);
return v___x_2760_;
}
else
{
lean_object* v_head_2761_; lean_object* v_tail_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2773_; 
v_head_2761_ = lean_ctor_get(v_a_2758_, 0);
v_tail_2762_ = lean_ctor_get(v_a_2758_, 1);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_a_2758_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2764_ = v_a_2758_;
v_isShared_2765_ = v_isSharedCheck_2773_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_tail_2762_);
lean_inc(v_head_2761_);
lean_dec(v_a_2758_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2773_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_kind_2766_; uint8_t v___x_2767_; 
v_kind_2766_ = lean_ctor_get(v_head_2761_, 6);
v___x_2767_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_2766_, v_k_2757_);
if (v___x_2767_ == 0)
{
lean_del_object(v___x_2764_);
lean_dec(v_head_2761_);
v_a_2758_ = v_tail_2762_;
goto _start;
}
else
{
lean_object* v___x_2770_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 1, v_a_2759_);
v___x_2770_ = v___x_2764_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_head_2761_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_a_2759_);
v___x_2770_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
v_a_2758_ = v_tail_2762_;
v_a_2759_ = v___x_2770_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_2774_, v_a_2775_, v_a_2776_);
lean_dec(v_k_2774_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_2778_, lean_object* v_msg_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_fileName_2787_; lean_object* v_fileMap_2788_; lean_object* v_options_2789_; lean_object* v_currRecDepth_2790_; lean_object* v_maxRecDepth_2791_; lean_object* v_ref_2792_; lean_object* v_currNamespace_2793_; lean_object* v_openDecls_2794_; lean_object* v_initHeartbeats_2795_; lean_object* v_maxHeartbeats_2796_; lean_object* v_quotContext_2797_; lean_object* v_currMacroScope_2798_; uint8_t v_diag_2799_; lean_object* v_cancelTk_x3f_2800_; uint8_t v_suppressElabErrors_2801_; lean_object* v_inheritedTraceOptions_2802_; lean_object* v_ref_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_fileName_2787_ = lean_ctor_get(v___y_2784_, 0);
v_fileMap_2788_ = lean_ctor_get(v___y_2784_, 1);
v_options_2789_ = lean_ctor_get(v___y_2784_, 2);
v_currRecDepth_2790_ = lean_ctor_get(v___y_2784_, 3);
v_maxRecDepth_2791_ = lean_ctor_get(v___y_2784_, 4);
v_ref_2792_ = lean_ctor_get(v___y_2784_, 5);
v_currNamespace_2793_ = lean_ctor_get(v___y_2784_, 6);
v_openDecls_2794_ = lean_ctor_get(v___y_2784_, 7);
v_initHeartbeats_2795_ = lean_ctor_get(v___y_2784_, 8);
v_maxHeartbeats_2796_ = lean_ctor_get(v___y_2784_, 9);
v_quotContext_2797_ = lean_ctor_get(v___y_2784_, 10);
v_currMacroScope_2798_ = lean_ctor_get(v___y_2784_, 11);
v_diag_2799_ = lean_ctor_get_uint8(v___y_2784_, sizeof(void*)*14);
v_cancelTk_x3f_2800_ = lean_ctor_get(v___y_2784_, 12);
v_suppressElabErrors_2801_ = lean_ctor_get_uint8(v___y_2784_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2802_ = lean_ctor_get(v___y_2784_, 13);
v_ref_2803_ = l_Lean_replaceRef(v_ref_2778_, v_ref_2792_);
lean_inc_ref(v_inheritedTraceOptions_2802_);
lean_inc(v_cancelTk_x3f_2800_);
lean_inc(v_currMacroScope_2798_);
lean_inc(v_quotContext_2797_);
lean_inc(v_maxHeartbeats_2796_);
lean_inc(v_initHeartbeats_2795_);
lean_inc(v_openDecls_2794_);
lean_inc(v_currNamespace_2793_);
lean_inc(v_maxRecDepth_2791_);
lean_inc(v_currRecDepth_2790_);
lean_inc_ref(v_options_2789_);
lean_inc_ref(v_fileMap_2788_);
lean_inc_ref(v_fileName_2787_);
v___x_2804_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2804_, 0, v_fileName_2787_);
lean_ctor_set(v___x_2804_, 1, v_fileMap_2788_);
lean_ctor_set(v___x_2804_, 2, v_options_2789_);
lean_ctor_set(v___x_2804_, 3, v_currRecDepth_2790_);
lean_ctor_set(v___x_2804_, 4, v_maxRecDepth_2791_);
lean_ctor_set(v___x_2804_, 5, v_ref_2803_);
lean_ctor_set(v___x_2804_, 6, v_currNamespace_2793_);
lean_ctor_set(v___x_2804_, 7, v_openDecls_2794_);
lean_ctor_set(v___x_2804_, 8, v_initHeartbeats_2795_);
lean_ctor_set(v___x_2804_, 9, v_maxHeartbeats_2796_);
lean_ctor_set(v___x_2804_, 10, v_quotContext_2797_);
lean_ctor_set(v___x_2804_, 11, v_currMacroScope_2798_);
lean_ctor_set(v___x_2804_, 12, v_cancelTk_x3f_2800_);
lean_ctor_set(v___x_2804_, 13, v_inheritedTraceOptions_2802_);
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*14, v_diag_2799_);
lean_ctor_set_uint8(v___x_2804_, sizeof(void*)*14 + 1, v_suppressElabErrors_2801_);
v___x_2805_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___x_2804_, v___y_2785_);
lean_dec_ref(v___x_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_2806_, lean_object* v_msg_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_2806_, v_msg_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v_ref_2806_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_2816_, lean_object* v_id_2817_, uint8_t v_minIndexable_2818_, lean_object* v_as_x27_2819_, lean_object* v_b_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
if (lean_obj_tag(v_as_x27_2819_) == 0)
{
lean_object* v___x_2826_; 
lean_dec(v_id_2817_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_b_2820_);
return v___x_2826_;
}
else
{
lean_object* v_head_2827_; lean_object* v_tail_2828_; lean_object* v_fileName_2829_; lean_object* v_fileMap_2830_; lean_object* v_options_2831_; lean_object* v_currRecDepth_2832_; lean_object* v_maxRecDepth_2833_; lean_object* v_ref_2834_; lean_object* v_currNamespace_2835_; lean_object* v_openDecls_2836_; lean_object* v_initHeartbeats_2837_; lean_object* v_maxHeartbeats_2838_; lean_object* v_quotContext_2839_; lean_object* v_currMacroScope_2840_; uint8_t v_diag_2841_; lean_object* v_cancelTk_x3f_2842_; uint8_t v_suppressElabErrors_2843_; lean_object* v_inheritedTraceOptions_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; lean_object* v_ref_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v_head_2827_ = lean_ctor_get(v_as_x27_2819_, 0);
v_tail_2828_ = lean_ctor_get(v_as_x27_2819_, 1);
v_fileName_2829_ = lean_ctor_get(v___y_2823_, 0);
v_fileMap_2830_ = lean_ctor_get(v___y_2823_, 1);
v_options_2831_ = lean_ctor_get(v___y_2823_, 2);
v_currRecDepth_2832_ = lean_ctor_get(v___y_2823_, 3);
v_maxRecDepth_2833_ = lean_ctor_get(v___y_2823_, 4);
v_ref_2834_ = lean_ctor_get(v___y_2823_, 5);
v_currNamespace_2835_ = lean_ctor_get(v___y_2823_, 6);
v_openDecls_2836_ = lean_ctor_get(v___y_2823_, 7);
v_initHeartbeats_2837_ = lean_ctor_get(v___y_2823_, 8);
v_maxHeartbeats_2838_ = lean_ctor_get(v___y_2823_, 9);
v_quotContext_2839_ = lean_ctor_get(v___y_2823_, 10);
v_currMacroScope_2840_ = lean_ctor_get(v___y_2823_, 11);
v_diag_2841_ = lean_ctor_get_uint8(v___y_2823_, sizeof(void*)*14);
v_cancelTk_x3f_2842_ = lean_ctor_get(v___y_2823_, 12);
v_suppressElabErrors_2843_ = lean_ctor_get_uint8(v___y_2823_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2844_ = lean_ctor_get(v___y_2823_, 13);
v___x_2845_ = 0;
v___x_2846_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_2847_ = 1;
v_ref_2848_ = l_Lean_replaceRef(v_p_2816_, v_ref_2834_);
lean_inc_ref(v_inheritedTraceOptions_2844_);
lean_inc(v_cancelTk_x3f_2842_);
lean_inc(v_currMacroScope_2840_);
lean_inc(v_quotContext_2839_);
lean_inc(v_maxHeartbeats_2838_);
lean_inc(v_initHeartbeats_2837_);
lean_inc(v_openDecls_2836_);
lean_inc(v_currNamespace_2835_);
lean_inc(v_maxRecDepth_2833_);
lean_inc(v_currRecDepth_2832_);
lean_inc_ref(v_options_2831_);
lean_inc_ref(v_fileMap_2830_);
lean_inc_ref(v_fileName_2829_);
v___x_2849_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2849_, 0, v_fileName_2829_);
lean_ctor_set(v___x_2849_, 1, v_fileMap_2830_);
lean_ctor_set(v___x_2849_, 2, v_options_2831_);
lean_ctor_set(v___x_2849_, 3, v_currRecDepth_2832_);
lean_ctor_set(v___x_2849_, 4, v_maxRecDepth_2833_);
lean_ctor_set(v___x_2849_, 5, v_ref_2848_);
lean_ctor_set(v___x_2849_, 6, v_currNamespace_2835_);
lean_ctor_set(v___x_2849_, 7, v_openDecls_2836_);
lean_ctor_set(v___x_2849_, 8, v_initHeartbeats_2837_);
lean_ctor_set(v___x_2849_, 9, v_maxHeartbeats_2838_);
lean_ctor_set(v___x_2849_, 10, v_quotContext_2839_);
lean_ctor_set(v___x_2849_, 11, v_currMacroScope_2840_);
lean_ctor_set(v___x_2849_, 12, v_cancelTk_x3f_2842_);
lean_ctor_set(v___x_2849_, 13, v_inheritedTraceOptions_2844_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*14, v_diag_2841_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*14 + 1, v_suppressElabErrors_2843_);
lean_inc(v_head_2827_);
lean_inc(v_id_2817_);
v___x_2850_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2820_, v_id_2817_, v_head_2827_, v___x_2846_, v_minIndexable_2818_, v___x_2845_, v___x_2847_, v___y_2821_, v___y_2822_, v___x_2849_, v___y_2824_);
lean_dec_ref(v___x_2849_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref(v___x_2850_);
v_as_x27_2819_ = v_tail_2828_;
v_b_2820_ = v_a_2851_;
goto _start;
}
else
{
lean_dec(v_id_2817_);
return v___x_2850_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_2853_, lean_object* v_id_2854_, lean_object* v_minIndexable_2855_, lean_object* v_as_x27_2856_, lean_object* v_b_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
uint8_t v_minIndexable_boxed_2863_; lean_object* v_res_2864_; 
v_minIndexable_boxed_2863_ = lean_unbox(v_minIndexable_2855_);
v_res_2864_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_2853_, v_id_2854_, v_minIndexable_boxed_2863_, v_as_x27_2856_, v_b_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v_as_x27_2856_);
lean_dec(v_p_2853_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_2865_){
_start:
{
if (lean_obj_tag(v_x_2865_) == 0)
{
lean_object* v___x_2866_; 
v___x_2866_ = lean_box(0);
return v___x_2866_;
}
else
{
lean_object* v_head_2867_; lean_object* v_tail_2868_; lean_object* v_fst_2869_; uint8_t v___x_2870_; 
v_head_2867_ = lean_ctor_get(v_x_2865_, 0);
v_tail_2868_ = lean_ctor_get(v_x_2865_, 1);
v_fst_2869_ = lean_ctor_get(v_head_2867_, 0);
v___x_2870_ = l_Lean_isPrivateName(v_fst_2869_);
if (v___x_2870_ == 0)
{
v_x_2865_ = v_tail_2868_;
goto _start;
}
else
{
lean_object* v___x_2872_; 
lean_inc(v_head_2867_);
v___x_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2872_, 0, v_head_2867_);
return v___x_2872_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_2873_);
lean_dec(v_x_2873_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_2875_, lean_object* v_msgData_2876_, uint8_t v_severity_2877_, uint8_t v_isSilent_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v___y_2885_; uint8_t v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; uint8_t v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2921_; lean_object* v___y_2922_; uint8_t v___y_2923_; lean_object* v___y_2924_; uint8_t v___y_2925_; uint8_t v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2946_; lean_object* v___y_2947_; uint8_t v___y_2948_; lean_object* v___y_2949_; uint8_t v___y_2950_; uint8_t v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; uint8_t v___y_2960_; uint8_t v___y_2961_; lean_object* v___y_2962_; uint8_t v___y_2963_; uint8_t v___x_2968_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; uint8_t v___y_2973_; lean_object* v___y_2974_; uint8_t v___y_2975_; uint8_t v___y_2976_; uint8_t v___y_2978_; uint8_t v___x_2993_; 
v___x_2968_ = 2;
v___x_2993_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2877_, v___x_2968_);
if (v___x_2993_ == 0)
{
v___y_2978_ = v___x_2993_;
goto v___jp_2977_;
}
else
{
uint8_t v___x_2994_; 
lean_inc_ref(v_msgData_2876_);
v___x_2994_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2876_);
v___y_2978_ = v___x_2994_;
goto v___jp_2977_;
}
v___jp_2884_:
{
lean_object* v___x_2894_; lean_object* v_currNamespace_2895_; lean_object* v_openDecls_2896_; lean_object* v_env_2897_; lean_object* v_nextMacroScope_2898_; lean_object* v_ngen_2899_; lean_object* v_auxDeclNGen_2900_; lean_object* v_traceState_2901_; lean_object* v_cache_2902_; lean_object* v_messages_2903_; lean_object* v_infoState_2904_; lean_object* v_snapshotTasks_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2919_; 
v___x_2894_ = lean_st_ref_take(v___y_2893_);
v_currNamespace_2895_ = lean_ctor_get(v___y_2892_, 6);
v_openDecls_2896_ = lean_ctor_get(v___y_2892_, 7);
v_env_2897_ = lean_ctor_get(v___x_2894_, 0);
v_nextMacroScope_2898_ = lean_ctor_get(v___x_2894_, 1);
v_ngen_2899_ = lean_ctor_get(v___x_2894_, 2);
v_auxDeclNGen_2900_ = lean_ctor_get(v___x_2894_, 3);
v_traceState_2901_ = lean_ctor_get(v___x_2894_, 4);
v_cache_2902_ = lean_ctor_get(v___x_2894_, 5);
v_messages_2903_ = lean_ctor_get(v___x_2894_, 6);
v_infoState_2904_ = lean_ctor_get(v___x_2894_, 7);
v_snapshotTasks_2905_ = lean_ctor_get(v___x_2894_, 8);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2907_ = v___x_2894_;
v_isShared_2908_ = v_isSharedCheck_2919_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_snapshotTasks_2905_);
lean_inc(v_infoState_2904_);
lean_inc(v_messages_2903_);
lean_inc(v_cache_2902_);
lean_inc(v_traceState_2901_);
lean_inc(v_auxDeclNGen_2900_);
lean_inc(v_ngen_2899_);
lean_inc(v_nextMacroScope_2898_);
lean_inc(v_env_2897_);
lean_dec(v___x_2894_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2919_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
lean_inc(v_openDecls_2896_);
lean_inc(v_currNamespace_2895_);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v_currNamespace_2895_);
lean_ctor_set(v___x_2909_, 1, v_openDecls_2896_);
v___x_2910_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v___y_2885_);
lean_inc_ref(v___y_2888_);
lean_inc_ref(v___y_2891_);
v___x_2911_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2911_, 0, v___y_2891_);
lean_ctor_set(v___x_2911_, 1, v___y_2890_);
lean_ctor_set(v___x_2911_, 2, v___y_2887_);
lean_ctor_set(v___x_2911_, 3, v___y_2888_);
lean_ctor_set(v___x_2911_, 4, v___x_2910_);
lean_ctor_set_uint8(v___x_2911_, sizeof(void*)*5, v___y_2889_);
lean_ctor_set_uint8(v___x_2911_, sizeof(void*)*5 + 1, v___y_2886_);
lean_ctor_set_uint8(v___x_2911_, sizeof(void*)*5 + 2, v_isSilent_2878_);
v___x_2912_ = l_Lean_MessageLog_add(v___x_2911_, v_messages_2903_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 6, v___x_2912_);
v___x_2914_ = v___x_2907_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_env_2897_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_nextMacroScope_2898_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_ngen_2899_);
lean_ctor_set(v_reuseFailAlloc_2918_, 3, v_auxDeclNGen_2900_);
lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_traceState_2901_);
lean_ctor_set(v_reuseFailAlloc_2918_, 5, v_cache_2902_);
lean_ctor_set(v_reuseFailAlloc_2918_, 6, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2918_, 7, v_infoState_2904_);
lean_ctor_set(v_reuseFailAlloc_2918_, 8, v_snapshotTasks_2905_);
v___x_2914_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2915_ = lean_st_ref_set(v___y_2893_, v___x_2914_);
v___x_2916_ = lean_box(0);
v___x_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
return v___x_2917_;
}
}
}
v___jp_2920_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2944_; 
v___x_2929_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2876_);
v___x_2930_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_2929_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2944_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2944_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
lean_inc_ref_n(v___y_2924_, 2);
v___x_2935_ = l_Lean_FileMap_toPosition(v___y_2924_, v___y_2922_);
lean_dec(v___y_2922_);
v___x_2936_ = l_Lean_FileMap_toPosition(v___y_2924_, v___y_2928_);
lean_dec(v___y_2928_);
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
v___x_2938_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_2926_ == 0)
{
lean_del_object(v___x_2933_);
lean_dec_ref(v___y_2921_);
v___y_2885_ = v_a_2931_;
v___y_2886_ = v___y_2923_;
v___y_2887_ = v___x_2937_;
v___y_2888_ = v___x_2938_;
v___y_2889_ = v___y_2925_;
v___y_2890_ = v___x_2935_;
v___y_2891_ = v___y_2927_;
v___y_2892_ = v___y_2881_;
v___y_2893_ = v___y_2882_;
goto v___jp_2884_;
}
else
{
uint8_t v___x_2939_; 
lean_inc(v_a_2931_);
v___x_2939_ = l_Lean_MessageData_hasTag(v___y_2921_, v_a_2931_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
lean_dec_ref(v___x_2937_);
lean_dec_ref(v___x_2935_);
lean_dec(v_a_2931_);
v___x_2940_ = lean_box(0);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2940_);
v___x_2942_ = v___x_2933_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
else
{
lean_del_object(v___x_2933_);
v___y_2885_ = v_a_2931_;
v___y_2886_ = v___y_2923_;
v___y_2887_ = v___x_2937_;
v___y_2888_ = v___x_2938_;
v___y_2889_ = v___y_2925_;
v___y_2890_ = v___x_2935_;
v___y_2891_ = v___y_2927_;
v___y_2892_ = v___y_2881_;
v___y_2893_ = v___y_2882_;
goto v___jp_2884_;
}
}
}
}
v___jp_2945_:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Lean_Syntax_getTailPos_x3f(v___y_2947_, v___y_2950_);
lean_dec(v___y_2947_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_inc(v___y_2953_);
v___y_2921_ = v___y_2946_;
v___y_2922_ = v___y_2953_;
v___y_2923_ = v___y_2948_;
v___y_2924_ = v___y_2949_;
v___y_2925_ = v___y_2950_;
v___y_2926_ = v___y_2951_;
v___y_2927_ = v___y_2952_;
v___y_2928_ = v___y_2953_;
goto v___jp_2920_;
}
else
{
lean_object* v_val_2955_; 
v_val_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_val_2955_);
lean_dec_ref(v___x_2954_);
v___y_2921_ = v___y_2946_;
v___y_2922_ = v___y_2953_;
v___y_2923_ = v___y_2948_;
v___y_2924_ = v___y_2949_;
v___y_2925_ = v___y_2950_;
v___y_2926_ = v___y_2951_;
v___y_2927_ = v___y_2952_;
v___y_2928_ = v_val_2955_;
goto v___jp_2920_;
}
}
v___jp_2956_:
{
lean_object* v_ref_2964_; lean_object* v___x_2965_; 
v_ref_2964_ = l_Lean_replaceRef(v_ref_2875_, v___y_2959_);
v___x_2965_ = l_Lean_Syntax_getPos_x3f(v_ref_2964_, v___y_2960_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_unsigned_to_nat(0u);
v___y_2946_ = v___y_2957_;
v___y_2947_ = v_ref_2964_;
v___y_2948_ = v___y_2963_;
v___y_2949_ = v___y_2958_;
v___y_2950_ = v___y_2960_;
v___y_2951_ = v___y_2961_;
v___y_2952_ = v___y_2962_;
v___y_2953_ = v___x_2966_;
goto v___jp_2945_;
}
else
{
lean_object* v_val_2967_; 
v_val_2967_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_val_2967_);
lean_dec_ref(v___x_2965_);
v___y_2946_ = v___y_2957_;
v___y_2947_ = v_ref_2964_;
v___y_2948_ = v___y_2963_;
v___y_2949_ = v___y_2958_;
v___y_2950_ = v___y_2960_;
v___y_2951_ = v___y_2961_;
v___y_2952_ = v___y_2962_;
v___y_2953_ = v_val_2967_;
goto v___jp_2945_;
}
}
v___jp_2969_:
{
if (v___y_2976_ == 0)
{
v___y_2957_ = v___y_2972_;
v___y_2958_ = v___y_2970_;
v___y_2959_ = v___y_2971_;
v___y_2960_ = v___y_2975_;
v___y_2961_ = v___y_2973_;
v___y_2962_ = v___y_2974_;
v___y_2963_ = v_severity_2877_;
goto v___jp_2956_;
}
else
{
v___y_2957_ = v___y_2972_;
v___y_2958_ = v___y_2970_;
v___y_2959_ = v___y_2971_;
v___y_2960_ = v___y_2975_;
v___y_2961_ = v___y_2973_;
v___y_2962_ = v___y_2974_;
v___y_2963_ = v___x_2968_;
goto v___jp_2956_;
}
}
v___jp_2977_:
{
if (v___y_2978_ == 0)
{
lean_object* v_fileName_2979_; lean_object* v_fileMap_2980_; lean_object* v_options_2981_; lean_object* v_ref_2982_; uint8_t v_suppressElabErrors_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___f_2986_; uint8_t v___x_2987_; uint8_t v___x_2988_; 
v_fileName_2979_ = lean_ctor_get(v___y_2881_, 0);
v_fileMap_2980_ = lean_ctor_get(v___y_2881_, 1);
v_options_2981_ = lean_ctor_get(v___y_2881_, 2);
v_ref_2982_ = lean_ctor_get(v___y_2881_, 5);
v_suppressElabErrors_2983_ = lean_ctor_get_uint8(v___y_2881_, sizeof(void*)*14 + 1);
v___x_2984_ = lean_box(v___y_2978_);
v___x_2985_ = lean_box(v_suppressElabErrors_2983_);
v___f_2986_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2986_, 0, v___x_2984_);
lean_closure_set(v___f_2986_, 1, v___x_2985_);
v___x_2987_ = 1;
v___x_2988_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2877_, v___x_2987_);
if (v___x_2988_ == 0)
{
v___y_2970_ = v_fileMap_2980_;
v___y_2971_ = v_ref_2982_;
v___y_2972_ = v___f_2986_;
v___y_2973_ = v_suppressElabErrors_2983_;
v___y_2974_ = v_fileName_2979_;
v___y_2975_ = v___y_2978_;
v___y_2976_ = v___x_2988_;
goto v___jp_2969_;
}
else
{
lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2989_ = l_Lean_warningAsError;
v___x_2990_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2981_, v___x_2989_);
v___y_2970_ = v_fileMap_2980_;
v___y_2971_ = v_ref_2982_;
v___y_2972_ = v___f_2986_;
v___y_2973_ = v_suppressElabErrors_2983_;
v___y_2974_ = v_fileName_2979_;
v___y_2975_ = v___y_2978_;
v___y_2976_ = v___x_2990_;
goto v___jp_2969_;
}
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_dec_ref(v_msgData_2876_);
v___x_2991_ = lean_box(0);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_2995_, lean_object* v_msgData_2996_, lean_object* v_severity_2997_, lean_object* v_isSilent_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
uint8_t v_severity_boxed_3004_; uint8_t v_isSilent_boxed_3005_; lean_object* v_res_3006_; 
v_severity_boxed_3004_ = lean_unbox(v_severity_2997_);
v_isSilent_boxed_3005_ = lean_unbox(v_isSilent_2998_);
v_res_3006_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_2995_, v_msgData_2996_, v_severity_boxed_3004_, v_isSilent_boxed_3005_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v_ref_2995_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_3007_, uint8_t v_severity_3008_, uint8_t v_isSilent_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v_ref_3017_; lean_object* v___x_3018_; 
v_ref_3017_ = lean_ctor_get(v___y_3014_, 5);
v___x_3018_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3017_, v_msgData_3007_, v_severity_3008_, v_isSilent_3009_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_3019_, lean_object* v_severity_3020_, lean_object* v_isSilent_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
uint8_t v_severity_boxed_3029_; uint8_t v_isSilent_boxed_3030_; lean_object* v_res_3031_; 
v_severity_boxed_3029_ = lean_unbox(v_severity_3020_);
v_isSilent_boxed_3030_ = lean_unbox(v_isSilent_3021_);
v_res_3031_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3019_, v_severity_boxed_3029_, v_isSilent_boxed_3030_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
uint8_t v___x_3040_; uint8_t v___x_3041_; lean_object* v___x_3042_; 
v___x_3040_ = 1;
v___x_3041_ = 0;
v___x_3042_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3032_, v___x_3040_, v___x_3041_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_options_3055_; uint8_t v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_options_3055_ = lean_ctor_get(v___y_3053_, 2);
v___x_3056_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_3055_, v_opt_3052_);
v___x_3057_ = lean_box(v___x_3056_);
v___x_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3059_, v___y_3060_);
lean_dec_ref(v___y_3060_);
lean_dec_ref(v_opt_3059_);
return v_res_3062_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3065_ = l_Lean_stringToMessageData(v___x_3064_);
return v___x_3065_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3068_ = l_Lean_stringToMessageData(v___x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v___x_3077_; lean_object* v_env_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3100_; 
v___x_3077_ = lean_st_ref_get(v___y_3075_);
v_env_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc_ref(v_env_3078_);
lean_dec(v___x_3077_);
v___x_3079_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3080_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3079_, v___y_3074_);
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3083_ = v___x_3080_;
v_isShared_3084_ = v_isSharedCheck_3100_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3100_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
uint8_t v_isExporting_3090_; 
v_isExporting_3090_ = lean_ctor_get_uint8(v_env_3078_, sizeof(void*)*8);
lean_dec_ref(v_env_3078_);
if (v_isExporting_3090_ == 0)
{
lean_dec(v_a_3081_);
lean_dec(v_id_3069_);
goto v___jp_3085_;
}
else
{
uint8_t v___x_3091_; 
v___x_3091_ = l_Lean_isPrivateName(v_id_3069_);
if (v___x_3091_ == 0)
{
lean_dec(v_a_3081_);
lean_dec(v_id_3069_);
goto v___jp_3085_;
}
else
{
uint8_t v___x_3092_; 
v___x_3092_ = lean_unbox(v_a_3081_);
lean_dec(v_a_3081_);
if (v___x_3092_ == 0)
{
lean_dec(v_id_3069_);
goto v___jp_3085_;
}
else
{
lean_object* v___x_3093_; uint8_t v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_del_object(v___x_3083_);
v___x_3093_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3094_ = 0;
v___x_3095_ = l_Lean_MessageData_ofConstName(v_id_3069_, v___x_3094_);
v___x_3096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3093_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3098_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
return v___x_3099_;
}
}
}
v___jp_3085_:
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3086_ = lean_box(0);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v___x_3086_);
v___x_3088_ = v___x_3083_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3110_, uint8_t v_enableLog_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___x_3119_; lean_object* v_env_3120_; lean_object* v_options_3121_; lean_object* v_currNamespace_3122_; lean_object* v_openDecls_3123_; lean_object* v___x_3124_; lean_object* v_env_3125_; lean_object* v_res_3126_; 
v___x_3119_ = lean_st_ref_get(v___y_3117_);
v_env_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc_ref(v_env_3120_);
lean_dec(v___x_3119_);
v_options_3121_ = lean_ctor_get(v___y_3116_, 2);
v_currNamespace_3122_ = lean_ctor_get(v___y_3116_, 6);
v_openDecls_3123_ = lean_ctor_get(v___y_3116_, 7);
v___x_3124_ = lean_st_ref_get(v___y_3117_);
v_env_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc_ref(v_env_3125_);
lean_dec(v___x_3124_);
lean_inc(v_openDecls_3123_);
lean_inc(v_currNamespace_3122_);
v_res_3126_ = l_Lean_ResolveName_resolveGlobalName(v_env_3120_, v_options_3121_, v_currNamespace_3122_, v_openDecls_3123_, v_id_3110_);
if (v_enableLog_3111_ == 0)
{
lean_object* v___x_3127_; 
lean_dec_ref(v_env_3125_);
v___x_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3127_, 0, v_res_3126_);
return v___x_3127_;
}
else
{
uint8_t v_isExporting_3128_; 
v_isExporting_3128_ = lean_ctor_get_uint8(v_env_3125_, sizeof(void*)*8);
lean_dec_ref(v_env_3125_);
if (v_isExporting_3128_ == 0)
{
lean_object* v___x_3129_; 
v___x_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3129_, 0, v_res_3126_);
return v___x_3129_;
}
else
{
lean_object* v___x_3130_; 
v___x_3130_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3126_);
if (lean_obj_tag(v___x_3130_) == 1)
{
lean_object* v_val_3131_; lean_object* v_fst_3132_; lean_object* v___x_3133_; 
v_val_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_val_3131_);
lean_dec_ref(v___x_3130_);
v_fst_3132_ = lean_ctor_get(v_val_3131_, 0);
lean_inc(v_fst_3132_);
lean_dec(v_val_3131_);
v___x_3133_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3132_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v___x_3133_, 0);
lean_dec(v_unused_3141_);
v___x_3135_ = v___x_3133_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_dec(v___x_3133_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v_res_3126_);
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_res_3126_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_dec(v_res_3126_);
v_a_3142_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3133_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3133_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_object* v___x_3150_; 
lean_dec(v___x_3130_);
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v_res_3126_);
return v___x_3150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3151_, lean_object* v_enableLog_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
uint8_t v_enableLog_boxed_3160_; lean_object* v_res_3161_; 
v_enableLog_boxed_3160_ = lean_unbox(v_enableLog_3152_);
v_res_3161_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3151_, v_enableLog_boxed_3160_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3162_, lean_object* v_a_3163_){
_start:
{
if (lean_obj_tag(v_a_3162_) == 0)
{
lean_object* v___x_3164_; 
v___x_3164_ = l_List_reverse___redArg(v_a_3163_);
return v___x_3164_;
}
else
{
lean_object* v_head_3165_; lean_object* v_tail_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3177_; 
v_head_3165_ = lean_ctor_get(v_a_3162_, 0);
v_tail_3166_ = lean_ctor_get(v_a_3162_, 1);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_a_3162_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3168_ = v_a_3162_;
v_isShared_3169_ = v_isSharedCheck_3177_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_tail_3166_);
lean_inc(v_head_3165_);
lean_dec(v_a_3162_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3177_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v_snd_3170_; uint8_t v___x_3171_; 
v_snd_3170_ = lean_ctor_get(v_head_3165_, 1);
v___x_3171_ = l_List_isEmpty___redArg(v_snd_3170_);
if (v___x_3171_ == 0)
{
lean_del_object(v___x_3168_);
lean_dec(v_head_3165_);
v_a_3162_ = v_tail_3166_;
goto _start;
}
else
{
lean_object* v___x_3174_; 
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 1, v_a_3163_);
v___x_3174_ = v___x_3168_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_head_3165_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v_a_3163_);
v___x_3174_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
v_a_3162_ = v_tail_3166_;
v_a_3163_ = v___x_3174_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3178_, lean_object* v_findLocalDecl_x3f_3179_, lean_object* v_n_3180_, lean_object* v_projs_3181_, uint8_t v_globalDeclFound_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v___y_3191_; lean_object* v___y_3192_; uint8_t v_globalDeclFoundNext_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v_imported_3202_; lean_object* v_ctx_3203_; lean_object* v_scopes_3204_; lean_object* v_givenNameView_3205_; uint8_t v___y_3207_; 
v_imported_3202_ = lean_ctor_get(v_view_3178_, 1);
v_ctx_3203_ = lean_ctor_get(v_view_3178_, 2);
v_scopes_3204_ = lean_ctor_get(v_view_3178_, 3);
lean_inc(v_scopes_3204_);
lean_inc(v_ctx_3203_);
lean_inc(v_imported_3202_);
lean_inc(v_n_3180_);
v_givenNameView_3205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3205_, 0, v_n_3180_);
lean_ctor_set(v_givenNameView_3205_, 1, v_imported_3202_);
lean_ctor_set(v_givenNameView_3205_, 2, v_ctx_3203_);
lean_ctor_set(v_givenNameView_3205_, 3, v_scopes_3204_);
if (v_globalDeclFound_3182_ == 0)
{
v___y_3207_ = v_globalDeclFound_3182_;
goto v___jp_3206_;
}
else
{
uint8_t v___x_3242_; 
v___x_3242_ = l_List_isEmpty___redArg(v_projs_3181_);
if (v___x_3242_ == 0)
{
v___y_3207_ = v_globalDeclFound_3182_;
goto v___jp_3206_;
}
else
{
uint8_t v___x_3243_; 
v___x_3243_ = 0;
v___y_3207_ = v___x_3243_;
goto v___jp_3206_;
}
}
v___jp_3190_:
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___y_3191_);
lean_ctor_set(v___x_3200_, 1, v_projs_3181_);
v_n_3180_ = v___y_3192_;
v_projs_3181_ = v___x_3200_;
v_globalDeclFound_3182_ = v_globalDeclFoundNext_3193_;
v___y_3183_ = v___y_3194_;
v___y_3184_ = v___y_3195_;
v___y_3185_ = v___y_3196_;
v___y_3186_ = v___y_3197_;
v___y_3187_ = v___y_3198_;
v___y_3188_ = v___y_3199_;
goto _start;
}
v___jp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = lean_box(v___y_3207_);
lean_inc_ref(v_findLocalDecl_x3f_3179_);
lean_inc_ref(v_givenNameView_3205_);
v___x_3209_ = lean_apply_2(v_findLocalDecl_x3f_3179_, v_givenNameView_3205_, v___x_3208_);
if (lean_obj_tag(v___x_3209_) == 0)
{
if (lean_obj_tag(v_n_3180_) == 1)
{
if (v_globalDeclFound_3182_ == 0)
{
lean_object* v_pre_3210_; lean_object* v_str_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v_pre_3210_ = lean_ctor_get(v_n_3180_, 0);
lean_inc(v_pre_3210_);
v_str_3211_ = lean_ctor_get(v_n_3180_, 1);
lean_inc_ref(v_str_3211_);
lean_dec_ref(v_n_3180_);
v___x_3212_ = l_Lean_MacroScopesView_review(v_givenNameView_3205_);
v___x_3213_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3212_, v_globalDeclFound_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3215_; lean_object* v_r_3216_; uint8_t v___x_3217_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref(v___x_3213_);
v___x_3215_ = lean_box(0);
v_r_3216_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3214_, v___x_3215_);
v___x_3217_ = l_List_isEmpty___redArg(v_r_3216_);
lean_dec(v_r_3216_);
if (v___x_3217_ == 0)
{
uint8_t v_globalDeclFoundNext_3218_; 
v_globalDeclFoundNext_3218_ = 1;
v___y_3191_ = v_str_3211_;
v___y_3192_ = v_pre_3210_;
v_globalDeclFoundNext_3193_ = v_globalDeclFoundNext_3218_;
v___y_3194_ = v___y_3183_;
v___y_3195_ = v___y_3184_;
v___y_3196_ = v___y_3185_;
v___y_3197_ = v___y_3186_;
v___y_3198_ = v___y_3187_;
v___y_3199_ = v___y_3188_;
goto v___jp_3190_;
}
else
{
v___y_3191_ = v_str_3211_;
v___y_3192_ = v_pre_3210_;
v_globalDeclFoundNext_3193_ = v_globalDeclFound_3182_;
v___y_3194_ = v___y_3183_;
v___y_3195_ = v___y_3184_;
v___y_3196_ = v___y_3185_;
v___y_3197_ = v___y_3186_;
v___y_3198_ = v___y_3187_;
v___y_3199_ = v___y_3188_;
goto v___jp_3190_;
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec_ref(v_str_3211_);
lean_dec(v_pre_3210_);
lean_dec(v_projs_3181_);
lean_dec_ref(v_findLocalDecl_x3f_3179_);
v_a_3219_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3213_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3213_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v_pre_3227_; lean_object* v_str_3228_; 
lean_dec_ref(v_givenNameView_3205_);
v_pre_3227_ = lean_ctor_get(v_n_3180_, 0);
lean_inc(v_pre_3227_);
v_str_3228_ = lean_ctor_get(v_n_3180_, 1);
lean_inc_ref(v_str_3228_);
lean_dec_ref(v_n_3180_);
v___y_3191_ = v_str_3228_;
v___y_3192_ = v_pre_3227_;
v_globalDeclFoundNext_3193_ = v_globalDeclFound_3182_;
v___y_3194_ = v___y_3183_;
v___y_3195_ = v___y_3184_;
v___y_3196_ = v___y_3185_;
v___y_3197_ = v___y_3186_;
v___y_3198_ = v___y_3187_;
v___y_3199_ = v___y_3188_;
goto v___jp_3190_;
}
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
lean_dec_ref(v_givenNameView_3205_);
lean_dec(v_projs_3181_);
lean_dec(v_n_3180_);
lean_dec_ref(v_findLocalDecl_x3f_3179_);
v___x_3229_ = lean_box(0);
v___x_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
return v___x_3230_;
}
}
else
{
lean_object* v_val_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v_givenNameView_3205_);
lean_dec(v_n_3180_);
lean_dec_ref(v_findLocalDecl_x3f_3179_);
v_val_3231_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3233_ = v___x_3209_;
v_isShared_3234_ = v_isSharedCheck_3241_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_val_3231_);
lean_dec(v___x_3209_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3241_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3235_ = l_Lean_LocalDecl_toExpr(v_val_3231_);
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
lean_ctor_set(v___x_3236_, 1, v_projs_3181_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v___x_3236_);
v___x_3238_ = v___x_3233_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
return v___x_3239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3244_, lean_object* v_findLocalDecl_x3f_3245_, lean_object* v_n_3246_, lean_object* v_projs_3247_, lean_object* v_globalDeclFound_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
uint8_t v_globalDeclFound_boxed_3256_; lean_object* v_res_3257_; 
v_globalDeclFound_boxed_3256_ = lean_unbox(v_globalDeclFound_3248_);
v_res_3257_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3244_, v_findLocalDecl_x3f_3245_, v_n_3246_, v_projs_3247_, v_globalDeclFound_boxed_3256_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec_ref(v_view_3244_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3258_, lean_object* v_givenName_3259_, lean_object* v_as_3260_, lean_object* v_i_3261_){
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
lean_object* v_one_3265_; lean_object* v_n_3266_; lean_object* v___y_3268_; lean_object* v___x_3270_; 
v_one_3265_ = lean_unsigned_to_nat(1u);
v_n_3266_ = lean_nat_sub(v_i_3261_, v_one_3265_);
lean_dec(v_i_3261_);
v___x_3270_ = lean_array_fget_borrowed(v_as_3260_, v_n_3266_);
if (lean_obj_tag(v___x_3270_) == 0)
{
v___y_3268_ = v___x_3270_;
goto v___jp_3267_;
}
else
{
lean_object* v_val_3271_; uint8_t v___x_3272_; 
v_val_3271_ = lean_ctor_get(v___x_3270_, 0);
v___x_3272_ = l_Lean_LocalDecl_isAuxDecl(v_val_3271_);
if (v___x_3272_ == 0)
{
v___y_3268_ = v_localDecl_x3f_3258_;
goto v___jp_3267_;
}
else
{
lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = l_Lean_LocalDecl_userName(v_val_3271_);
v___x_3274_ = lean_name_eq(v___x_3273_, v_givenName_3259_);
lean_dec(v___x_3273_);
if (v___x_3274_ == 0)
{
v_i_3261_ = v_n_3266_;
goto _start;
}
else
{
v___y_3268_ = v___x_3270_;
goto v___jp_3267_;
}
}
}
v___jp_3267_:
{
if (lean_obj_tag(v___y_3268_) == 0)
{
v_i_3261_ = v_n_3266_;
goto _start;
}
else
{
lean_dec(v_n_3266_);
lean_inc_ref(v___y_3268_);
return v___y_3268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3276_, lean_object* v_givenName_3277_, lean_object* v_as_3278_, lean_object* v_i_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3276_, v_givenName_3277_, v_as_3278_, v_i_3279_);
lean_dec_ref(v_as_3278_);
lean_dec(v_givenName_3277_);
lean_dec(v_localDecl_x3f_3276_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3281_, lean_object* v_givenName_3282_, lean_object* v_as_3283_, lean_object* v_i_3284_){
_start:
{
lean_object* v_zero_3285_; uint8_t v_isZero_3286_; 
v_zero_3285_ = lean_unsigned_to_nat(0u);
v_isZero_3286_ = lean_nat_dec_eq(v_i_3284_, v_zero_3285_);
if (v_isZero_3286_ == 1)
{
lean_object* v___x_3287_; 
lean_dec(v_i_3284_);
v___x_3287_ = lean_box(0);
return v___x_3287_;
}
else
{
lean_object* v_one_3288_; lean_object* v_n_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_one_3288_ = lean_unsigned_to_nat(1u);
v_n_3289_ = lean_nat_sub(v_i_3284_, v_one_3288_);
lean_dec(v_i_3284_);
v___x_3290_ = lean_array_fget_borrowed(v_as_3283_, v_n_3289_);
v___x_3291_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3281_, v_givenName_3282_, v___x_3290_);
if (lean_obj_tag(v___x_3291_) == 0)
{
v_i_3284_ = v_n_3289_;
goto _start;
}
else
{
lean_dec(v_n_3289_);
return v___x_3291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3293_, lean_object* v_givenName_3294_, lean_object* v_x_3295_){
_start:
{
if (lean_obj_tag(v_x_3295_) == 0)
{
lean_object* v_cs_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_cs_3296_ = lean_ctor_get(v_x_3295_, 0);
v___x_3297_ = lean_array_get_size(v_cs_3296_);
v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3293_, v_givenName_3294_, v_cs_3296_, v___x_3297_);
return v___x_3298_;
}
else
{
lean_object* v_vs_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v_vs_3299_ = lean_ctor_get(v_x_3295_, 0);
v___x_3300_ = lean_array_get_size(v_vs_3299_);
v___x_3301_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3293_, v_givenName_3294_, v_vs_3299_, v___x_3300_);
return v___x_3301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3302_, lean_object* v_givenName_3303_, lean_object* v_x_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3302_, v_givenName_3303_, v_x_3304_);
lean_dec_ref(v_x_3304_);
lean_dec(v_givenName_3303_);
lean_dec(v_localDecl_x3f_3302_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3306_, lean_object* v_givenName_3307_, lean_object* v_as_3308_, lean_object* v_i_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3306_, v_givenName_3307_, v_as_3308_, v_i_3309_);
lean_dec_ref(v_as_3308_);
lean_dec(v_givenName_3307_);
lean_dec(v_localDecl_x3f_3306_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3311_, lean_object* v_givenName_3312_, lean_object* v_t_3313_){
_start:
{
lean_object* v_root_3314_; lean_object* v_tail_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_root_3314_ = lean_ctor_get(v_t_3313_, 0);
v_tail_3315_ = lean_ctor_get(v_t_3313_, 1);
v___x_3316_ = lean_array_get_size(v_tail_3315_);
v___x_3317_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3311_, v_givenName_3312_, v_tail_3315_, v___x_3316_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3311_, v_givenName_3312_, v_root_3314_);
return v___x_3318_;
}
else
{
return v___x_3317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3319_, lean_object* v_givenName_3320_, lean_object* v_t_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3319_, v_givenName_3320_, v_t_3321_);
lean_dec_ref(v_t_3321_);
lean_dec(v_givenName_3320_);
lean_dec(v_localDecl_x3f_3319_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3323_, lean_object* v_k_3324_){
_start:
{
if (lean_obj_tag(v_t_3323_) == 0)
{
lean_object* v_k_3325_; lean_object* v_v_3326_; lean_object* v_l_3327_; lean_object* v_r_3328_; uint8_t v___x_3329_; 
v_k_3325_ = lean_ctor_get(v_t_3323_, 1);
v_v_3326_ = lean_ctor_get(v_t_3323_, 2);
v_l_3327_ = lean_ctor_get(v_t_3323_, 3);
v_r_3328_ = lean_ctor_get(v_t_3323_, 4);
v___x_3329_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3324_, v_k_3325_);
switch(v___x_3329_)
{
case 0:
{
v_t_3323_ = v_l_3327_;
goto _start;
}
case 1:
{
lean_object* v___x_3331_; 
lean_inc(v_v_3326_);
v___x_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3331_, 0, v_v_3326_);
return v___x_3331_;
}
default: 
{
v_t_3323_ = v_r_3328_;
goto _start;
}
}
}
else
{
lean_object* v___x_3333_; 
v___x_3333_ = lean_box(0);
return v___x_3333_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3334_, lean_object* v_k_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3334_, v_k_3335_);
lean_dec(v_k_3335_);
lean_dec(v_t_3334_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3337_, lean_object* v_givenName_3338_){
_start:
{
lean_object* v___x_3339_; uint8_t v___x_3340_; 
v___x_3339_ = l_Lean_LocalDecl_userName(v_localDecl_3337_);
v___x_3340_ = lean_name_eq(v___x_3339_, v_givenName_3338_);
lean_dec(v___x_3339_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
lean_dec_ref(v_localDecl_3337_);
v___x_3341_ = lean_box(0);
return v___x_3341_;
}
else
{
lean_object* v___x_3342_; 
v___x_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3342_, 0, v_localDecl_3337_);
return v___x_3342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3343_, lean_object* v_givenName_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3343_, v_givenName_3344_);
lean_dec(v_givenName_3344_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3346_, uint8_t v_skipAuxDecl_3347_, lean_object* v_auxDeclToFullName_3348_, lean_object* v___x_3349_, lean_object* v_givenNameView_3350_, lean_object* v_as_3351_, lean_object* v_i_3352_){
_start:
{
lean_object* v_zero_3353_; uint8_t v_isZero_3354_; 
v_zero_3353_ = lean_unsigned_to_nat(0u);
v_isZero_3354_ = lean_nat_dec_eq(v_i_3352_, v_zero_3353_);
if (v_isZero_3354_ == 1)
{
lean_object* v___x_3355_; 
lean_dec(v_i_3352_);
lean_dec_ref(v_givenNameView_3350_);
lean_dec(v___x_3349_);
v___x_3355_ = lean_box(0);
return v___x_3355_;
}
else
{
lean_object* v_one_3356_; lean_object* v_n_3357_; lean_object* v___y_3359_; lean_object* v___x_3361_; 
v_one_3356_ = lean_unsigned_to_nat(1u);
v_n_3357_ = lean_nat_sub(v_i_3352_, v_one_3356_);
lean_dec(v_i_3352_);
v___x_3361_ = lean_array_fget_borrowed(v_as_3351_, v_n_3357_);
if (lean_obj_tag(v___x_3361_) == 0)
{
v___y_3359_ = v___x_3361_;
goto v___jp_3358_;
}
else
{
lean_object* v_val_3362_; uint8_t v___x_3363_; 
v_val_3362_ = lean_ctor_get(v___x_3361_, 0);
v___x_3363_ = l_Lean_LocalDecl_isAuxDecl(v_val_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
lean_inc(v_val_3362_);
v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3362_, v_givenName_3346_);
v___y_3359_ = v___x_3364_;
goto v___jp_3358_;
}
else
{
if (v_skipAuxDecl_3347_ == 0)
{
if (v___x_3363_ == 0)
{
v_i_3352_ = v_n_3357_;
goto _start;
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = l_Lean_LocalDecl_fvarId(v_val_3362_);
v___x_3367_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3348_, v___x_3366_);
lean_dec(v___x_3366_);
if (lean_obj_tag(v___x_3367_) == 1)
{
lean_object* v_val_3368_; lean_object* v_fullDeclView_3369_; lean_object* v___y_3371_; lean_object* v_name_3392_; lean_object* v___x_3393_; 
v_val_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_val_3368_);
lean_dec_ref(v___x_3367_);
v_fullDeclView_3369_ = l_Lean_extractMacroScopes(v_val_3368_);
v_name_3392_ = lean_ctor_get(v_fullDeclView_3369_, 0);
lean_inc_n(v_name_3392_, 2);
v___x_3393_ = lean_private_to_user_name(v_name_3392_);
if (lean_obj_tag(v___x_3393_) == 0)
{
v___y_3371_ = v_name_3392_;
goto v___jp_3370_;
}
else
{
lean_object* v_val_3394_; 
lean_dec(v_name_3392_);
v_val_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_val_3394_);
lean_dec_ref(v___x_3393_);
v___y_3371_ = v_val_3394_;
goto v___jp_3370_;
}
v___jp_3370_:
{
lean_object* v_imported_3372_; lean_object* v_ctx_3373_; lean_object* v_scopes_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3390_; 
v_imported_3372_ = lean_ctor_get(v_fullDeclView_3369_, 1);
v_ctx_3373_ = lean_ctor_get(v_fullDeclView_3369_, 2);
v_scopes_3374_ = lean_ctor_get(v_fullDeclView_3369_, 3);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_fullDeclView_3369_);
if (v_isSharedCheck_3390_ == 0)
{
lean_object* v_unused_3391_; 
v_unused_3391_ = lean_ctor_get(v_fullDeclView_3369_, 0);
lean_dec(v_unused_3391_);
v___x_3376_ = v_fullDeclView_3369_;
v_isShared_3377_ = v_isSharedCheck_3390_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_scopes_3374_);
lean_inc(v_ctx_3373_);
lean_inc(v_imported_3372_);
lean_dec(v_fullDeclView_3369_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3390_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v_fullDeclView_3379_; 
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v___y_3371_);
v_fullDeclView_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___y_3371_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_imported_3372_);
lean_ctor_set(v_reuseFailAlloc_3389_, 2, v_ctx_3373_);
lean_ctor_set(v_reuseFailAlloc_3389_, 3, v_scopes_3374_);
v_fullDeclView_3379_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v_fullDeclName_3380_; uint8_t v___x_3381_; 
lean_inc_ref(v_fullDeclView_3379_);
v_fullDeclName_3380_ = l_Lean_MacroScopesView_review(v_fullDeclView_3379_);
v___x_3381_ = l_Lean_Name_isPrefixOf(v___x_3349_, v_fullDeclName_3380_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; 
lean_dec_ref(v_fullDeclView_3379_);
lean_inc(v___x_3349_);
lean_inc_ref(v_givenNameView_3350_);
lean_inc(v_val_3362_);
v___x_3382_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3362_, v_givenNameView_3350_, v_fullDeclName_3380_, v___x_3349_);
lean_dec(v_fullDeclName_3380_);
v___y_3359_ = v___x_3382_;
goto v___jp_3358_;
}
else
{
lean_object* v___x_3383_; lean_object* v_localDeclNameView_3384_; uint8_t v___x_3385_; 
lean_dec(v_fullDeclName_3380_);
v___x_3383_ = l_Lean_LocalDecl_userName(v_val_3362_);
v_localDeclNameView_3384_ = l_Lean_extractMacroScopes(v___x_3383_);
v___x_3385_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3384_, v_givenNameView_3350_);
lean_dec_ref(v_localDeclNameView_3384_);
if (v___x_3385_ == 0)
{
lean_dec_ref(v_fullDeclView_3379_);
v_i_3352_ = v_n_3357_;
goto _start;
}
else
{
uint8_t v___x_3387_; 
v___x_3387_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3350_, v_fullDeclView_3379_);
lean_dec_ref(v_fullDeclView_3379_);
if (v___x_3387_ == 0)
{
v_i_3352_ = v_n_3357_;
goto _start;
}
else
{
lean_inc_ref(v___x_3361_);
v___y_3359_ = v___x_3361_;
goto v___jp_3358_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3395_; 
lean_dec(v___x_3367_);
lean_inc(v_val_3362_);
v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3362_, v_givenName_3346_);
v___y_3359_ = v___x_3395_;
goto v___jp_3358_;
}
}
}
else
{
v_i_3352_ = v_n_3357_;
goto _start;
}
}
}
v___jp_3358_:
{
if (lean_obj_tag(v___y_3359_) == 0)
{
v_i_3352_ = v_n_3357_;
goto _start;
}
else
{
lean_dec(v_n_3357_);
lean_dec_ref(v_givenNameView_3350_);
lean_dec(v___x_3349_);
return v___y_3359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3397_, lean_object* v_skipAuxDecl_3398_, lean_object* v_auxDeclToFullName_3399_, lean_object* v___x_3400_, lean_object* v_givenNameView_3401_, lean_object* v_as_3402_, lean_object* v_i_3403_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3404_; lean_object* v_res_3405_; 
v_skipAuxDecl_boxed_3404_ = lean_unbox(v_skipAuxDecl_3398_);
v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3397_, v_skipAuxDecl_boxed_3404_, v_auxDeclToFullName_3399_, v___x_3400_, v_givenNameView_3401_, v_as_3402_, v_i_3403_);
lean_dec_ref(v_as_3402_);
lean_dec(v_auxDeclToFullName_3399_);
lean_dec(v_givenName_3397_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3406_, uint8_t v_skipAuxDecl_3407_, lean_object* v_auxDeclToFullName_3408_, lean_object* v___x_3409_, lean_object* v_givenNameView_3410_, lean_object* v_as_3411_, lean_object* v_i_3412_){
_start:
{
lean_object* v_zero_3413_; uint8_t v_isZero_3414_; 
v_zero_3413_ = lean_unsigned_to_nat(0u);
v_isZero_3414_ = lean_nat_dec_eq(v_i_3412_, v_zero_3413_);
if (v_isZero_3414_ == 1)
{
lean_object* v___x_3415_; 
lean_dec(v_i_3412_);
lean_dec_ref(v_givenNameView_3410_);
lean_dec(v___x_3409_);
v___x_3415_ = lean_box(0);
return v___x_3415_;
}
else
{
lean_object* v_one_3416_; lean_object* v_n_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v_one_3416_ = lean_unsigned_to_nat(1u);
v_n_3417_ = lean_nat_sub(v_i_3412_, v_one_3416_);
lean_dec(v_i_3412_);
v___x_3418_ = lean_array_fget_borrowed(v_as_3411_, v_n_3417_);
lean_inc_ref(v_givenNameView_3410_);
lean_inc(v___x_3409_);
v___x_3419_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3406_, v_skipAuxDecl_3407_, v_auxDeclToFullName_3408_, v___x_3409_, v_givenNameView_3410_, v___x_3418_);
if (lean_obj_tag(v___x_3419_) == 0)
{
v_i_3412_ = v_n_3417_;
goto _start;
}
else
{
lean_dec(v_n_3417_);
lean_dec_ref(v_givenNameView_3410_);
lean_dec(v___x_3409_);
return v___x_3419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3421_, uint8_t v_skipAuxDecl_3422_, lean_object* v_auxDeclToFullName_3423_, lean_object* v___x_3424_, lean_object* v_givenNameView_3425_, lean_object* v_x_3426_){
_start:
{
if (lean_obj_tag(v_x_3426_) == 0)
{
lean_object* v_cs_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v_cs_3427_ = lean_ctor_get(v_x_3426_, 0);
v___x_3428_ = lean_array_get_size(v_cs_3427_);
v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3421_, v_skipAuxDecl_3422_, v_auxDeclToFullName_3423_, v___x_3424_, v_givenNameView_3425_, v_cs_3427_, v___x_3428_);
return v___x_3429_;
}
else
{
lean_object* v_vs_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v_vs_3430_ = lean_ctor_get(v_x_3426_, 0);
v___x_3431_ = lean_array_get_size(v_vs_3430_);
v___x_3432_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3421_, v_skipAuxDecl_3422_, v_auxDeclToFullName_3423_, v___x_3424_, v_givenNameView_3425_, v_vs_3430_, v___x_3431_);
return v___x_3432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3433_, lean_object* v_skipAuxDecl_3434_, lean_object* v_auxDeclToFullName_3435_, lean_object* v___x_3436_, lean_object* v_givenNameView_3437_, lean_object* v_x_3438_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3439_; lean_object* v_res_3440_; 
v_skipAuxDecl_boxed_3439_ = lean_unbox(v_skipAuxDecl_3434_);
v_res_3440_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3433_, v_skipAuxDecl_boxed_3439_, v_auxDeclToFullName_3435_, v___x_3436_, v_givenNameView_3437_, v_x_3438_);
lean_dec_ref(v_x_3438_);
lean_dec(v_auxDeclToFullName_3435_);
lean_dec(v_givenName_3433_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3441_, lean_object* v_skipAuxDecl_3442_, lean_object* v_auxDeclToFullName_3443_, lean_object* v___x_3444_, lean_object* v_givenNameView_3445_, lean_object* v_as_3446_, lean_object* v_i_3447_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3448_; lean_object* v_res_3449_; 
v_skipAuxDecl_boxed_3448_ = lean_unbox(v_skipAuxDecl_3442_);
v_res_3449_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3441_, v_skipAuxDecl_boxed_3448_, v_auxDeclToFullName_3443_, v___x_3444_, v_givenNameView_3445_, v_as_3446_, v_i_3447_);
lean_dec_ref(v_as_3446_);
lean_dec(v_auxDeclToFullName_3443_);
lean_dec(v_givenName_3441_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3450_, uint8_t v_skipAuxDecl_3451_, lean_object* v_auxDeclToFullName_3452_, lean_object* v___x_3453_, lean_object* v_givenNameView_3454_, lean_object* v_t_3455_){
_start:
{
lean_object* v_root_3456_; lean_object* v_tail_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v_root_3456_ = lean_ctor_get(v_t_3455_, 0);
v_tail_3457_ = lean_ctor_get(v_t_3455_, 1);
v___x_3458_ = lean_array_get_size(v_tail_3457_);
lean_inc_ref(v_givenNameView_3454_);
lean_inc(v___x_3453_);
v___x_3459_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3450_, v_skipAuxDecl_3451_, v_auxDeclToFullName_3452_, v___x_3453_, v_givenNameView_3454_, v_tail_3457_, v___x_3458_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3450_, v_skipAuxDecl_3451_, v_auxDeclToFullName_3452_, v___x_3453_, v_givenNameView_3454_, v_root_3456_);
return v___x_3460_;
}
else
{
lean_dec_ref(v_givenNameView_3454_);
lean_dec(v___x_3453_);
return v___x_3459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3461_, lean_object* v_skipAuxDecl_3462_, lean_object* v_auxDeclToFullName_3463_, lean_object* v___x_3464_, lean_object* v_givenNameView_3465_, lean_object* v_t_3466_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3467_; lean_object* v_res_3468_; 
v_skipAuxDecl_boxed_3467_ = lean_unbox(v_skipAuxDecl_3462_);
v_res_3468_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3461_, v_skipAuxDecl_boxed_3467_, v_auxDeclToFullName_3463_, v___x_3464_, v_givenNameView_3465_, v_t_3466_);
lean_dec_ref(v_t_3466_);
lean_dec(v_auxDeclToFullName_3463_);
lean_dec(v_givenName_3461_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3469_, lean_object* v_currNamespace_3470_, lean_object* v_decls_3471_, lean_object* v_givenNameView_3472_, uint8_t v_skipAuxDecl_3473_){
_start:
{
lean_object* v_givenName_3474_; lean_object* v_localDecl_x3f_3475_; 
lean_inc_ref(v_givenNameView_3472_);
v_givenName_3474_ = l_Lean_MacroScopesView_review(v_givenNameView_3472_);
v_localDecl_x3f_3475_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3474_, v_skipAuxDecl_3473_, v_auxDeclToFullName_3469_, v_currNamespace_3470_, v_givenNameView_3472_, v_decls_3471_);
if (lean_obj_tag(v_localDecl_x3f_3475_) == 0)
{
if (v_skipAuxDecl_3473_ == 0)
{
lean_object* v___x_3476_; 
v___x_3476_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3475_, v_givenName_3474_, v_decls_3471_);
lean_dec(v_givenName_3474_);
return v___x_3476_;
}
else
{
lean_dec(v_givenName_3474_);
return v_localDecl_x3f_3475_;
}
}
else
{
lean_dec(v_givenName_3474_);
return v_localDecl_x3f_3475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3477_, lean_object* v_currNamespace_3478_, lean_object* v_decls_3479_, lean_object* v_givenNameView_3480_, lean_object* v_skipAuxDecl_3481_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3482_; lean_object* v_res_3483_; 
v_skipAuxDecl_boxed_3482_ = lean_unbox(v_skipAuxDecl_3481_);
v_res_3483_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3477_, v_currNamespace_3478_, v_decls_3479_, v_givenNameView_3480_, v_skipAuxDecl_boxed_3482_);
lean_dec_ref(v_decls_3479_);
lean_dec(v_auxDeclToFullName_3477_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v_lctx_3492_; lean_object* v_decls_3493_; lean_object* v_auxDeclToFullName_3494_; lean_object* v_currNamespace_3495_; lean_object* v_view_3496_; lean_object* v_name_3497_; lean_object* v_findLocalDecl_x3f_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; lean_object* v___x_3501_; 
v_lctx_3492_ = lean_ctor_get(v___y_3487_, 2);
v_decls_3493_ = lean_ctor_get(v_lctx_3492_, 1);
v_auxDeclToFullName_3494_ = lean_ctor_get(v_lctx_3492_, 2);
v_currNamespace_3495_ = lean_ctor_get(v___y_3489_, 6);
v_view_3496_ = l_Lean_extractMacroScopes(v_n_3484_);
v_name_3497_ = lean_ctor_get(v_view_3496_, 0);
lean_inc(v_name_3497_);
lean_inc_ref(v_decls_3493_);
lean_inc(v_currNamespace_3495_);
lean_inc(v_auxDeclToFullName_3494_);
v_findLocalDecl_x3f_3498_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3498_, 0, v_auxDeclToFullName_3494_);
lean_closure_set(v_findLocalDecl_x3f_3498_, 1, v_currNamespace_3495_);
lean_closure_set(v_findLocalDecl_x3f_3498_, 2, v_decls_3493_);
v___x_3499_ = lean_box(0);
v___x_3500_ = 0;
v___x_3501_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3496_, v_findLocalDecl_x3f_3498_, v_name_3497_, v___x_3499_, v___x_3500_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec_ref(v_view_3496_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3511_, lean_object* v_b_3512_){
_start:
{
if (lean_obj_tag(v_as_x27_3511_) == 0)
{
lean_object* v___x_3514_; 
v___x_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3514_, 0, v_b_3512_);
return v___x_3514_;
}
else
{
lean_object* v_head_3515_; lean_object* v_tail_3516_; lean_object* v_config_3517_; lean_object* v_extensions_3518_; lean_object* v_extra_3519_; lean_object* v_extraInj_3520_; lean_object* v_extraFacts_3521_; lean_object* v_symPrios_3522_; lean_object* v_norm_3523_; lean_object* v_normProcs_3524_; lean_object* v_anchorRefs_x3f_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3534_; 
v_head_3515_ = lean_ctor_get(v_as_x27_3511_, 0);
v_tail_3516_ = lean_ctor_get(v_as_x27_3511_, 1);
v_config_3517_ = lean_ctor_get(v_b_3512_, 0);
v_extensions_3518_ = lean_ctor_get(v_b_3512_, 1);
v_extra_3519_ = lean_ctor_get(v_b_3512_, 2);
v_extraInj_3520_ = lean_ctor_get(v_b_3512_, 3);
v_extraFacts_3521_ = lean_ctor_get(v_b_3512_, 4);
v_symPrios_3522_ = lean_ctor_get(v_b_3512_, 5);
v_norm_3523_ = lean_ctor_get(v_b_3512_, 6);
v_normProcs_3524_ = lean_ctor_get(v_b_3512_, 7);
v_anchorRefs_x3f_3525_ = lean_ctor_get(v_b_3512_, 8);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_b_3512_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3527_ = v_b_3512_;
v_isShared_3528_ = v_isSharedCheck_3534_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_anchorRefs_x3f_3525_);
lean_inc(v_normProcs_3524_);
lean_inc(v_norm_3523_);
lean_inc(v_symPrios_3522_);
lean_inc(v_extraFacts_3521_);
lean_inc(v_extraInj_3520_);
lean_inc(v_extra_3519_);
lean_inc(v_extensions_3518_);
lean_inc(v_config_3517_);
lean_dec(v_b_3512_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3534_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
lean_inc(v_head_3515_);
v___x_3529_ = l_Lean_PersistentArray_push___redArg(v_extra_3519_, v_head_3515_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 2, v___x_3529_);
v___x_3531_ = v___x_3527_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_config_3517_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_extensions_3518_);
lean_ctor_set(v_reuseFailAlloc_3533_, 2, v___x_3529_);
lean_ctor_set(v_reuseFailAlloc_3533_, 3, v_extraInj_3520_);
lean_ctor_set(v_reuseFailAlloc_3533_, 4, v_extraFacts_3521_);
lean_ctor_set(v_reuseFailAlloc_3533_, 5, v_symPrios_3522_);
lean_ctor_set(v_reuseFailAlloc_3533_, 6, v_norm_3523_);
lean_ctor_set(v_reuseFailAlloc_3533_, 7, v_normProcs_3524_);
lean_ctor_set(v_reuseFailAlloc_3533_, 8, v_anchorRefs_x3f_3525_);
v___x_3531_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
v_as_x27_3511_ = v_tail_3516_;
v_b_3512_ = v___x_3531_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3535_, lean_object* v_b_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3535_, v_b_3536_);
lean_dec(v_as_x27_3535_);
return v_res_3538_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3541_ = l_Lean_stringToMessageData(v___x_3540_);
return v___x_3541_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3544_ = l_Lean_stringToMessageData(v___x_3543_);
return v___x_3544_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3547_ = l_Lean_stringToMessageData(v___x_3546_);
return v___x_3547_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3550_ = l_Lean_stringToMessageData(v___x_3549_);
return v___x_3550_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3553_ = l_Lean_stringToMessageData(v___x_3552_);
return v___x_3553_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3556_ = l_Lean_stringToMessageData(v___x_3555_);
return v___x_3556_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3559_ = l_Lean_stringToMessageData(v___x_3558_);
return v___x_3559_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3562_ = l_Lean_stringToMessageData(v___x_3561_);
return v___x_3562_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3565_ = l_Lean_stringToMessageData(v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3568_ = l_Lean_stringToMessageData(v___x_3567_);
return v___x_3568_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3571_ = l_Lean_stringToMessageData(v___x_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3572_, lean_object* v_p_3573_, lean_object* v_mod_x3f_3574_, lean_object* v_id_3575_, uint8_t v_minIndexable_3576_, uint8_t v_only_3577_, uint8_t v_incremental_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3699_; uint8_t v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v_a_3761_; lean_object* v___y_3986_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = lean_box(0);
lean_inc(v_id_3575_);
v___x_3998_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3575_, v___x_3997_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref(v___x_3998_);
v_a_3761_ = v_a_3999_;
goto v___jp_3760_;
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4074_; 
v_a_4000_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4002_ = v___x_3998_;
v_isShared_4003_ = v_isSharedCheck_4074_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3998_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4074_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
uint8_t v___y_4005_; uint8_t v___x_4072_; 
v___x_4072_ = l_Lean_Exception_isInterrupt(v_a_4000_);
if (v___x_4072_ == 0)
{
uint8_t v___x_4073_; 
lean_inc(v_a_4000_);
v___x_4073_ = l_Lean_Exception_isRuntime(v_a_4000_);
v___y_4005_ = v___x_4073_;
goto v___jp_4004_;
}
else
{
v___y_4005_ = v___x_4072_;
goto v___jp_4004_;
}
v___jp_4004_:
{
if (v___y_4005_ == 0)
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_del_object(v___x_4002_);
v___x_4006_ = l_Lean_TSyntax_getId(v_id_3575_);
lean_inc(v___x_4006_);
v___x_4007_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4006_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref(v___x_4007_);
if (lean_obj_tag(v_a_4008_) == 0)
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_4006_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4038_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4038_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4038_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
if (lean_obj_tag(v_a_4010_) == 1)
{
lean_del_object(v___x_4012_);
lean_dec(v_a_4000_);
if (lean_obj_tag(v_mod_x3f_3574_) == 1)
{
lean_object* v_val_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec_ref(v_a_4010_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v_val_4014_ = lean_ctor_get(v_mod_x3f_3574_, 0);
lean_inc(v_val_4014_);
lean_dec_ref(v_mod_x3f_3574_);
v___x_4015_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_4016_ = l_Lean_MessageData_ofName(v___x_4006_);
v___x_4017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4015_);
lean_ctor_set(v___x_4017_, 1, v___x_4016_);
v___x_4018_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4017_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
v___x_4020_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4014_, v___x_4019_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
lean_dec(v_val_4014_);
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_4020_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4020_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
else
{
lean_object* v_val_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
lean_dec(v___x_4006_);
v_val_4029_ = lean_ctor_get(v_a_4010_, 0);
lean_inc(v_val_4029_);
lean_dec_ref(v_a_4010_);
v___x_4030_ = lean_box(0);
lean_inc_ref(v_params_3572_);
v___x_4031_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3572_, v_val_4029_, v___x_4030_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
lean_dec(v_val_4029_);
v___y_3986_ = v___x_4031_;
goto v___jp_3985_;
}
}
else
{
lean_object* v___x_4032_; uint8_t v___x_4033_; 
lean_dec(v_a_4010_);
v___x_4032_ = l_Lean_Name_getPrefix(v___x_4006_);
lean_dec(v___x_4006_);
v___x_4033_ = l_Lean_Name_isAnonymous(v___x_4032_);
lean_dec(v___x_4032_);
if (v___x_4033_ == 0)
{
lean_object* v___x_4034_; 
lean_del_object(v___x_4012_);
lean_dec(v_a_4000_);
v___x_4034_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3572_, v_p_3573_, v_mod_x3f_3574_, v_id_3575_, v_minIndexable_3576_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
return v___x_4034_;
}
else
{
lean_object* v___x_4036_; 
lean_dec(v_id_3575_);
lean_dec(v_mod_x3f_3574_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set_tag(v___x_4012_, 1);
lean_ctor_set(v___x_4012_, 0, v_a_4000_);
v___x_4036_ = v___x_4012_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4000_);
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
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec(v___x_4006_);
lean_dec(v_a_4000_);
lean_dec(v_id_3575_);
lean_dec(v_mod_x3f_3574_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v_a_4039_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4009_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4009_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
else
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec_ref(v_a_4008_);
lean_dec(v___x_4006_);
lean_dec(v_a_4000_);
lean_dec(v_mod_x3f_3574_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v___x_4047_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
lean_inc(v_id_3575_);
v___x_4048_ = l_Lean_MessageData_ofSyntax(v_id_3575_);
v___x_4049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4047_);
lean_ctor_set(v___x_4049_, 1, v___x_4048_);
v___x_4050_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4049_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3575_, v___x_4051_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
lean_dec(v_id_3575_);
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4052_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4052_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
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
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec(v___x_4006_);
lean_dec(v_a_4000_);
lean_dec(v_id_3575_);
lean_dec(v_mod_x3f_3574_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v_a_4061_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4007_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4007_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
else
{
lean_object* v___x_4070_; 
lean_dec(v_id_3575_);
lean_dec(v_mod_x3f_3574_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
if (v_isShared_4003_ == 0)
{
v___x_4070_ = v___x_4002_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4000_);
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
v___jp_3586_:
{
uint8_t v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = 0;
lean_inc(v___y_3587_);
v___x_3595_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3587_, v___x_3594_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref(v___x_3595_);
if (lean_obj_tag(v_a_3596_) == 1)
{
lean_object* v_val_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
lean_dec(v___y_3587_);
v_val_3597_ = lean_ctor_get(v_a_3596_, 0);
lean_inc_n(v_val_3597_, 2);
lean_dec_ref(v_a_3596_);
v___x_3598_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3572_, v_val_3597_, v___x_3594_);
v___x_3599_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3597_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3610_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3602_ = v___x_3599_;
v_isShared_3603_ = v_isSharedCheck_3610_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3599_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3610_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
if (lean_obj_tag(v_a_3600_) == 1)
{
lean_object* v_val_3604_; lean_object* v_ctors_3605_; lean_object* v___x_3606_; 
lean_del_object(v___x_3602_);
v_val_3604_ = lean_ctor_get(v_a_3600_, 0);
lean_inc(v_val_3604_);
lean_dec_ref(v_a_3600_);
v_ctors_3605_ = lean_ctor_get(v_val_3604_, 4);
lean_inc(v_ctors_3605_);
lean_dec(v_val_3604_);
v___x_3606_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3573_, v_id_3575_, v_minIndexable_3576_, v_ctors_3605_, v___x_3598_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
lean_dec(v_ctors_3605_);
lean_dec(v_p_3573_);
return v___x_3606_;
}
else
{
lean_object* v___x_3608_; 
lean_dec(v_a_3600_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 0, v___x_3598_);
v___x_3608_ = v___x_3602_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3598_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref(v___x_3598_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
v_a_3611_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3599_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3599_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
else
{
lean_object* v_fileName_3619_; lean_object* v_fileMap_3620_; lean_object* v_options_3621_; lean_object* v_currRecDepth_3622_; lean_object* v_maxRecDepth_3623_; lean_object* v_ref_3624_; lean_object* v_currNamespace_3625_; lean_object* v_openDecls_3626_; lean_object* v_initHeartbeats_3627_; lean_object* v_maxHeartbeats_3628_; lean_object* v_quotContext_3629_; lean_object* v_currMacroScope_3630_; uint8_t v_diag_3631_; lean_object* v_cancelTk_x3f_3632_; uint8_t v_suppressElabErrors_3633_; lean_object* v_inheritedTraceOptions_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; lean_object* v_ref_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
lean_dec(v_a_3596_);
v_fileName_3619_ = lean_ctor_get(v___y_3592_, 0);
v_fileMap_3620_ = lean_ctor_get(v___y_3592_, 1);
v_options_3621_ = lean_ctor_get(v___y_3592_, 2);
v_currRecDepth_3622_ = lean_ctor_get(v___y_3592_, 3);
v_maxRecDepth_3623_ = lean_ctor_get(v___y_3592_, 4);
v_ref_3624_ = lean_ctor_get(v___y_3592_, 5);
v_currNamespace_3625_ = lean_ctor_get(v___y_3592_, 6);
v_openDecls_3626_ = lean_ctor_get(v___y_3592_, 7);
v_initHeartbeats_3627_ = lean_ctor_get(v___y_3592_, 8);
v_maxHeartbeats_3628_ = lean_ctor_get(v___y_3592_, 9);
v_quotContext_3629_ = lean_ctor_get(v___y_3592_, 10);
v_currMacroScope_3630_ = lean_ctor_get(v___y_3592_, 11);
v_diag_3631_ = lean_ctor_get_uint8(v___y_3592_, sizeof(void*)*14);
v_cancelTk_x3f_3632_ = lean_ctor_get(v___y_3592_, 12);
v_suppressElabErrors_3633_ = lean_ctor_get_uint8(v___y_3592_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3634_ = lean_ctor_get(v___y_3592_, 13);
v___x_3635_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_3636_ = 1;
v_ref_3637_ = l_Lean_replaceRef(v_p_3573_, v_ref_3624_);
lean_dec(v_p_3573_);
lean_inc_ref(v_inheritedTraceOptions_3634_);
lean_inc(v_cancelTk_x3f_3632_);
lean_inc(v_currMacroScope_3630_);
lean_inc(v_quotContext_3629_);
lean_inc(v_maxHeartbeats_3628_);
lean_inc(v_initHeartbeats_3627_);
lean_inc(v_openDecls_3626_);
lean_inc(v_currNamespace_3625_);
lean_inc(v_maxRecDepth_3623_);
lean_inc(v_currRecDepth_3622_);
lean_inc_ref(v_options_3621_);
lean_inc_ref(v_fileMap_3620_);
lean_inc_ref(v_fileName_3619_);
v___x_3638_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3638_, 0, v_fileName_3619_);
lean_ctor_set(v___x_3638_, 1, v_fileMap_3620_);
lean_ctor_set(v___x_3638_, 2, v_options_3621_);
lean_ctor_set(v___x_3638_, 3, v_currRecDepth_3622_);
lean_ctor_set(v___x_3638_, 4, v_maxRecDepth_3623_);
lean_ctor_set(v___x_3638_, 5, v_ref_3637_);
lean_ctor_set(v___x_3638_, 6, v_currNamespace_3625_);
lean_ctor_set(v___x_3638_, 7, v_openDecls_3626_);
lean_ctor_set(v___x_3638_, 8, v_initHeartbeats_3627_);
lean_ctor_set(v___x_3638_, 9, v_maxHeartbeats_3628_);
lean_ctor_set(v___x_3638_, 10, v_quotContext_3629_);
lean_ctor_set(v___x_3638_, 11, v_currMacroScope_3630_);
lean_ctor_set(v___x_3638_, 12, v_cancelTk_x3f_3632_);
lean_ctor_set(v___x_3638_, 13, v_inheritedTraceOptions_3634_);
lean_ctor_set_uint8(v___x_3638_, sizeof(void*)*14, v_diag_3631_);
lean_ctor_set_uint8(v___x_3638_, sizeof(void*)*14 + 1, v_suppressElabErrors_3633_);
v___x_3639_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3572_, v_id_3575_, v___y_3587_, v___x_3635_, v_minIndexable_3576_, v___x_3636_, v___x_3636_, v___y_3590_, v___y_3591_, v___x_3638_, v___y_3593_);
lean_dec_ref(v___x_3638_);
return v___x_3639_;
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec(v___y_3587_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v_a_3640_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3595_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3595_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
v___jp_3648_:
{
lean_object* v___x_3657_; 
v___x_3657_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3576_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
lean_dec_ref(v___x_3657_);
v___x_3658_ = l_Lean_Meta_Grind_grindExt;
v___x_3659_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3658_, v___y_3656_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; uint8_t v___x_3665_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref(v___x_3659_);
lean_inc(v___y_3650_);
v___x_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3661_, 0, v___y_3650_);
v___x_3662_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3660_, v___x_3661_);
lean_dec_ref(v___x_3661_);
lean_dec(v_a_3660_);
v___x_3663_ = lean_box(0);
v___x_3664_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3649_, v___x_3662_, v___x_3663_);
lean_dec(v___y_3649_);
v___x_3665_ = l_List_isEmpty___redArg(v___x_3664_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3666_; 
lean_dec(v___y_3650_);
lean_dec(v_p_3573_);
v___x_3666_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3664_, v_params_3572_);
lean_dec(v___x_3664_);
return v___x_3666_;
}
else
{
lean_object* v___x_3667_; uint8_t v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec(v___x_3664_);
lean_dec_ref(v_params_3572_);
v___x_3667_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3668_ = 0;
v___x_3669_ = l_Lean_MessageData_ofConstName(v___y_3650_, v___x_3668_);
v___x_3670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3667_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
v___x_3671_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3670_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
v___x_3673_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3573_, v___x_3672_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec(v_p_3573_);
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3673_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3673_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v_a_3682_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3659_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3659_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v_a_3690_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3657_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3657_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
v___jp_3698_:
{
lean_object* v___x_3705_; 
v___x_3705_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3576_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_fileName_3706_; lean_object* v_fileMap_3707_; lean_object* v_options_3708_; lean_object* v_currRecDepth_3709_; lean_object* v_maxRecDepth_3710_; lean_object* v_ref_3711_; lean_object* v_currNamespace_3712_; lean_object* v_openDecls_3713_; lean_object* v_initHeartbeats_3714_; lean_object* v_maxHeartbeats_3715_; lean_object* v_quotContext_3716_; lean_object* v_currMacroScope_3717_; uint8_t v_diag_3718_; lean_object* v_cancelTk_x3f_3719_; uint8_t v_suppressElabErrors_3720_; lean_object* v_inheritedTraceOptions_3721_; lean_object* v_ref_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec_ref(v___x_3705_);
v_fileName_3706_ = lean_ctor_get(v___y_3703_, 0);
v_fileMap_3707_ = lean_ctor_get(v___y_3703_, 1);
v_options_3708_ = lean_ctor_get(v___y_3703_, 2);
v_currRecDepth_3709_ = lean_ctor_get(v___y_3703_, 3);
v_maxRecDepth_3710_ = lean_ctor_get(v___y_3703_, 4);
v_ref_3711_ = lean_ctor_get(v___y_3703_, 5);
v_currNamespace_3712_ = lean_ctor_get(v___y_3703_, 6);
v_openDecls_3713_ = lean_ctor_get(v___y_3703_, 7);
v_initHeartbeats_3714_ = lean_ctor_get(v___y_3703_, 8);
v_maxHeartbeats_3715_ = lean_ctor_get(v___y_3703_, 9);
v_quotContext_3716_ = lean_ctor_get(v___y_3703_, 10);
v_currMacroScope_3717_ = lean_ctor_get(v___y_3703_, 11);
v_diag_3718_ = lean_ctor_get_uint8(v___y_3703_, sizeof(void*)*14);
v_cancelTk_x3f_3719_ = lean_ctor_get(v___y_3703_, 12);
v_suppressElabErrors_3720_ = lean_ctor_get_uint8(v___y_3703_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3721_ = lean_ctor_get(v___y_3703_, 13);
v_ref_3722_ = l_Lean_replaceRef(v_p_3573_, v_ref_3711_);
lean_dec(v_p_3573_);
lean_inc_ref(v_inheritedTraceOptions_3721_);
lean_inc(v_cancelTk_x3f_3719_);
lean_inc(v_currMacroScope_3717_);
lean_inc(v_quotContext_3716_);
lean_inc(v_maxHeartbeats_3715_);
lean_inc(v_initHeartbeats_3714_);
lean_inc(v_openDecls_3713_);
lean_inc(v_currNamespace_3712_);
lean_inc(v_maxRecDepth_3710_);
lean_inc(v_currRecDepth_3709_);
lean_inc_ref(v_options_3708_);
lean_inc_ref(v_fileMap_3707_);
lean_inc_ref(v_fileName_3706_);
v___x_3723_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3723_, 0, v_fileName_3706_);
lean_ctor_set(v___x_3723_, 1, v_fileMap_3707_);
lean_ctor_set(v___x_3723_, 2, v_options_3708_);
lean_ctor_set(v___x_3723_, 3, v_currRecDepth_3709_);
lean_ctor_set(v___x_3723_, 4, v_maxRecDepth_3710_);
lean_ctor_set(v___x_3723_, 5, v_ref_3722_);
lean_ctor_set(v___x_3723_, 6, v_currNamespace_3712_);
lean_ctor_set(v___x_3723_, 7, v_openDecls_3713_);
lean_ctor_set(v___x_3723_, 8, v_initHeartbeats_3714_);
lean_ctor_set(v___x_3723_, 9, v_maxHeartbeats_3715_);
lean_ctor_set(v___x_3723_, 10, v_quotContext_3716_);
lean_ctor_set(v___x_3723_, 11, v_currMacroScope_3717_);
lean_ctor_set(v___x_3723_, 12, v_cancelTk_x3f_3719_);
lean_ctor_set(v___x_3723_, 13, v_inheritedTraceOptions_3721_);
lean_ctor_set_uint8(v___x_3723_, sizeof(void*)*14, v_diag_3718_);
lean_ctor_set_uint8(v___x_3723_, sizeof(void*)*14 + 1, v_suppressElabErrors_3720_);
lean_inc(v___y_3699_);
v___x_3724_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3699_, v___y_3700_, v___x_3723_, v___y_3704_);
lean_dec_ref(v___x_3723_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3732_; 
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3732_ == 0)
{
lean_object* v_unused_3733_; 
v_unused_3733_ = lean_ctor_get(v___x_3724_, 0);
lean_dec(v_unused_3733_);
v___x_3726_ = v___x_3724_;
v_isShared_3727_ = v_isSharedCheck_3732_;
goto v_resetjp_3725_;
}
else
{
lean_dec(v___x_3724_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3732_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3728_; lean_object* v___x_3730_; 
v___x_3728_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3572_, v___y_3699_, v___y_3700_);
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 0, v___x_3728_);
v___x_3730_ = v___x_3726_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec(v___y_3699_);
lean_dec_ref(v_params_3572_);
v_a_3734_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3724_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3724_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec(v___y_3699_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v_a_3742_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3705_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3705_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
v___jp_3750_:
{
lean_object* v_ctors_3758_; lean_object* v___x_3759_; 
v_ctors_3758_ = lean_ctor_get(v___y_3751_, 4);
lean_inc(v_ctors_3758_);
lean_dec_ref(v___y_3751_);
v___x_3759_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3573_, v_id_3575_, v_minIndexable_3576_, v_ctors_3758_, v_params_3572_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v_ctors_3758_);
lean_dec(v_p_3573_);
return v___x_3759_;
}
v___jp_3760_:
{
lean_object* v___x_3762_; 
lean_inc(v_a_3761_);
v___x_3762_ = l_Lean_Linter_checkDeprecated(v_a_3761_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_dec_ref(v___x_3762_);
if (lean_obj_tag(v_mod_x3f_3574_) == 1)
{
lean_object* v_val_3763_; lean_object* v___x_3764_; 
v_val_3763_ = lean_ctor_get(v_mod_x3f_3574_, 0);
lean_inc(v_val_3763_);
lean_dec_ref(v_mod_x3f_3574_);
v___x_3764_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_3763_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3968_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3767_ = v___x_3764_;
v_isShared_3768_ = v_isSharedCheck_3968_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3764_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3968_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
switch(lean_obj_tag(v_a_3765_))
{
case 0:
{
lean_object* v_k_3769_; 
lean_del_object(v___x_3767_);
v_k_3769_ = lean_ctor_get(v_a_3765_, 0);
lean_inc(v_k_3769_);
lean_dec_ref(v_a_3765_);
if (lean_obj_tag(v_k_3769_) == 9)
{
lean_dec(v_id_3575_);
if (v_only_3577_ == 0)
{
lean_object* v_fileName_3770_; lean_object* v_fileMap_3771_; lean_object* v_options_3772_; lean_object* v_currRecDepth_3773_; lean_object* v_maxRecDepth_3774_; lean_object* v_ref_3775_; lean_object* v_currNamespace_3776_; lean_object* v_openDecls_3777_; lean_object* v_initHeartbeats_3778_; lean_object* v_maxHeartbeats_3779_; lean_object* v_quotContext_3780_; lean_object* v_currMacroScope_3781_; uint8_t v_diag_3782_; lean_object* v_cancelTk_x3f_3783_; uint8_t v_suppressElabErrors_3784_; lean_object* v_inheritedTraceOptions_3785_; lean_object* v_ref_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v_fileName_3770_ = lean_ctor_get(v_a_3583_, 0);
v_fileMap_3771_ = lean_ctor_get(v_a_3583_, 1);
v_options_3772_ = lean_ctor_get(v_a_3583_, 2);
v_currRecDepth_3773_ = lean_ctor_get(v_a_3583_, 3);
v_maxRecDepth_3774_ = lean_ctor_get(v_a_3583_, 4);
v_ref_3775_ = lean_ctor_get(v_a_3583_, 5);
v_currNamespace_3776_ = lean_ctor_get(v_a_3583_, 6);
v_openDecls_3777_ = lean_ctor_get(v_a_3583_, 7);
v_initHeartbeats_3778_ = lean_ctor_get(v_a_3583_, 8);
v_maxHeartbeats_3779_ = lean_ctor_get(v_a_3583_, 9);
v_quotContext_3780_ = lean_ctor_get(v_a_3583_, 10);
v_currMacroScope_3781_ = lean_ctor_get(v_a_3583_, 11);
v_diag_3782_ = lean_ctor_get_uint8(v_a_3583_, sizeof(void*)*14);
v_cancelTk_x3f_3783_ = lean_ctor_get(v_a_3583_, 12);
v_suppressElabErrors_3784_ = lean_ctor_get_uint8(v_a_3583_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3785_ = lean_ctor_get(v_a_3583_, 13);
v_ref_3786_ = l_Lean_replaceRef(v_p_3573_, v_ref_3775_);
lean_inc_ref(v_inheritedTraceOptions_3785_);
lean_inc(v_cancelTk_x3f_3783_);
lean_inc(v_currMacroScope_3781_);
lean_inc(v_quotContext_3780_);
lean_inc(v_maxHeartbeats_3779_);
lean_inc(v_initHeartbeats_3778_);
lean_inc(v_openDecls_3777_);
lean_inc(v_currNamespace_3776_);
lean_inc(v_maxRecDepth_3774_);
lean_inc(v_currRecDepth_3773_);
lean_inc_ref(v_options_3772_);
lean_inc_ref(v_fileMap_3771_);
lean_inc_ref(v_fileName_3770_);
v___x_3787_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3787_, 0, v_fileName_3770_);
lean_ctor_set(v___x_3787_, 1, v_fileMap_3771_);
lean_ctor_set(v___x_3787_, 2, v_options_3772_);
lean_ctor_set(v___x_3787_, 3, v_currRecDepth_3773_);
lean_ctor_set(v___x_3787_, 4, v_maxRecDepth_3774_);
lean_ctor_set(v___x_3787_, 5, v_ref_3786_);
lean_ctor_set(v___x_3787_, 6, v_currNamespace_3776_);
lean_ctor_set(v___x_3787_, 7, v_openDecls_3777_);
lean_ctor_set(v___x_3787_, 8, v_initHeartbeats_3778_);
lean_ctor_set(v___x_3787_, 9, v_maxHeartbeats_3779_);
lean_ctor_set(v___x_3787_, 10, v_quotContext_3780_);
lean_ctor_set(v___x_3787_, 11, v_currMacroScope_3781_);
lean_ctor_set(v___x_3787_, 12, v_cancelTk_x3f_3783_);
lean_ctor_set(v___x_3787_, 13, v_inheritedTraceOptions_3785_);
lean_ctor_set_uint8(v___x_3787_, sizeof(void*)*14, v_diag_3782_);
lean_ctor_set_uint8(v___x_3787_, sizeof(void*)*14 + 1, v_suppressElabErrors_3784_);
v___x_3788_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_3787_, v_a_3584_);
lean_dec_ref(v___x_3787_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_dec_ref(v___x_3788_);
v___y_3649_ = v_k_3769_;
v___y_3650_ = v_a_3761_;
v___y_3651_ = v_a_3579_;
v___y_3652_ = v_a_3580_;
v___y_3653_ = v_a_3581_;
v___y_3654_ = v_a_3582_;
v___y_3655_ = v_a_3583_;
v___y_3656_ = v_a_3584_;
goto v___jp_3648_;
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec(v_a_3761_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
v___y_3649_ = v_k_3769_;
v___y_3650_ = v_a_3761_;
v___y_3651_ = v_a_3579_;
v___y_3652_ = v_a_3580_;
v___y_3653_ = v_a_3581_;
v___y_3654_ = v_a_3582_;
v___y_3655_ = v_a_3583_;
v___y_3656_ = v_a_3584_;
goto v___jp_3648_;
}
}
else
{
lean_object* v_fileName_3797_; lean_object* v_fileMap_3798_; lean_object* v_options_3799_; lean_object* v_currRecDepth_3800_; lean_object* v_maxRecDepth_3801_; lean_object* v_ref_3802_; lean_object* v_currNamespace_3803_; lean_object* v_openDecls_3804_; lean_object* v_initHeartbeats_3805_; lean_object* v_maxHeartbeats_3806_; lean_object* v_quotContext_3807_; lean_object* v_currMacroScope_3808_; uint8_t v_diag_3809_; lean_object* v_cancelTk_x3f_3810_; uint8_t v_suppressElabErrors_3811_; lean_object* v_inheritedTraceOptions_3812_; uint8_t v___x_3813_; uint8_t v___x_3814_; lean_object* v_ref_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v_fileName_3797_ = lean_ctor_get(v_a_3583_, 0);
v_fileMap_3798_ = lean_ctor_get(v_a_3583_, 1);
v_options_3799_ = lean_ctor_get(v_a_3583_, 2);
v_currRecDepth_3800_ = lean_ctor_get(v_a_3583_, 3);
v_maxRecDepth_3801_ = lean_ctor_get(v_a_3583_, 4);
v_ref_3802_ = lean_ctor_get(v_a_3583_, 5);
v_currNamespace_3803_ = lean_ctor_get(v_a_3583_, 6);
v_openDecls_3804_ = lean_ctor_get(v_a_3583_, 7);
v_initHeartbeats_3805_ = lean_ctor_get(v_a_3583_, 8);
v_maxHeartbeats_3806_ = lean_ctor_get(v_a_3583_, 9);
v_quotContext_3807_ = lean_ctor_get(v_a_3583_, 10);
v_currMacroScope_3808_ = lean_ctor_get(v_a_3583_, 11);
v_diag_3809_ = lean_ctor_get_uint8(v_a_3583_, sizeof(void*)*14);
v_cancelTk_x3f_3810_ = lean_ctor_get(v_a_3583_, 12);
v_suppressElabErrors_3811_ = lean_ctor_get_uint8(v_a_3583_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3812_ = lean_ctor_get(v_a_3583_, 13);
v___x_3813_ = 0;
v___x_3814_ = 1;
v_ref_3815_ = l_Lean_replaceRef(v_p_3573_, v_ref_3802_);
lean_dec(v_p_3573_);
lean_inc_ref(v_inheritedTraceOptions_3812_);
lean_inc(v_cancelTk_x3f_3810_);
lean_inc(v_currMacroScope_3808_);
lean_inc(v_quotContext_3807_);
lean_inc(v_maxHeartbeats_3806_);
lean_inc(v_initHeartbeats_3805_);
lean_inc(v_openDecls_3804_);
lean_inc(v_currNamespace_3803_);
lean_inc(v_maxRecDepth_3801_);
lean_inc(v_currRecDepth_3800_);
lean_inc_ref(v_options_3799_);
lean_inc_ref(v_fileMap_3798_);
lean_inc_ref(v_fileName_3797_);
v___x_3816_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3816_, 0, v_fileName_3797_);
lean_ctor_set(v___x_3816_, 1, v_fileMap_3798_);
lean_ctor_set(v___x_3816_, 2, v_options_3799_);
lean_ctor_set(v___x_3816_, 3, v_currRecDepth_3800_);
lean_ctor_set(v___x_3816_, 4, v_maxRecDepth_3801_);
lean_ctor_set(v___x_3816_, 5, v_ref_3815_);
lean_ctor_set(v___x_3816_, 6, v_currNamespace_3803_);
lean_ctor_set(v___x_3816_, 7, v_openDecls_3804_);
lean_ctor_set(v___x_3816_, 8, v_initHeartbeats_3805_);
lean_ctor_set(v___x_3816_, 9, v_maxHeartbeats_3806_);
lean_ctor_set(v___x_3816_, 10, v_quotContext_3807_);
lean_ctor_set(v___x_3816_, 11, v_currMacroScope_3808_);
lean_ctor_set(v___x_3816_, 12, v_cancelTk_x3f_3810_);
lean_ctor_set(v___x_3816_, 13, v_inheritedTraceOptions_3812_);
lean_ctor_set_uint8(v___x_3816_, sizeof(void*)*14, v_diag_3809_);
lean_ctor_set_uint8(v___x_3816_, sizeof(void*)*14 + 1, v_suppressElabErrors_3811_);
v___x_3817_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3572_, v_id_3575_, v_a_3761_, v_k_3769_, v_minIndexable_3576_, v___x_3813_, v___x_3814_, v_a_3581_, v_a_3582_, v___x_3816_, v_a_3584_);
lean_dec_ref(v___x_3816_);
return v___x_3817_;
}
}
case 1:
{
lean_del_object(v___x_3767_);
lean_dec(v_id_3575_);
if (v_incremental_3578_ == 0)
{
uint8_t v_eager_3818_; 
v_eager_3818_ = lean_ctor_get_uint8(v_a_3765_, 0);
lean_dec_ref(v_a_3765_);
v___y_3699_ = v_a_3761_;
v___y_3700_ = v_eager_3818_;
v___y_3701_ = v_a_3581_;
v___y_3702_ = v_a_3582_;
v___y_3703_ = v_a_3583_;
v___y_3704_ = v_a_3584_;
goto v___jp_3698_;
}
else
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3761_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v___x_3819_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3820_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3819_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3820_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3820_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
case 2:
{
uint8_t v___x_3829_; lean_object* v___x_3830_; 
lean_del_object(v___x_3767_);
v___x_3829_ = 0;
lean_inc(v_a_3761_);
v___x_3830_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3761_, v___x_3829_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref(v___x_3830_);
if (lean_obj_tag(v_a_3831_) == 1)
{
lean_dec(v_a_3761_);
if (v_incremental_3578_ == 0)
{
lean_object* v_val_3832_; 
v_val_3832_ = lean_ctor_get(v_a_3831_, 0);
lean_inc(v_val_3832_);
lean_dec_ref(v_a_3831_);
v___y_3751_ = v_val_3832_;
v___y_3752_ = v_a_3579_;
v___y_3753_ = v_a_3580_;
v___y_3754_ = v_a_3581_;
v___y_3755_ = v_a_3582_;
v___y_3756_ = v_a_3583_;
v___y_3757_ = v_a_3584_;
goto v___jp_3750_;
}
else
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
lean_dec_ref(v_a_3831_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v___x_3833_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3834_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3833_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3834_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
else
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec(v_a_3831_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v___x_3843_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_3844_ = l_Lean_MessageData_ofConstName(v_a_3761_, v___x_3829_);
v___x_3845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3843_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_3847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3845_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3847_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3848_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3848_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec(v_a_3761_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v_a_3857_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3830_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3830_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
case 3:
{
lean_del_object(v___x_3767_);
v___y_3587_ = v_a_3761_;
v___y_3588_ = v_a_3579_;
v___y_3589_ = v_a_3580_;
v___y_3590_ = v_a_3581_;
v___y_3591_ = v_a_3582_;
v___y_3592_ = v_a_3583_;
v___y_3593_ = v_a_3584_;
goto v___jp_3586_;
}
case 4:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_del_object(v___x_3767_);
lean_dec(v_a_3761_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v___x_3865_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_3866_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3865_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3866_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3866_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
case 5:
{
lean_object* v_prio_3875_; lean_object* v___x_3876_; 
lean_del_object(v___x_3767_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
v_prio_3875_ = lean_ctor_get(v_a_3765_, 0);
lean_inc(v_prio_3875_);
lean_dec_ref(v_a_3765_);
v___x_3876_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3576_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3900_; 
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3900_ == 0)
{
lean_object* v_unused_3901_; 
v_unused_3901_ = lean_ctor_get(v___x_3876_, 0);
lean_dec(v_unused_3901_);
v___x_3878_ = v___x_3876_;
v_isShared_3879_ = v_isSharedCheck_3900_;
goto v_resetjp_3877_;
}
else
{
lean_dec(v___x_3876_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3900_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v_config_3880_; lean_object* v_extensions_3881_; lean_object* v_extra_3882_; lean_object* v_extraInj_3883_; lean_object* v_extraFacts_3884_; lean_object* v_symPrios_3885_; lean_object* v_norm_3886_; lean_object* v_normProcs_3887_; lean_object* v_anchorRefs_x3f_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3899_; 
v_config_3880_ = lean_ctor_get(v_params_3572_, 0);
v_extensions_3881_ = lean_ctor_get(v_params_3572_, 1);
v_extra_3882_ = lean_ctor_get(v_params_3572_, 2);
v_extraInj_3883_ = lean_ctor_get(v_params_3572_, 3);
v_extraFacts_3884_ = lean_ctor_get(v_params_3572_, 4);
v_symPrios_3885_ = lean_ctor_get(v_params_3572_, 5);
v_norm_3886_ = lean_ctor_get(v_params_3572_, 6);
v_normProcs_3887_ = lean_ctor_get(v_params_3572_, 7);
v_anchorRefs_x3f_3888_ = lean_ctor_get(v_params_3572_, 8);
v_isSharedCheck_3899_ = !lean_is_exclusive(v_params_3572_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3890_ = v_params_3572_;
v_isShared_3891_ = v_isSharedCheck_3899_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_anchorRefs_x3f_3888_);
lean_inc(v_normProcs_3887_);
lean_inc(v_norm_3886_);
lean_inc(v_symPrios_3885_);
lean_inc(v_extraFacts_3884_);
lean_inc(v_extraInj_3883_);
lean_inc(v_extra_3882_);
lean_inc(v_extensions_3881_);
lean_inc(v_config_3880_);
lean_dec(v_params_3572_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3899_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3892_; lean_object* v___x_3894_; 
v___x_3892_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_3885_, v_a_3761_, v_prio_3875_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 5, v___x_3892_);
v___x_3894_ = v___x_3890_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_config_3880_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v_extensions_3881_);
lean_ctor_set(v_reuseFailAlloc_3898_, 2, v_extra_3882_);
lean_ctor_set(v_reuseFailAlloc_3898_, 3, v_extraInj_3883_);
lean_ctor_set(v_reuseFailAlloc_3898_, 4, v_extraFacts_3884_);
lean_ctor_set(v_reuseFailAlloc_3898_, 5, v___x_3892_);
lean_ctor_set(v_reuseFailAlloc_3898_, 6, v_norm_3886_);
lean_ctor_set(v_reuseFailAlloc_3898_, 7, v_normProcs_3887_);
lean_ctor_set(v_reuseFailAlloc_3898_, 8, v_anchorRefs_x3f_3888_);
v___x_3894_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
lean_object* v___x_3896_; 
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 0, v___x_3894_);
v___x_3896_ = v___x_3878_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
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
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_dec(v_prio_3875_);
lean_dec(v_a_3761_);
lean_dec_ref(v_params_3572_);
v_a_3902_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3876_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3876_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
case 6:
{
lean_object* v___x_3910_; 
lean_del_object(v___x_3767_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
v___x_3910_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3761_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3935_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3935_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3935_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v_config_3915_; lean_object* v_extensions_3916_; lean_object* v_extra_3917_; lean_object* v_extraInj_3918_; lean_object* v_extraFacts_3919_; lean_object* v_symPrios_3920_; lean_object* v_norm_3921_; lean_object* v_normProcs_3922_; lean_object* v_anchorRefs_x3f_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3934_; 
v_config_3915_ = lean_ctor_get(v_params_3572_, 0);
v_extensions_3916_ = lean_ctor_get(v_params_3572_, 1);
v_extra_3917_ = lean_ctor_get(v_params_3572_, 2);
v_extraInj_3918_ = lean_ctor_get(v_params_3572_, 3);
v_extraFacts_3919_ = lean_ctor_get(v_params_3572_, 4);
v_symPrios_3920_ = lean_ctor_get(v_params_3572_, 5);
v_norm_3921_ = lean_ctor_get(v_params_3572_, 6);
v_normProcs_3922_ = lean_ctor_get(v_params_3572_, 7);
v_anchorRefs_x3f_3923_ = lean_ctor_get(v_params_3572_, 8);
v_isSharedCheck_3934_ = !lean_is_exclusive(v_params_3572_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3925_ = v_params_3572_;
v_isShared_3926_ = v_isSharedCheck_3934_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_anchorRefs_x3f_3923_);
lean_inc(v_normProcs_3922_);
lean_inc(v_norm_3921_);
lean_inc(v_symPrios_3920_);
lean_inc(v_extraFacts_3919_);
lean_inc(v_extraInj_3918_);
lean_inc(v_extra_3917_);
lean_inc(v_extensions_3916_);
lean_inc(v_config_3915_);
lean_dec(v_params_3572_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3934_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3927_ = l_Lean_PersistentArray_push___redArg(v_extraInj_3918_, v_a_3911_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 3, v___x_3927_);
v___x_3929_ = v___x_3925_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_config_3915_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v_extensions_3916_);
lean_ctor_set(v_reuseFailAlloc_3933_, 2, v_extra_3917_);
lean_ctor_set(v_reuseFailAlloc_3933_, 3, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3933_, 4, v_extraFacts_3919_);
lean_ctor_set(v_reuseFailAlloc_3933_, 5, v_symPrios_3920_);
lean_ctor_set(v_reuseFailAlloc_3933_, 6, v_norm_3921_);
lean_ctor_set(v_reuseFailAlloc_3933_, 7, v_normProcs_3922_);
lean_ctor_set(v_reuseFailAlloc_3933_, 8, v_anchorRefs_x3f_3923_);
v___x_3929_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
lean_object* v___x_3931_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3929_);
v___x_3931_ = v___x_3913_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3929_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec_ref(v_params_3572_);
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
case 7:
{
lean_object* v___x_3944_; lean_object* v___x_3946_; 
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
v___x_3944_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3572_, v_a_3761_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 0, v___x_3944_);
v___x_3946_ = v___x_3767_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
case 8:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3957_; 
lean_dec_ref(v_a_3765_);
lean_del_object(v___x_3767_);
lean_dec(v_a_3761_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v___x_3948_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_3949_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3948_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3952_ = v___x_3949_;
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3949_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3950_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
default: 
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_del_object(v___x_3767_);
lean_dec(v_a_3761_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v___x_3958_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_3959_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3958_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3959_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3959_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
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
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
lean_dec(v_a_3761_);
lean_dec(v_id_3575_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v_a_3969_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3764_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3764_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_3574_);
v___y_3587_ = v_a_3761_;
v___y_3588_ = v_a_3579_;
v___y_3589_ = v_a_3580_;
v___y_3590_ = v_a_3581_;
v___y_3591_ = v_a_3582_;
v___y_3592_ = v_a_3583_;
v___y_3593_ = v_a_3584_;
goto v___jp_3586_;
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec(v_a_3761_);
lean_dec(v_id_3575_);
lean_dec(v_mod_x3f_3574_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v_a_3977_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3762_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3762_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
v___jp_3985_:
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3996_; 
v_a_3987_ = lean_ctor_get(v___y_3986_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___y_3986_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3989_ = v___y_3986_;
v_isShared_3990_ = v_isSharedCheck_3996_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___y_3986_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3996_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
if (lean_obj_tag(v_a_3987_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3993_; 
lean_dec(v_id_3575_);
lean_dec(v_mod_x3f_3574_);
lean_dec(v_p_3573_);
lean_dec_ref(v_params_3572_);
v_a_3991_ = lean_ctor_get(v_a_3987_, 0);
lean_inc(v_a_3991_);
lean_dec_ref(v_a_3987_);
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 0, v_a_3991_);
v___x_3993_ = v___x_3989_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3991_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
else
{
lean_object* v_a_3995_; 
lean_del_object(v___x_3989_);
v_a_3995_ = lean_ctor_get(v_a_3987_, 0);
lean_inc(v_a_3995_);
lean_dec_ref(v_a_3987_);
v_a_3761_ = v_a_3995_;
goto v___jp_3760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4075_, lean_object* v_p_4076_, lean_object* v_mod_x3f_4077_, lean_object* v_id_4078_, lean_object* v_minIndexable_4079_, lean_object* v_only_4080_, lean_object* v_incremental_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_){
_start:
{
uint8_t v_minIndexable_boxed_4089_; uint8_t v_only_boxed_4090_; uint8_t v_incremental_boxed_4091_; lean_object* v_res_4092_; 
v_minIndexable_boxed_4089_ = lean_unbox(v_minIndexable_4079_);
v_only_boxed_4090_ = lean_unbox(v_only_4080_);
v_incremental_boxed_4091_ = lean_unbox(v_incremental_4081_);
v_res_4092_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4075_, v_p_4076_, v_mod_x3f_4077_, v_id_4078_, v_minIndexable_boxed_4089_, v_only_boxed_4090_, v_incremental_boxed_4091_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_);
lean_dec(v_a_4087_);
lean_dec_ref(v_a_4086_);
lean_dec(v_a_4085_);
lean_dec_ref(v_a_4084_);
lean_dec(v_a_4083_);
lean_dec_ref(v_a_4082_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4093_, lean_object* v_id_4094_, uint8_t v_minIndexable_4095_, lean_object* v_as_4096_, lean_object* v_as_x27_4097_, lean_object* v_b_4098_, lean_object* v_a_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v___x_4107_; 
v___x_4107_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4093_, v_id_4094_, v_minIndexable_4095_, v_as_x27_4097_, v_b_4098_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4108_, lean_object* v_id_4109_, lean_object* v_minIndexable_4110_, lean_object* v_as_4111_, lean_object* v_as_x27_4112_, lean_object* v_b_4113_, lean_object* v_a_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
uint8_t v_minIndexable_boxed_4122_; lean_object* v_res_4123_; 
v_minIndexable_boxed_4122_ = lean_unbox(v_minIndexable_4110_);
v_res_4123_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4108_, v_id_4109_, v_minIndexable_boxed_4122_, v_as_4111_, v_as_x27_4112_, v_b_4113_, v_a_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v_as_x27_4112_);
lean_dec(v_as_4111_);
lean_dec(v_p_4108_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4124_, lean_object* v_as_x27_4125_, lean_object* v_b_4126_, lean_object* v_a_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4125_, v_b_4126_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4136_, lean_object* v_as_x27_4137_, lean_object* v_b_4138_, lean_object* v_a_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4136_, v_as_x27_4137_, v_b_4138_, v_a_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v_as_x27_4137_);
lean_dec(v_as_4136_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4148_, lean_object* v_ref_4149_, lean_object* v_msg_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v___x_4158_; 
v___x_4158_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4149_, v_msg_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4159_, lean_object* v_ref_4160_, lean_object* v_msg_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4159_, v_ref_4160_, v_msg_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v_ref_4160_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4170_, lean_object* v_id_4171_, uint8_t v_minIndexable_4172_, lean_object* v_as_4173_, lean_object* v_as_x27_4174_, lean_object* v_b_4175_, lean_object* v_a_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
lean_object* v___x_4184_; 
v___x_4184_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4170_, v_id_4171_, v_minIndexable_4172_, v_as_x27_4174_, v_b_4175_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4185_, lean_object* v_id_4186_, lean_object* v_minIndexable_4187_, lean_object* v_as_4188_, lean_object* v_as_x27_4189_, lean_object* v_b_4190_, lean_object* v_a_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
uint8_t v_minIndexable_boxed_4199_; lean_object* v_res_4200_; 
v_minIndexable_boxed_4199_ = lean_unbox(v_minIndexable_4187_);
v_res_4200_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4185_, v_id_4186_, v_minIndexable_boxed_4199_, v_as_4188_, v_as_x27_4189_, v_b_4190_, v_a_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec(v___y_4195_);
lean_dec_ref(v___y_4194_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v_as_x27_4189_);
lean_dec(v_as_4188_);
lean_dec(v_p_4185_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4201_, lean_object* v_t_4202_, lean_object* v_k_4203_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4202_, v_k_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4205_, lean_object* v_t_4206_, lean_object* v_k_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4205_, v_t_4206_, v_k_4207_);
lean_dec(v_k_4207_);
lean_dec(v_t_4206_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4209_, uint8_t v_skipAuxDecl_4210_, lean_object* v_auxDeclToFullName_4211_, lean_object* v___x_4212_, lean_object* v_givenNameView_4213_, lean_object* v_as_4214_, lean_object* v_i_4215_, lean_object* v_a_4216_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4209_, v_skipAuxDecl_4210_, v_auxDeclToFullName_4211_, v___x_4212_, v_givenNameView_4213_, v_as_4214_, v_i_4215_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4218_, lean_object* v_skipAuxDecl_4219_, lean_object* v_auxDeclToFullName_4220_, lean_object* v___x_4221_, lean_object* v_givenNameView_4222_, lean_object* v_as_4223_, lean_object* v_i_4224_, lean_object* v_a_4225_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4226_; lean_object* v_res_4227_; 
v_skipAuxDecl_boxed_4226_ = lean_unbox(v_skipAuxDecl_4219_);
v_res_4227_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4218_, v_skipAuxDecl_boxed_4226_, v_auxDeclToFullName_4220_, v___x_4221_, v_givenNameView_4222_, v_as_4223_, v_i_4224_, v_a_4225_);
lean_dec_ref(v_as_4223_);
lean_dec(v_auxDeclToFullName_4220_);
lean_dec(v_givenName_4218_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4228_, lean_object* v_givenName_4229_, lean_object* v_as_4230_, lean_object* v_i_4231_, lean_object* v_a_4232_){
_start:
{
lean_object* v___x_4233_; 
v___x_4233_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4228_, v_givenName_4229_, v_as_4230_, v_i_4231_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4234_, lean_object* v_givenName_4235_, lean_object* v_as_4236_, lean_object* v_i_4237_, lean_object* v_a_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4234_, v_givenName_4235_, v_as_4236_, v_i_4237_, v_a_4238_);
lean_dec_ref(v_as_4236_);
lean_dec(v_givenName_4235_);
lean_dec(v_localDecl_x3f_4234_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4240_, uint8_t v_skipAuxDecl_4241_, lean_object* v_auxDeclToFullName_4242_, lean_object* v___x_4243_, lean_object* v_givenNameView_4244_, lean_object* v_as_4245_, lean_object* v_i_4246_, lean_object* v_a_4247_){
_start:
{
lean_object* v___x_4248_; 
v___x_4248_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4240_, v_skipAuxDecl_4241_, v_auxDeclToFullName_4242_, v___x_4243_, v_givenNameView_4244_, v_as_4245_, v_i_4246_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4249_, lean_object* v_skipAuxDecl_4250_, lean_object* v_auxDeclToFullName_4251_, lean_object* v___x_4252_, lean_object* v_givenNameView_4253_, lean_object* v_as_4254_, lean_object* v_i_4255_, lean_object* v_a_4256_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4257_; lean_object* v_res_4258_; 
v_skipAuxDecl_boxed_4257_ = lean_unbox(v_skipAuxDecl_4250_);
v_res_4258_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4249_, v_skipAuxDecl_boxed_4257_, v_auxDeclToFullName_4251_, v___x_4252_, v_givenNameView_4253_, v_as_4254_, v_i_4255_, v_a_4256_);
lean_dec_ref(v_as_4254_);
lean_dec(v_auxDeclToFullName_4251_);
lean_dec(v_givenName_4249_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4259_, lean_object* v_givenName_4260_, lean_object* v_as_4261_, lean_object* v_i_4262_, lean_object* v_a_4263_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4259_, v_givenName_4260_, v_as_4261_, v_i_4262_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4265_, lean_object* v_givenName_4266_, lean_object* v_as_4267_, lean_object* v_i_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4265_, v_givenName_4266_, v_as_4267_, v_i_4268_, v_a_4269_);
lean_dec_ref(v_as_4267_);
lean_dec(v_givenName_4266_);
lean_dec(v_localDecl_x3f_4265_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v___x_4279_; 
v___x_4279_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4271_, v___y_4276_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec_ref(v_opt_4280_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4289_, lean_object* v_msgData_4290_, uint8_t v_severity_4291_, uint8_t v_isSilent_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4289_, v_msgData_4290_, v_severity_4291_, v_isSilent_4292_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4301_, lean_object* v_msgData_4302_, lean_object* v_severity_4303_, lean_object* v_isSilent_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
uint8_t v_severity_boxed_4312_; uint8_t v_isSilent_boxed_4313_; lean_object* v_res_4314_; 
v_severity_boxed_4312_ = lean_unbox(v_severity_4303_);
v_isSilent_boxed_4313_ = lean_unbox(v_isSilent_4304_);
v_res_4314_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4301_, v_msgData_4302_, v_severity_boxed_4312_, v_isSilent_boxed_4313_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v_ref_4301_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4315_, lean_object* v_b_4316_, lean_object* v_____r_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4325_ = lean_box(0);
v___x_4326_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4315_, v___x_4325_, v___y_4322_, v___y_4323_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v_a_4327_; lean_object* v___x_4328_; 
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
lean_inc_n(v_a_4327_, 2);
lean_dec_ref(v___x_4326_);
v___x_4328_ = l_Lean_Linter_checkDeprecated(v_a_4327_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
if (lean_obj_tag(v___x_4328_) == 0)
{
uint8_t v___x_4329_; lean_object* v___x_4330_; 
lean_dec_ref(v___x_4328_);
v___x_4329_ = 0;
lean_inc(v_a_4327_);
v___x_4330_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4327_, v___x_4329_, v___y_4322_, v___y_4323_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4390_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4333_ = v___x_4330_;
v_isShared_4334_ = v_isSharedCheck_4390_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4330_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4390_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
if (lean_obj_tag(v_a_4331_) == 1)
{
lean_object* v_val_4335_; lean_object* v___x_4336_; 
lean_del_object(v___x_4333_);
lean_dec(v_a_4327_);
v_val_4335_ = lean_ctor_get(v_a_4331_, 0);
lean_inc_n(v_val_4335_, 2);
lean_dec_ref(v_a_4331_);
v___x_4336_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4335_, v___y_4322_, v___y_4323_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v___x_4337_; 
lean_dec_ref(v___x_4336_);
v___x_4337_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4316_, v_val_4335_, v___y_4322_, v___y_4323_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4347_; 
v_a_4338_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4340_ = v___x_4337_;
v_isShared_4341_ = v_isSharedCheck_4347_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4337_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4347_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4345_; 
v___x_4342_ = lean_box(0);
v___x_4343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4342_);
lean_ctor_set(v___x_4343_, 1, v_a_4338_);
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 0, v___x_4343_);
v___x_4345_ = v___x_4340_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4343_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
v_a_4348_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4337_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4337_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
lean_dec(v_val_4335_);
lean_dec_ref(v_b_4316_);
v_a_4356_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4336_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4336_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
}
else
{
uint8_t v___x_4364_; 
lean_dec(v_a_4331_);
lean_inc(v_a_4327_);
v___x_4364_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4316_, v_a_4327_);
if (v___x_4364_ == 0)
{
lean_object* v___x_4365_; 
lean_del_object(v___x_4333_);
v___x_4365_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4316_, v_a_4327_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4375_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4368_ = v___x_4365_;
v_isShared_4369_ = v_isSharedCheck_4375_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4365_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4375_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4373_; 
v___x_4370_ = lean_box(0);
v___x_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4370_);
lean_ctor_set(v___x_4371_, 1, v_a_4366_);
if (v_isShared_4369_ == 0)
{
lean_ctor_set(v___x_4368_, 0, v___x_4371_);
v___x_4373_ = v___x_4368_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4371_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
else
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
v_a_4376_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4365_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4365_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4376_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
else
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4388_; 
v___x_4384_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4316_, v_a_4327_);
v___x_4385_ = lean_box(0);
v___x_4386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
lean_ctor_set(v___x_4386_, 1, v___x_4384_);
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 0, v___x_4386_);
v___x_4388_ = v___x_4333_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4386_);
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
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_dec(v_a_4327_);
lean_dec_ref(v_b_4316_);
v_a_4391_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4330_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4330_);
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
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
lean_dec(v_a_4327_);
lean_dec_ref(v_b_4316_);
v_a_4399_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4328_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4328_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec_ref(v_b_4316_);
v_a_4407_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4326_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4326_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4415_, lean_object* v_b_4416_, lean_object* v_____r_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4415_, v_b_4416_, v_____r_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4429_, lean_object* v_b_4430_, lean_object* v_a_4431_, uint8_t v___x_4432_, uint8_t v_only_4433_, uint8_t v_incremental_4434_, lean_object* v_x_4435_, lean_object* v_mod_x3f_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; uint8_t v___x_4447_; 
v___x_4444_ = lean_unsigned_to_nat(1u);
v___x_4445_ = l_Lean_Syntax_getArg(v___x_4429_, v___x_4444_);
v___x_4446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4445_);
v___x_4447_ = l_Lean_Syntax_isOfKind(v___x_4445_, v___x_4446_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; 
v___x_4448_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4430_, v_a_4431_, v_mod_x3f_4436_, v___x_4445_, v___x_4447_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4458_; 
v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4451_ = v___x_4448_;
v_isShared_4452_ = v_isSharedCheck_4458_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4448_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4458_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4456_; 
v___x_4453_ = lean_box(0);
v___x_4454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4453_);
lean_ctor_set(v___x_4454_, 1, v_a_4449_);
if (v_isShared_4452_ == 0)
{
lean_ctor_set(v___x_4451_, 0, v___x_4454_);
v___x_4456_ = v___x_4451_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v___x_4454_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
v_a_4459_ = lean_ctor_get(v___x_4448_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4448_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4448_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
else
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = l_Lean_TSyntax_getId(v___x_4445_);
v___x_4468_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4467_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v_a_4469_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; 
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
lean_inc(v_a_4469_);
lean_dec_ref(v___x_4468_);
if (lean_obj_tag(v_a_4469_) == 1)
{
lean_object* v_val_4496_; lean_object* v_snd_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4522_; 
v_val_4496_ = lean_ctor_get(v_a_4469_, 0);
lean_inc(v_val_4496_);
lean_dec_ref(v_a_4469_);
v_snd_4497_ = lean_ctor_get(v_val_4496_, 1);
v_isSharedCheck_4522_ = !lean_is_exclusive(v_val_4496_);
if (v_isSharedCheck_4522_ == 0)
{
lean_object* v_unused_4523_; 
v_unused_4523_ = lean_ctor_get(v_val_4496_, 0);
lean_dec(v_unused_4523_);
v___x_4499_ = v_val_4496_;
v_isShared_4500_ = v_isSharedCheck_4522_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_snd_4497_);
lean_dec(v_val_4496_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4522_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
if (lean_obj_tag(v_snd_4497_) == 1)
{
lean_object* v___x_4501_; 
lean_dec_ref(v_snd_4497_);
v___x_4501_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4430_, v_a_4431_, v_mod_x3f_4436_, v___x_4445_, v___x_4432_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4513_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4504_ = v___x_4501_;
v_isShared_4505_ = v_isSharedCheck_4513_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4501_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4513_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4506_ = lean_box(0);
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 1, v_a_4502_);
lean_ctor_set(v___x_4499_, 0, v___x_4506_);
v___x_4508_ = v___x_4499_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4506_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_a_4502_);
v___x_4508_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4510_; 
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 0, v___x_4508_);
v___x_4510_ = v___x_4504_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4508_);
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
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
lean_del_object(v___x_4499_);
v_a_4514_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4501_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4501_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
else
{
lean_del_object(v___x_4499_);
lean_dec(v_snd_4497_);
v___y_4471_ = v___y_4437_;
v___y_4472_ = v___y_4438_;
v___y_4473_ = v___y_4439_;
v___y_4474_ = v___y_4440_;
v___y_4475_ = v___y_4441_;
v___y_4476_ = v___y_4442_;
goto v___jp_4470_;
}
}
}
else
{
lean_dec(v_a_4469_);
v___y_4471_ = v___y_4437_;
v___y_4472_ = v___y_4438_;
v___y_4473_ = v___y_4439_;
v___y_4474_ = v___y_4440_;
v___y_4475_ = v___y_4441_;
v___y_4476_ = v___y_4442_;
goto v___jp_4470_;
}
v___jp_4470_:
{
lean_object* v___x_4477_; 
v___x_4477_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4430_, v_a_4431_, v_mod_x3f_4436_, v___x_4445_, v___x_4432_, v_only_4433_, v_incremental_4434_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4487_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4480_ = v___x_4477_;
v_isShared_4481_ = v_isSharedCheck_4487_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4477_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4487_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4485_; 
v___x_4482_ = lean_box(0);
v___x_4483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4483_, 0, v___x_4482_);
lean_ctor_set(v___x_4483_, 1, v_a_4478_);
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 0, v___x_4483_);
v___x_4485_ = v___x_4480_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v___x_4483_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
else
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
v_a_4488_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4490_ = v___x_4477_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4477_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
}
else
{
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4531_; 
lean_dec(v___x_4445_);
lean_dec(v_mod_x3f_4436_);
lean_dec(v_a_4431_);
lean_dec_ref(v_b_4430_);
v_a_4524_ = lean_ctor_get(v___x_4468_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4468_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4526_ = v___x_4468_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4468_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4527_ == 0)
{
v___x_4529_ = v___x_4526_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4524_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
return v___x_4529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4532_, lean_object* v_b_4533_, lean_object* v_a_4534_, lean_object* v___x_4535_, lean_object* v_only_4536_, lean_object* v_incremental_4537_, lean_object* v_x_4538_, lean_object* v_mod_x3f_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
uint8_t v___x_23950__boxed_4547_; uint8_t v_only_boxed_4548_; uint8_t v_incremental_boxed_4549_; lean_object* v_res_4550_; 
v___x_23950__boxed_4547_ = lean_unbox(v___x_4535_);
v_only_boxed_4548_ = lean_unbox(v_only_4536_);
v_incremental_boxed_4549_ = lean_unbox(v_incremental_4537_);
v_res_4550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4532_, v_b_4533_, v_a_4534_, v___x_23950__boxed_4547_, v_only_boxed_4548_, v_incremental_boxed_4549_, v_x_4538_, v_mod_x3f_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___x_4532_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4551_, lean_object* v___x_4552_, lean_object* v_____r_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v___x_4561_; 
v___x_4561_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4551_, v___x_4552_, v___y_4558_, v___y_4559_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4571_; 
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4564_ = v___x_4561_;
v_isShared_4565_ = v_isSharedCheck_4571_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4561_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4571_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4569_; 
v___x_4566_ = lean_box(0);
v___x_4567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4566_);
lean_ctor_set(v___x_4567_, 1, v_a_4562_);
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 0, v___x_4567_);
v___x_4569_ = v___x_4564_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
v_a_4572_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4561_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4561_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4580_, lean_object* v___x_4581_, lean_object* v_____r_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4580_, v___x_4581_, v_____r_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v___x_4581_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4591_, lean_object* v_b_4592_, lean_object* v_a_4593_, uint8_t v___x_4594_, uint8_t v_only_4595_, uint8_t v_incremental_4596_, lean_object* v_x_4597_, lean_object* v_mod_x3f_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; uint8_t v___x_4609_; 
v___x_4606_ = lean_unsigned_to_nat(2u);
v___x_4607_ = l_Lean_Syntax_getArg(v___x_4591_, v___x_4606_);
v___x_4608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4607_);
v___x_4609_ = l_Lean_Syntax_isOfKind(v___x_4607_, v___x_4608_);
if (v___x_4609_ == 0)
{
lean_object* v___x_4610_; 
v___x_4610_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4592_, v_a_4593_, v_mod_x3f_4598_, v___x_4607_, v___x_4594_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4620_; 
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4613_ = v___x_4610_;
v_isShared_4614_ = v_isSharedCheck_4620_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4620_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4618_; 
v___x_4615_ = lean_box(0);
v___x_4616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
lean_ctor_set(v___x_4616_, 1, v_a_4611_);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v___x_4616_);
v___x_4618_ = v___x_4613_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v___x_4616_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
}
else
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
v_a_4621_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4610_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4610_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
}
else
{
lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4629_ = l_Lean_TSyntax_getId(v___x_4607_);
v___x_4630_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4629_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
if (lean_obj_tag(v___x_4630_) == 0)
{
lean_object* v_a_4631_; lean_object* v___y_4633_; lean_object* v___y_4634_; lean_object* v___y_4635_; lean_object* v___y_4636_; lean_object* v___y_4637_; lean_object* v___y_4638_; 
v_a_4631_ = lean_ctor_get(v___x_4630_, 0);
lean_inc(v_a_4631_);
lean_dec_ref(v___x_4630_);
if (lean_obj_tag(v_a_4631_) == 1)
{
lean_object* v_val_4658_; lean_object* v_snd_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4684_; 
v_val_4658_ = lean_ctor_get(v_a_4631_, 0);
lean_inc(v_val_4658_);
lean_dec_ref(v_a_4631_);
v_snd_4659_ = lean_ctor_get(v_val_4658_, 1);
v_isSharedCheck_4684_ = !lean_is_exclusive(v_val_4658_);
if (v_isSharedCheck_4684_ == 0)
{
lean_object* v_unused_4685_; 
v_unused_4685_ = lean_ctor_get(v_val_4658_, 0);
lean_dec(v_unused_4685_);
v___x_4661_ = v_val_4658_;
v_isShared_4662_ = v_isSharedCheck_4684_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_snd_4659_);
lean_dec(v_val_4658_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4684_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
if (lean_obj_tag(v_snd_4659_) == 1)
{
lean_object* v___x_4663_; 
lean_dec_ref(v_snd_4659_);
v___x_4663_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4592_, v_a_4593_, v_mod_x3f_4598_, v___x_4607_, v___x_4594_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4675_; 
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4666_ = v___x_4663_;
v_isShared_4667_ = v_isSharedCheck_4675_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4663_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4675_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4668_; lean_object* v___x_4670_; 
v___x_4668_ = lean_box(0);
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 1, v_a_4664_);
lean_ctor_set(v___x_4661_, 0, v___x_4668_);
v___x_4670_ = v___x_4661_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v___x_4668_);
lean_ctor_set(v_reuseFailAlloc_4674_, 1, v_a_4664_);
v___x_4670_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
lean_object* v___x_4672_; 
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 0, v___x_4670_);
v___x_4672_ = v___x_4666_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v___x_4670_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
}
}
else
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4683_; 
lean_del_object(v___x_4661_);
v_a_4676_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4678_ = v___x_4663_;
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4663_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4681_; 
if (v_isShared_4679_ == 0)
{
v___x_4681_ = v___x_4678_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_a_4676_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
}
else
{
lean_del_object(v___x_4661_);
lean_dec(v_snd_4659_);
v___y_4633_ = v___y_4599_;
v___y_4634_ = v___y_4600_;
v___y_4635_ = v___y_4601_;
v___y_4636_ = v___y_4602_;
v___y_4637_ = v___y_4603_;
v___y_4638_ = v___y_4604_;
goto v___jp_4632_;
}
}
}
else
{
lean_dec(v_a_4631_);
v___y_4633_ = v___y_4599_;
v___y_4634_ = v___y_4600_;
v___y_4635_ = v___y_4601_;
v___y_4636_ = v___y_4602_;
v___y_4637_ = v___y_4603_;
v___y_4638_ = v___y_4604_;
goto v___jp_4632_;
}
v___jp_4632_:
{
lean_object* v___x_4639_; 
v___x_4639_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4592_, v_a_4593_, v_mod_x3f_4598_, v___x_4607_, v___x_4594_, v_only_4595_, v_incremental_4596_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
if (lean_obj_tag(v___x_4639_) == 0)
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4649_; 
v_a_4640_ = lean_ctor_get(v___x_4639_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4639_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4642_ = v___x_4639_;
v_isShared_4643_ = v_isSharedCheck_4649_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4639_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4649_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4647_; 
v___x_4644_ = lean_box(0);
v___x_4645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4644_);
lean_ctor_set(v___x_4645_, 1, v_a_4640_);
if (v_isShared_4643_ == 0)
{
lean_ctor_set(v___x_4642_, 0, v___x_4645_);
v___x_4647_ = v___x_4642_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4645_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
else
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
v_a_4650_ = lean_ctor_get(v___x_4639_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4639_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v___x_4639_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4639_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
}
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
lean_dec(v___x_4607_);
lean_dec(v_mod_x3f_4598_);
lean_dec(v_a_4593_);
lean_dec_ref(v_b_4592_);
v_a_4686_ = lean_ctor_get(v___x_4630_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4630_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4630_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4630_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4694_, lean_object* v_b_4695_, lean_object* v_a_4696_, lean_object* v___x_4697_, lean_object* v_only_4698_, lean_object* v_incremental_4699_, lean_object* v_x_4700_, lean_object* v_mod_x3f_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
uint8_t v___x_24229__boxed_4709_; uint8_t v_only_boxed_4710_; uint8_t v_incremental_boxed_4711_; lean_object* v_res_4712_; 
v___x_24229__boxed_4709_ = lean_unbox(v___x_4697_);
v_only_boxed_4710_ = lean_unbox(v_only_4698_);
v_incremental_boxed_4711_ = lean_unbox(v_incremental_4699_);
v_res_4712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4694_, v_b_4695_, v_a_4696_, v___x_24229__boxed_4709_, v_only_boxed_4710_, v_incremental_boxed_4711_, v_x_4700_, v_mod_x3f_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v___x_4694_);
return v_res_4712_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4721_ = l_Lean_stringToMessageData(v___x_4720_);
return v___x_4721_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15(void){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14));
v___x_4751_ = l_Lean_stringToMessageData(v___x_4750_);
return v___x_4751_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4754_ = l_Lean_stringToMessageData(v___x_4753_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4755_, uint8_t v_only_4756_, uint8_t v_incremental_4757_, lean_object* v_as_4758_, size_t v_sz_4759_, size_t v_i_4760_, lean_object* v_b_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
lean_object* v_snd_4770_; lean_object* v___y_4775_; uint8_t v___y_4776_; lean_object* v_a_4780_; lean_object* v___y_4784_; uint8_t v___x_4788_; 
v___x_4788_ = lean_usize_dec_lt(v_i_4760_, v_sz_4759_);
if (v___x_4788_ == 0)
{
lean_object* v___x_4789_; 
v___x_4789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4789_, 0, v_b_4761_);
return v___x_4789_;
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4791_; uint8_t v___x_4792_; 
v_a_4790_ = lean_array_uget_borrowed(v_as_4758_, v_i_4760_);
v___x_4791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_4790_);
v___x_4792_ = l_Lean_Syntax_isOfKind(v_a_4790_, v___x_4791_);
if (v___x_4792_ == 0)
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4793_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4790_);
v___x_4794_ = l_Lean_MessageData_ofSyntax(v_a_4790_);
v___x_4795_ = l_Lean_indentD(v___x_4794_);
v___x_4796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4793_);
lean_ctor_set(v___x_4796_, 1, v___x_4795_);
v___x_4797_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4796_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_dec_ref(v___x_4797_);
v_snd_4770_ = v_b_4761_;
goto v___jp_4769_;
}
else
{
lean_object* v_a_4798_; 
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
lean_inc(v_a_4798_);
lean_dec_ref(v___x_4797_);
v_a_4780_ = v_a_4798_;
goto v___jp_4779_;
}
}
else
{
lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; uint8_t v___x_4802_; 
v___x_4799_ = lean_unsigned_to_nat(0u);
v___x_4800_ = l_Lean_Syntax_getArg(v_a_4790_, v___x_4799_);
v___x_4801_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_4800_);
v___x_4802_ = l_Lean_Syntax_isOfKind(v___x_4800_, v___x_4801_);
if (v___x_4802_ == 0)
{
lean_object* v___x_4803_; uint8_t v___x_4804_; 
v___x_4803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_4800_);
v___x_4804_ = l_Lean_Syntax_isOfKind(v___x_4800_, v___x_4803_);
if (v___x_4804_ == 0)
{
lean_object* v___x_4805_; uint8_t v___x_4806_; 
v___x_4805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_4800_);
v___x_4806_ = l_Lean_Syntax_isOfKind(v___x_4800_, v___x_4805_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; uint8_t v___x_4808_; 
v___x_4807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_4800_);
v___x_4808_ = l_Lean_Syntax_isOfKind(v___x_4800_, v___x_4807_);
if (v___x_4808_ == 0)
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
lean_dec(v___x_4800_);
v___x_4809_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4790_);
v___x_4810_ = l_Lean_MessageData_ofSyntax(v_a_4790_);
v___x_4811_ = l_Lean_indentD(v___x_4810_);
v___x_4812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4812_, 0, v___x_4809_);
lean_ctor_set(v___x_4812_, 1, v___x_4811_);
v___x_4813_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4812_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_dec_ref(v___x_4813_);
v_snd_4770_ = v_b_4761_;
goto v___jp_4769_;
}
else
{
lean_object* v_a_4814_; 
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
lean_inc(v_a_4814_);
lean_dec_ref(v___x_4813_);
v_a_4780_ = v_a_4814_;
goto v___jp_4779_;
}
}
else
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; 
v___x_4815_ = lean_unsigned_to_nat(1u);
v___x_4816_ = l_Lean_Syntax_getArg(v___x_4800_, v___x_4815_);
lean_dec(v___x_4800_);
v___x_4817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13));
lean_inc(v___x_4816_);
v___x_4818_ = l_Lean_Syntax_isOfKind(v___x_4816_, v___x_4817_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
lean_dec(v___x_4816_);
v___x_4819_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4790_);
v___x_4820_ = l_Lean_MessageData_ofSyntax(v_a_4790_);
v___x_4821_ = l_Lean_indentD(v___x_4820_);
v___x_4822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4819_);
lean_ctor_set(v___x_4822_, 1, v___x_4821_);
v___x_4823_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4822_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_dec_ref(v___x_4823_);
v_snd_4770_ = v_b_4761_;
goto v___jp_4769_;
}
else
{
lean_object* v_a_4824_; 
v_a_4824_ = lean_ctor_get(v___x_4823_, 0);
lean_inc(v_a_4824_);
lean_dec_ref(v___x_4823_);
v_a_4780_ = v_a_4824_;
goto v___jp_4779_;
}
}
else
{
if (v_only_4756_ == 0)
{
lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4825_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15);
v___x_4826_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_4816_, v___x_4825_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4826_) == 0)
{
lean_object* v_a_4827_; lean_object* v___x_4828_; 
v_a_4827_ = lean_ctor_get(v___x_4826_, 0);
lean_inc(v_a_4827_);
lean_dec_ref(v___x_4826_);
lean_inc_ref(v_b_4761_);
v___x_4828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4761_, v___x_4816_, v_a_4827_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
lean_dec(v___x_4816_);
v___y_4784_ = v___x_4828_;
goto v___jp_4783_;
}
else
{
lean_object* v_a_4829_; 
lean_dec(v___x_4816_);
v_a_4829_ = lean_ctor_get(v___x_4826_, 0);
lean_inc(v_a_4829_);
lean_dec_ref(v___x_4826_);
v_a_4780_ = v_a_4829_;
goto v___jp_4779_;
}
}
else
{
lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4830_ = lean_box(0);
lean_inc_ref(v_b_4761_);
v___x_4831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4761_, v___x_4816_, v___x_4830_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
lean_dec(v___x_4816_);
v___y_4784_ = v___x_4831_;
goto v___jp_4783_;
}
}
}
}
else
{
lean_object* v___x_4832_; lean_object* v___x_4833_; uint8_t v___x_4834_; 
v___x_4832_ = lean_unsigned_to_nat(1u);
v___x_4833_ = l_Lean_Syntax_getArg(v___x_4800_, v___x_4832_);
v___x_4834_ = l_Lean_Syntax_isNone(v___x_4833_);
if (v___x_4834_ == 0)
{
uint8_t v___x_4835_; 
lean_inc(v___x_4833_);
v___x_4835_ = l_Lean_Syntax_matchesNull(v___x_4833_, v___x_4832_);
if (v___x_4835_ == 0)
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
lean_dec(v___x_4833_);
lean_dec(v___x_4800_);
v___x_4836_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4790_);
v___x_4837_ = l_Lean_MessageData_ofSyntax(v_a_4790_);
v___x_4838_ = l_Lean_indentD(v___x_4837_);
v___x_4839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4839_, 0, v___x_4836_);
lean_ctor_set(v___x_4839_, 1, v___x_4838_);
v___x_4840_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4839_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_dec_ref(v___x_4840_);
v_snd_4770_ = v_b_4761_;
goto v___jp_4769_;
}
else
{
lean_object* v_a_4841_; 
v_a_4841_ = lean_ctor_get(v___x_4840_, 0);
lean_inc(v_a_4841_);
lean_dec_ref(v___x_4840_);
v_a_4780_ = v_a_4841_;
goto v___jp_4779_;
}
}
else
{
lean_object* v___x_4842_; lean_object* v___x_4843_; uint8_t v___x_4844_; 
v___x_4842_ = l_Lean_Syntax_getArg(v___x_4833_, v___x_4799_);
lean_dec(v___x_4833_);
v___x_4843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4842_);
v___x_4844_ = l_Lean_Syntax_isOfKind(v___x_4842_, v___x_4843_);
if (v___x_4844_ == 0)
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
lean_dec(v___x_4842_);
lean_dec(v___x_4800_);
v___x_4845_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4790_);
v___x_4846_ = l_Lean_MessageData_ofSyntax(v_a_4790_);
v___x_4847_ = l_Lean_indentD(v___x_4846_);
v___x_4848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4845_);
lean_ctor_set(v___x_4848_, 1, v___x_4847_);
v___x_4849_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4848_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_dec_ref(v___x_4849_);
v_snd_4770_ = v_b_4761_;
goto v___jp_4769_;
}
else
{
lean_object* v_a_4850_; 
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
lean_inc(v_a_4850_);
lean_dec_ref(v___x_4849_);
v_a_4780_ = v_a_4850_;
goto v___jp_4779_;
}
}
else
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4851_ = lean_box(0);
v___x_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4842_);
lean_inc(v_a_4790_);
lean_inc_ref(v_b_4761_);
v___x_4853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4800_, v_b_4761_, v_a_4790_, v___x_4788_, v_only_4756_, v_incremental_4757_, v___x_4851_, v___x_4852_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
lean_dec(v___x_4800_);
v___y_4784_ = v___x_4853_;
goto v___jp_4783_;
}
}
}
else
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
lean_dec(v___x_4833_);
v___x_4854_ = lean_box(0);
v___x_4855_ = lean_box(0);
lean_inc(v_a_4790_);
lean_inc_ref(v_b_4761_);
v___x_4856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4800_, v_b_4761_, v_a_4790_, v___x_4788_, v_only_4756_, v_incremental_4757_, v___x_4854_, v___x_4855_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
lean_dec(v___x_4800_);
v___y_4784_ = v___x_4856_;
goto v___jp_4783_;
}
}
}
else
{
lean_object* v___x_4857_; uint8_t v___x_4858_; 
v___x_4857_ = l_Lean_Syntax_getArg(v___x_4800_, v___x_4799_);
v___x_4858_ = l_Lean_Syntax_isNone(v___x_4857_);
if (v___x_4858_ == 0)
{
lean_object* v___x_4859_; uint8_t v___x_4860_; 
v___x_4859_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4857_);
v___x_4860_ = l_Lean_Syntax_matchesNull(v___x_4857_, v___x_4859_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
lean_dec(v___x_4857_);
lean_dec(v___x_4800_);
v___x_4861_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4790_);
v___x_4862_ = l_Lean_MessageData_ofSyntax(v_a_4790_);
v___x_4863_ = l_Lean_indentD(v___x_4862_);
v___x_4864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4861_);
lean_ctor_set(v___x_4864_, 1, v___x_4863_);
v___x_4865_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4864_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_dec_ref(v___x_4865_);
v_snd_4770_ = v_b_4761_;
goto v___jp_4769_;
}
else
{
lean_object* v_a_4866_; 
v_a_4866_ = lean_ctor_get(v___x_4865_, 0);
lean_inc(v_a_4866_);
lean_dec_ref(v___x_4865_);
v_a_4780_ = v_a_4866_;
goto v___jp_4779_;
}
}
else
{
lean_object* v___x_4867_; lean_object* v___x_4868_; uint8_t v___x_4869_; 
v___x_4867_ = l_Lean_Syntax_getArg(v___x_4857_, v___x_4799_);
lean_dec(v___x_4857_);
v___x_4868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4867_);
v___x_4869_ = l_Lean_Syntax_isOfKind(v___x_4867_, v___x_4868_);
if (v___x_4869_ == 0)
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
lean_dec(v___x_4867_);
lean_dec(v___x_4800_);
v___x_4870_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4790_);
v___x_4871_ = l_Lean_MessageData_ofSyntax(v_a_4790_);
v___x_4872_ = l_Lean_indentD(v___x_4871_);
v___x_4873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4870_);
lean_ctor_set(v___x_4873_, 1, v___x_4872_);
v___x_4874_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4873_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_dec_ref(v___x_4874_);
v_snd_4770_ = v_b_4761_;
goto v___jp_4769_;
}
else
{
lean_object* v_a_4875_; 
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
lean_inc(v_a_4875_);
lean_dec_ref(v___x_4874_);
v_a_4780_ = v_a_4875_;
goto v___jp_4779_;
}
}
else
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4876_ = lean_box(0);
v___x_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4867_);
lean_inc(v_a_4790_);
lean_inc_ref(v_b_4761_);
v___x_4878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4800_, v_b_4761_, v_a_4790_, v___x_4802_, v_only_4756_, v_incremental_4757_, v___x_4876_, v___x_4877_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
lean_dec(v___x_4800_);
v___y_4784_ = v___x_4878_;
goto v___jp_4783_;
}
}
}
else
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
lean_dec(v___x_4857_);
v___x_4879_ = lean_box(0);
v___x_4880_ = lean_box(0);
lean_inc(v_a_4790_);
lean_inc_ref(v_b_4761_);
v___x_4881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4800_, v_b_4761_, v_a_4790_, v___x_4802_, v_only_4756_, v_incremental_4757_, v___x_4879_, v___x_4880_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
lean_dec(v___x_4800_);
v___y_4784_ = v___x_4881_;
goto v___jp_4783_;
}
}
}
else
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; uint8_t v___x_4885_; 
v___x_4882_ = lean_unsigned_to_nat(1u);
v___x_4883_ = l_Lean_Syntax_getArg(v___x_4800_, v___x_4882_);
lean_dec(v___x_4800_);
v___x_4884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4883_);
v___x_4885_ = l_Lean_Syntax_isOfKind(v___x_4883_, v___x_4884_);
if (v___x_4885_ == 0)
{
lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
lean_dec(v___x_4883_);
v___x_4886_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4790_);
v___x_4887_ = l_Lean_MessageData_ofSyntax(v_a_4790_);
v___x_4888_ = l_Lean_indentD(v___x_4887_);
v___x_4889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4886_);
lean_ctor_set(v___x_4889_, 1, v___x_4888_);
v___x_4890_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4889_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_dec_ref(v___x_4890_);
v_snd_4770_ = v_b_4761_;
goto v___jp_4769_;
}
else
{
lean_object* v_a_4891_; 
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_a_4891_);
lean_dec_ref(v___x_4890_);
v_a_4780_ = v_a_4891_;
goto v___jp_4779_;
}
}
else
{
if (v_incremental_4757_ == 0)
{
lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___x_4892_ = lean_box(0);
lean_inc_ref(v_b_4761_);
v___x_4893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4883_, v_b_4761_, v___x_4892_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
v___y_4784_ = v___x_4893_;
goto v___jp_4783_;
}
else
{
lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4894_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_4895_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_4790_, v___x_4894_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; lean_object* v___x_4897_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
lean_inc(v_a_4896_);
lean_dec_ref(v___x_4895_);
lean_inc_ref(v_b_4761_);
v___x_4897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4883_, v_b_4761_, v_a_4896_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
v___y_4784_ = v___x_4897_;
goto v___jp_4783_;
}
else
{
lean_object* v_a_4898_; 
lean_dec(v___x_4883_);
v_a_4898_ = lean_ctor_get(v___x_4895_, 0);
lean_inc(v_a_4898_);
lean_dec_ref(v___x_4895_);
v_a_4780_ = v_a_4898_;
goto v___jp_4779_;
}
}
}
}
}
}
v___jp_4769_:
{
size_t v___x_4771_; size_t v___x_4772_; 
v___x_4771_ = ((size_t)1ULL);
v___x_4772_ = lean_usize_add(v_i_4760_, v___x_4771_);
v_i_4760_ = v___x_4772_;
v_b_4761_ = v_snd_4770_;
goto _start;
}
v___jp_4774_:
{
if (v___y_4776_ == 0)
{
if (v_lax_4755_ == 0)
{
lean_object* v___x_4777_; 
lean_dec_ref(v_b_4761_);
v___x_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4777_, 0, v___y_4775_);
return v___x_4777_;
}
else
{
lean_dec_ref(v___y_4775_);
v_snd_4770_ = v_b_4761_;
goto v___jp_4769_;
}
}
else
{
lean_object* v___x_4778_; 
lean_dec_ref(v_b_4761_);
v___x_4778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4778_, 0, v___y_4775_);
return v___x_4778_;
}
}
v___jp_4779_:
{
uint8_t v___x_4781_; 
v___x_4781_ = l_Lean_Exception_isInterrupt(v_a_4780_);
if (v___x_4781_ == 0)
{
uint8_t v___x_4782_; 
lean_inc_ref(v_a_4780_);
v___x_4782_ = l_Lean_Exception_isRuntime(v_a_4780_);
v___y_4775_ = v_a_4780_;
v___y_4776_ = v___x_4782_;
goto v___jp_4774_;
}
else
{
v___y_4775_ = v_a_4780_;
v___y_4776_ = v___x_4781_;
goto v___jp_4774_;
}
}
v___jp_4783_:
{
if (lean_obj_tag(v___y_4784_) == 0)
{
lean_object* v_a_4785_; lean_object* v_snd_4786_; 
lean_dec_ref(v_b_4761_);
v_a_4785_ = lean_ctor_get(v___y_4784_, 0);
lean_inc(v_a_4785_);
lean_dec_ref(v___y_4784_);
v_snd_4786_ = lean_ctor_get(v_a_4785_, 1);
lean_inc(v_snd_4786_);
lean_dec(v_a_4785_);
v_snd_4770_ = v_snd_4786_;
goto v___jp_4769_;
}
else
{
lean_object* v_a_4787_; 
v_a_4787_ = lean_ctor_get(v___y_4784_, 0);
lean_inc(v_a_4787_);
lean_dec_ref(v___y_4784_);
v_a_4780_ = v_a_4787_;
goto v___jp_4779_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_4899_, lean_object* v_only_4900_, lean_object* v_incremental_4901_, lean_object* v_as_4902_, lean_object* v_sz_4903_, lean_object* v_i_4904_, lean_object* v_b_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
uint8_t v_lax_boxed_4913_; uint8_t v_only_boxed_4914_; uint8_t v_incremental_boxed_4915_; size_t v_sz_boxed_4916_; size_t v_i_boxed_4917_; lean_object* v_res_4918_; 
v_lax_boxed_4913_ = lean_unbox(v_lax_4899_);
v_only_boxed_4914_ = lean_unbox(v_only_4900_);
v_incremental_boxed_4915_ = lean_unbox(v_incremental_4901_);
v_sz_boxed_4916_ = lean_unbox_usize(v_sz_4903_);
lean_dec(v_sz_4903_);
v_i_boxed_4917_ = lean_unbox_usize(v_i_4904_);
lean_dec(v_i_4904_);
v_res_4918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_4913_, v_only_boxed_4914_, v_incremental_boxed_4915_, v_as_4902_, v_sz_boxed_4916_, v_i_boxed_4917_, v_b_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_);
lean_dec(v___y_4911_);
lean_dec_ref(v___y_4910_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
lean_dec_ref(v_as_4902_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_4919_, lean_object* v_ps_4920_, uint8_t v_only_4921_, uint8_t v_lax_4922_, uint8_t v_incremental_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_){
_start:
{
size_t v_sz_4931_; size_t v___x_4932_; lean_object* v___x_4933_; 
v_sz_4931_ = lean_array_size(v_ps_4920_);
v___x_4932_ = ((size_t)0ULL);
v___x_4933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_4922_, v_only_4921_, v_incremental_4923_, v_ps_4920_, v_sz_4931_, v___x_4932_, v_params_4919_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_4934_, lean_object* v_ps_4935_, lean_object* v_only_4936_, lean_object* v_lax_4937_, lean_object* v_incremental_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_){
_start:
{
uint8_t v_only_boxed_4946_; uint8_t v_lax_boxed_4947_; uint8_t v_incremental_boxed_4948_; lean_object* v_res_4949_; 
v_only_boxed_4946_ = lean_unbox(v_only_4936_);
v_lax_boxed_4947_ = lean_unbox(v_lax_4937_);
v_incremental_boxed_4948_ = lean_unbox(v_incremental_4938_);
v_res_4949_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_4934_, v_ps_4935_, v_only_boxed_4946_, v_lax_boxed_4947_, v_incremental_boxed_4948_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
lean_dec(v_a_4944_);
lean_dec_ref(v_a_4943_);
lean_dec(v_a_4942_);
lean_dec_ref(v_a_4941_);
lean_dec(v_a_4940_);
lean_dec_ref(v_a_4939_);
lean_dec_ref(v_ps_4935_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_){
_start:
{
lean_object* v_origin_4961_; 
v_origin_4961_ = lean_ctor_get(v_thm_4950_, 5);
if (lean_obj_tag(v_origin_4961_) == 0)
{
lean_object* v_declName_4962_; lean_object* v___x_4963_; 
lean_inc_ref(v_origin_4961_);
lean_dec_ref(v_thm_4950_);
v_declName_4962_ = lean_ctor_get(v_origin_4961_, 0);
lean_inc(v_declName_4962_);
lean_dec_ref(v_origin_4961_);
v___x_4963_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_4962_, v_a_4958_, v_a_4959_);
return v___x_4963_;
}
else
{
lean_object* v_proof_4964_; lean_object* v___x_4965_; 
v_proof_4964_ = lean_ctor_get(v_thm_4950_, 1);
lean_inc_ref(v_proof_4964_);
lean_dec_ref(v_thm_4950_);
v___x_4965_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_4964_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_);
return v___x_4965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_);
lean_dec(v_a_4975_);
lean_dec_ref(v_a_4974_);
lean_dec(v_a_4973_);
lean_dec_ref(v_a_4972_);
lean_dec(v_a_4971_);
lean_dec_ref(v_a_4970_);
lean_dec(v_a_4969_);
lean_dec_ref(v_a_4968_);
lean_dec(v_a_4967_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_4978_, size_t v_sz_4979_, size_t v_i_4980_, lean_object* v_b_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_){
_start:
{
uint8_t v___x_4992_; 
v___x_4992_ = lean_usize_dec_lt(v_i_4980_, v_sz_4979_);
if (v___x_4992_ == 0)
{
lean_object* v___x_4993_; 
v___x_4993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4993_, 0, v_b_4981_);
return v___x_4993_;
}
else
{
lean_object* v_snd_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5020_; 
v_snd_4994_ = lean_ctor_get(v_b_4981_, 1);
v_isSharedCheck_5020_ = !lean_is_exclusive(v_b_4981_);
if (v_isSharedCheck_5020_ == 0)
{
lean_object* v_unused_5021_; 
v_unused_5021_ = lean_ctor_get(v_b_4981_, 0);
lean_dec(v_unused_5021_);
v___x_4996_ = v_b_4981_;
v_isShared_4997_ = v_isSharedCheck_5020_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_snd_4994_);
lean_dec(v_b_4981_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5020_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v_a_4998_; lean_object* v___x_4999_; 
v_a_4998_ = lean_array_uget_borrowed(v_as_4978_, v_i_4980_);
lean_inc(v_a_4998_);
v___x_4999_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_4998_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_object* v_a_5000_; lean_object* v___x_5001_; lean_object* v_a_5003_; uint8_t v___x_5010_; 
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
lean_inc(v_a_5000_);
lean_dec_ref(v___x_4999_);
v___x_5001_ = lean_box(0);
v___x_5010_ = lean_unbox(v_a_5000_);
lean_dec(v_a_5000_);
if (v___x_5010_ == 0)
{
v_a_5003_ = v_snd_4994_;
goto v___jp_5002_;
}
else
{
lean_object* v___x_5011_; 
lean_inc(v_a_4998_);
v___x_5011_ = l_Lean_PersistentArray_push___redArg(v_snd_4994_, v_a_4998_);
v_a_5003_ = v___x_5011_;
goto v___jp_5002_;
}
v___jp_5002_:
{
lean_object* v___x_5005_; 
if (v_isShared_4997_ == 0)
{
lean_ctor_set(v___x_4996_, 1, v_a_5003_);
lean_ctor_set(v___x_4996_, 0, v___x_5001_);
v___x_5005_ = v___x_4996_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v___x_5001_);
lean_ctor_set(v_reuseFailAlloc_5009_, 1, v_a_5003_);
v___x_5005_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
size_t v___x_5006_; size_t v___x_5007_; 
v___x_5006_ = ((size_t)1ULL);
v___x_5007_ = lean_usize_add(v_i_4980_, v___x_5006_);
v_i_4980_ = v___x_5007_;
v_b_4981_ = v___x_5005_;
goto _start;
}
}
}
else
{
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
lean_del_object(v___x_4996_);
lean_dec(v_snd_4994_);
v_a_5012_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_5014_ = v___x_4999_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_4999_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5022_, lean_object* v_sz_5023_, lean_object* v_i_5024_, lean_object* v_b_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
size_t v_sz_boxed_5036_; size_t v_i_boxed_5037_; lean_object* v_res_5038_; 
v_sz_boxed_5036_ = lean_unbox_usize(v_sz_5023_);
lean_dec(v_sz_5023_);
v_i_boxed_5037_ = lean_unbox_usize(v_i_5024_);
lean_dec(v_i_5024_);
v_res_5038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5022_, v_sz_boxed_5036_, v_i_boxed_5037_, v_b_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec(v___y_5028_);
lean_dec_ref(v___y_5027_);
lean_dec(v___y_5026_);
lean_dec_ref(v_as_5022_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5039_, size_t v_sz_5040_, size_t v_i_5041_, lean_object* v_b_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_){
_start:
{
uint8_t v___x_5053_; 
v___x_5053_ = lean_usize_dec_lt(v_i_5041_, v_sz_5040_);
if (v___x_5053_ == 0)
{
lean_object* v___x_5054_; 
v___x_5054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5054_, 0, v_b_5042_);
return v___x_5054_;
}
else
{
lean_object* v_snd_5055_; lean_object* v___x_5057_; uint8_t v_isShared_5058_; uint8_t v_isSharedCheck_5081_; 
v_snd_5055_ = lean_ctor_get(v_b_5042_, 1);
v_isSharedCheck_5081_ = !lean_is_exclusive(v_b_5042_);
if (v_isSharedCheck_5081_ == 0)
{
lean_object* v_unused_5082_; 
v_unused_5082_ = lean_ctor_get(v_b_5042_, 0);
lean_dec(v_unused_5082_);
v___x_5057_ = v_b_5042_;
v_isShared_5058_ = v_isSharedCheck_5081_;
goto v_resetjp_5056_;
}
else
{
lean_inc(v_snd_5055_);
lean_dec(v_b_5042_);
v___x_5057_ = lean_box(0);
v_isShared_5058_ = v_isSharedCheck_5081_;
goto v_resetjp_5056_;
}
v_resetjp_5056_:
{
lean_object* v_a_5059_; lean_object* v___x_5060_; 
v_a_5059_ = lean_array_uget_borrowed(v_as_5039_, v_i_5041_);
lean_inc(v_a_5059_);
v___x_5060_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5059_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; lean_object* v___x_5062_; lean_object* v_a_5064_; uint8_t v___x_5071_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5061_);
lean_dec_ref(v___x_5060_);
v___x_5062_ = lean_box(0);
v___x_5071_ = lean_unbox(v_a_5061_);
lean_dec(v_a_5061_);
if (v___x_5071_ == 0)
{
v_a_5064_ = v_snd_5055_;
goto v___jp_5063_;
}
else
{
lean_object* v___x_5072_; 
lean_inc(v_a_5059_);
v___x_5072_ = l_Lean_PersistentArray_push___redArg(v_snd_5055_, v_a_5059_);
v_a_5064_ = v___x_5072_;
goto v___jp_5063_;
}
v___jp_5063_:
{
lean_object* v___x_5066_; 
if (v_isShared_5058_ == 0)
{
lean_ctor_set(v___x_5057_, 1, v_a_5064_);
lean_ctor_set(v___x_5057_, 0, v___x_5062_);
v___x_5066_ = v___x_5057_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v___x_5062_);
lean_ctor_set(v_reuseFailAlloc_5070_, 1, v_a_5064_);
v___x_5066_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
size_t v___x_5067_; size_t v___x_5068_; lean_object* v___x_5069_; 
v___x_5067_ = ((size_t)1ULL);
v___x_5068_ = lean_usize_add(v_i_5041_, v___x_5067_);
v___x_5069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5039_, v_sz_5040_, v___x_5068_, v___x_5066_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_);
return v___x_5069_;
}
}
}
else
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5080_; 
lean_del_object(v___x_5057_);
lean_dec(v_snd_5055_);
v_a_5073_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5060_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5060_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5083_, lean_object* v_sz_5084_, lean_object* v_i_5085_, lean_object* v_b_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_){
_start:
{
size_t v_sz_boxed_5097_; size_t v_i_boxed_5098_; lean_object* v_res_5099_; 
v_sz_boxed_5097_ = lean_unbox_usize(v_sz_5084_);
lean_dec(v_sz_5084_);
v_i_boxed_5098_ = lean_unbox_usize(v_i_5085_);
lean_dec(v_i_5085_);
v_res_5099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5083_, v_sz_boxed_5097_, v_i_boxed_5098_, v_b_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec(v___y_5091_);
lean_dec_ref(v___y_5090_);
lean_dec(v___y_5089_);
lean_dec_ref(v___y_5088_);
lean_dec(v___y_5087_);
lean_dec_ref(v_as_5083_);
return v_res_5099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5100_, size_t v_sz_5101_, size_t v_i_5102_, lean_object* v_b_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_){
_start:
{
uint8_t v___x_5114_; 
v___x_5114_ = lean_usize_dec_lt(v_i_5102_, v_sz_5101_);
if (v___x_5114_ == 0)
{
lean_object* v___x_5115_; 
v___x_5115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5115_, 0, v_b_5103_);
return v___x_5115_;
}
else
{
lean_object* v_snd_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5142_; 
v_snd_5116_ = lean_ctor_get(v_b_5103_, 1);
v_isSharedCheck_5142_ = !lean_is_exclusive(v_b_5103_);
if (v_isSharedCheck_5142_ == 0)
{
lean_object* v_unused_5143_; 
v_unused_5143_ = lean_ctor_get(v_b_5103_, 0);
lean_dec(v_unused_5143_);
v___x_5118_ = v_b_5103_;
v_isShared_5119_ = v_isSharedCheck_5142_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_snd_5116_);
lean_dec(v_b_5103_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5142_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v_a_5120_; lean_object* v___x_5121_; 
v_a_5120_ = lean_array_uget_borrowed(v_as_5100_, v_i_5102_);
lean_inc(v_a_5120_);
v___x_5121_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5120_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
if (lean_obj_tag(v___x_5121_) == 0)
{
lean_object* v_a_5122_; lean_object* v___x_5123_; lean_object* v_a_5125_; uint8_t v___x_5132_; 
v_a_5122_ = lean_ctor_get(v___x_5121_, 0);
lean_inc(v_a_5122_);
lean_dec_ref(v___x_5121_);
v___x_5123_ = lean_box(0);
v___x_5132_ = lean_unbox(v_a_5122_);
lean_dec(v_a_5122_);
if (v___x_5132_ == 0)
{
v_a_5125_ = v_snd_5116_;
goto v___jp_5124_;
}
else
{
lean_object* v___x_5133_; 
lean_inc(v_a_5120_);
v___x_5133_ = l_Lean_PersistentArray_push___redArg(v_snd_5116_, v_a_5120_);
v_a_5125_ = v___x_5133_;
goto v___jp_5124_;
}
v___jp_5124_:
{
lean_object* v___x_5127_; 
if (v_isShared_5119_ == 0)
{
lean_ctor_set(v___x_5118_, 1, v_a_5125_);
lean_ctor_set(v___x_5118_, 0, v___x_5123_);
v___x_5127_ = v___x_5118_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v___x_5123_);
lean_ctor_set(v_reuseFailAlloc_5131_, 1, v_a_5125_);
v___x_5127_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
size_t v___x_5128_; size_t v___x_5129_; 
v___x_5128_ = ((size_t)1ULL);
v___x_5129_ = lean_usize_add(v_i_5102_, v___x_5128_);
v_i_5102_ = v___x_5129_;
v_b_5103_ = v___x_5127_;
goto _start;
}
}
}
else
{
lean_object* v_a_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5141_; 
lean_del_object(v___x_5118_);
lean_dec(v_snd_5116_);
v_a_5134_ = lean_ctor_get(v___x_5121_, 0);
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5121_);
if (v_isSharedCheck_5141_ == 0)
{
v___x_5136_ = v___x_5121_;
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_a_5134_);
lean_dec(v___x_5121_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5139_; 
if (v_isShared_5137_ == 0)
{
v___x_5139_ = v___x_5136_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v_a_5134_);
v___x_5139_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
return v___x_5139_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5144_, lean_object* v_sz_5145_, lean_object* v_i_5146_, lean_object* v_b_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
size_t v_sz_boxed_5158_; size_t v_i_boxed_5159_; lean_object* v_res_5160_; 
v_sz_boxed_5158_ = lean_unbox_usize(v_sz_5145_);
lean_dec(v_sz_5145_);
v_i_boxed_5159_ = lean_unbox_usize(v_i_5146_);
lean_dec(v_i_5146_);
v_res_5160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5144_, v_sz_boxed_5158_, v_i_boxed_5159_, v_b_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_);
lean_dec(v___y_5156_);
lean_dec_ref(v___y_5155_);
lean_dec(v___y_5154_);
lean_dec_ref(v___y_5153_);
lean_dec(v___y_5152_);
lean_dec_ref(v___y_5151_);
lean_dec(v___y_5150_);
lean_dec_ref(v___y_5149_);
lean_dec(v___y_5148_);
lean_dec_ref(v_as_5144_);
return v_res_5160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5161_, size_t v_sz_5162_, size_t v_i_5163_, lean_object* v_b_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_){
_start:
{
uint8_t v___x_5175_; 
v___x_5175_ = lean_usize_dec_lt(v_i_5163_, v_sz_5162_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; 
v___x_5176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5176_, 0, v_b_5164_);
return v___x_5176_;
}
else
{
lean_object* v_snd_5177_; lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5203_; 
v_snd_5177_ = lean_ctor_get(v_b_5164_, 1);
v_isSharedCheck_5203_ = !lean_is_exclusive(v_b_5164_);
if (v_isSharedCheck_5203_ == 0)
{
lean_object* v_unused_5204_; 
v_unused_5204_ = lean_ctor_get(v_b_5164_, 0);
lean_dec(v_unused_5204_);
v___x_5179_ = v_b_5164_;
v_isShared_5180_ = v_isSharedCheck_5203_;
goto v_resetjp_5178_;
}
else
{
lean_inc(v_snd_5177_);
lean_dec(v_b_5164_);
v___x_5179_ = lean_box(0);
v_isShared_5180_ = v_isSharedCheck_5203_;
goto v_resetjp_5178_;
}
v_resetjp_5178_:
{
lean_object* v_a_5181_; lean_object* v___x_5182_; 
v_a_5181_ = lean_array_uget_borrowed(v_as_5161_, v_i_5163_);
lean_inc(v_a_5181_);
v___x_5182_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5181_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v_a_5183_; lean_object* v___x_5184_; lean_object* v_a_5186_; uint8_t v___x_5193_; 
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
lean_inc(v_a_5183_);
lean_dec_ref(v___x_5182_);
v___x_5184_ = lean_box(0);
v___x_5193_ = lean_unbox(v_a_5183_);
lean_dec(v_a_5183_);
if (v___x_5193_ == 0)
{
v_a_5186_ = v_snd_5177_;
goto v___jp_5185_;
}
else
{
lean_object* v___x_5194_; 
lean_inc(v_a_5181_);
v___x_5194_ = l_Lean_PersistentArray_push___redArg(v_snd_5177_, v_a_5181_);
v_a_5186_ = v___x_5194_;
goto v___jp_5185_;
}
v___jp_5185_:
{
lean_object* v___x_5188_; 
if (v_isShared_5180_ == 0)
{
lean_ctor_set(v___x_5179_, 1, v_a_5186_);
lean_ctor_set(v___x_5179_, 0, v___x_5184_);
v___x_5188_ = v___x_5179_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v___x_5184_);
lean_ctor_set(v_reuseFailAlloc_5192_, 1, v_a_5186_);
v___x_5188_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
size_t v___x_5189_; size_t v___x_5190_; lean_object* v___x_5191_; 
v___x_5189_ = ((size_t)1ULL);
v___x_5190_ = lean_usize_add(v_i_5163_, v___x_5189_);
v___x_5191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5161_, v_sz_5162_, v___x_5190_, v___x_5188_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
return v___x_5191_;
}
}
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
lean_del_object(v___x_5179_);
lean_dec(v_snd_5177_);
v_a_5195_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5197_ = v___x_5182_;
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_a_5195_);
lean_dec(v___x_5182_);
v___x_5197_ = lean_box(0);
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
v_resetjp_5196_:
{
lean_object* v___x_5200_; 
if (v_isShared_5198_ == 0)
{
v___x_5200_ = v___x_5197_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_a_5195_);
v___x_5200_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
return v___x_5200_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5205_, lean_object* v_sz_5206_, lean_object* v_i_5207_, lean_object* v_b_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_){
_start:
{
size_t v_sz_boxed_5219_; size_t v_i_boxed_5220_; lean_object* v_res_5221_; 
v_sz_boxed_5219_ = lean_unbox_usize(v_sz_5206_);
lean_dec(v_sz_5206_);
v_i_boxed_5220_ = lean_unbox_usize(v_i_5207_);
lean_dec(v_i_5207_);
v_res_5221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5205_, v_sz_boxed_5219_, v_i_boxed_5220_, v_b_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
lean_dec(v___y_5211_);
lean_dec_ref(v___y_5210_);
lean_dec(v___y_5209_);
lean_dec_ref(v_as_5205_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5222_, lean_object* v_n_5223_, lean_object* v_b_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_){
_start:
{
if (lean_obj_tag(v_n_5223_) == 0)
{
lean_object* v_cs_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; size_t v_sz_5238_; size_t v___x_5239_; lean_object* v___x_5240_; 
v_cs_5235_ = lean_ctor_get(v_n_5223_, 0);
v___x_5236_ = lean_box(0);
v___x_5237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5237_, 0, v___x_5236_);
lean_ctor_set(v___x_5237_, 1, v_b_5224_);
v_sz_5238_ = lean_array_size(v_cs_5235_);
v___x_5239_ = ((size_t)0ULL);
v___x_5240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5222_, v_cs_5235_, v_sz_5238_, v___x_5239_, v___x_5237_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_);
if (lean_obj_tag(v___x_5240_) == 0)
{
lean_object* v_a_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5255_; 
v_a_5241_ = lean_ctor_get(v___x_5240_, 0);
v_isSharedCheck_5255_ = !lean_is_exclusive(v___x_5240_);
if (v_isSharedCheck_5255_ == 0)
{
v___x_5243_ = v___x_5240_;
v_isShared_5244_ = v_isSharedCheck_5255_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_a_5241_);
lean_dec(v___x_5240_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5255_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v_fst_5245_; 
v_fst_5245_ = lean_ctor_get(v_a_5241_, 0);
if (lean_obj_tag(v_fst_5245_) == 0)
{
lean_object* v_snd_5246_; lean_object* v___x_5247_; lean_object* v___x_5249_; 
v_snd_5246_ = lean_ctor_get(v_a_5241_, 1);
lean_inc(v_snd_5246_);
lean_dec(v_a_5241_);
v___x_5247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5247_, 0, v_snd_5246_);
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 0, v___x_5247_);
v___x_5249_ = v___x_5243_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v___x_5247_);
v___x_5249_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
return v___x_5249_;
}
}
else
{
lean_object* v_val_5251_; lean_object* v___x_5253_; 
lean_inc_ref(v_fst_5245_);
lean_dec(v_a_5241_);
v_val_5251_ = lean_ctor_get(v_fst_5245_, 0);
lean_inc(v_val_5251_);
lean_dec_ref(v_fst_5245_);
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 0, v_val_5251_);
v___x_5253_ = v___x_5243_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_val_5251_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
}
else
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5263_; 
v_a_5256_ = lean_ctor_get(v___x_5240_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5240_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5258_ = v___x_5240_;
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5240_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5263_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5261_; 
if (v_isShared_5259_ == 0)
{
v___x_5261_ = v___x_5258_;
goto v_reusejp_5260_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
v___x_5261_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5260_;
}
v_reusejp_5260_:
{
return v___x_5261_;
}
}
}
}
else
{
lean_object* v_vs_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; size_t v_sz_5267_; size_t v___x_5268_; lean_object* v___x_5269_; 
v_vs_5264_ = lean_ctor_get(v_n_5223_, 0);
v___x_5265_ = lean_box(0);
v___x_5266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5266_, 0, v___x_5265_);
lean_ctor_set(v___x_5266_, 1, v_b_5224_);
v_sz_5267_ = lean_array_size(v_vs_5264_);
v___x_5268_ = ((size_t)0ULL);
v___x_5269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5264_, v_sz_5267_, v___x_5268_, v___x_5266_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_);
if (lean_obj_tag(v___x_5269_) == 0)
{
lean_object* v_a_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5284_; 
v_a_5270_ = lean_ctor_get(v___x_5269_, 0);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5269_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5272_ = v___x_5269_;
v_isShared_5273_ = v_isSharedCheck_5284_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_a_5270_);
lean_dec(v___x_5269_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5284_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v_fst_5274_; 
v_fst_5274_ = lean_ctor_get(v_a_5270_, 0);
if (lean_obj_tag(v_fst_5274_) == 0)
{
lean_object* v_snd_5275_; lean_object* v___x_5276_; lean_object* v___x_5278_; 
v_snd_5275_ = lean_ctor_get(v_a_5270_, 1);
lean_inc(v_snd_5275_);
lean_dec(v_a_5270_);
v___x_5276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5276_, 0, v_snd_5275_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 0, v___x_5276_);
v___x_5278_ = v___x_5272_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___x_5276_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
return v___x_5278_;
}
}
else
{
lean_object* v_val_5280_; lean_object* v___x_5282_; 
lean_inc_ref(v_fst_5274_);
lean_dec(v_a_5270_);
v_val_5280_ = lean_ctor_get(v_fst_5274_, 0);
lean_inc(v_val_5280_);
lean_dec_ref(v_fst_5274_);
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 0, v_val_5280_);
v___x_5282_ = v___x_5272_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_val_5280_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
}
else
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5292_; 
v_a_5285_ = lean_ctor_get(v___x_5269_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5269_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5287_ = v___x_5269_;
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5269_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5290_; 
if (v_isShared_5288_ == 0)
{
v___x_5290_ = v___x_5287_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5285_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5293_, lean_object* v_as_5294_, size_t v_sz_5295_, size_t v_i_5296_, lean_object* v_b_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_){
_start:
{
uint8_t v___x_5308_; 
v___x_5308_ = lean_usize_dec_lt(v_i_5296_, v_sz_5295_);
if (v___x_5308_ == 0)
{
lean_object* v___x_5309_; 
v___x_5309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5309_, 0, v_b_5297_);
return v___x_5309_;
}
else
{
lean_object* v_snd_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5344_; 
v_snd_5310_ = lean_ctor_get(v_b_5297_, 1);
v_isSharedCheck_5344_ = !lean_is_exclusive(v_b_5297_);
if (v_isSharedCheck_5344_ == 0)
{
lean_object* v_unused_5345_; 
v_unused_5345_ = lean_ctor_get(v_b_5297_, 0);
lean_dec(v_unused_5345_);
v___x_5312_ = v_b_5297_;
v_isShared_5313_ = v_isSharedCheck_5344_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_snd_5310_);
lean_dec(v_b_5297_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5344_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v_a_5314_; lean_object* v___x_5315_; 
v_a_5314_ = lean_array_uget_borrowed(v_as_5294_, v_i_5296_);
lean_inc(v_snd_5310_);
v___x_5315_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5293_, v_a_5314_, v_snd_5310_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_);
if (lean_obj_tag(v___x_5315_) == 0)
{
lean_object* v_a_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5335_; 
v_a_5316_ = lean_ctor_get(v___x_5315_, 0);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5318_ = v___x_5315_;
v_isShared_5319_ = v_isSharedCheck_5335_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_a_5316_);
lean_dec(v___x_5315_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5335_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
if (lean_obj_tag(v_a_5316_) == 0)
{
lean_object* v___x_5320_; lean_object* v___x_5322_; 
v___x_5320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5320_, 0, v_a_5316_);
if (v_isShared_5313_ == 0)
{
lean_ctor_set(v___x_5312_, 0, v___x_5320_);
v___x_5322_ = v___x_5312_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v___x_5320_);
lean_ctor_set(v_reuseFailAlloc_5326_, 1, v_snd_5310_);
v___x_5322_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
lean_object* v___x_5324_; 
if (v_isShared_5319_ == 0)
{
lean_ctor_set(v___x_5318_, 0, v___x_5322_);
v___x_5324_ = v___x_5318_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v___x_5322_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
}
else
{
lean_object* v_a_5327_; lean_object* v___x_5328_; lean_object* v___x_5330_; 
lean_del_object(v___x_5318_);
lean_dec(v_snd_5310_);
v_a_5327_ = lean_ctor_get(v_a_5316_, 0);
lean_inc(v_a_5327_);
lean_dec_ref(v_a_5316_);
v___x_5328_ = lean_box(0);
if (v_isShared_5313_ == 0)
{
lean_ctor_set(v___x_5312_, 1, v_a_5327_);
lean_ctor_set(v___x_5312_, 0, v___x_5328_);
v___x_5330_ = v___x_5312_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5328_);
lean_ctor_set(v_reuseFailAlloc_5334_, 1, v_a_5327_);
v___x_5330_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
size_t v___x_5331_; size_t v___x_5332_; 
v___x_5331_ = ((size_t)1ULL);
v___x_5332_ = lean_usize_add(v_i_5296_, v___x_5331_);
v_i_5296_ = v___x_5332_;
v_b_5297_ = v___x_5330_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5343_; 
lean_del_object(v___x_5312_);
lean_dec(v_snd_5310_);
v_a_5336_ = lean_ctor_get(v___x_5315_, 0);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5338_ = v___x_5315_;
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5315_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5341_; 
if (v_isShared_5339_ == 0)
{
v___x_5341_ = v___x_5338_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_a_5336_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
return v___x_5341_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5346_, lean_object* v_as_5347_, lean_object* v_sz_5348_, lean_object* v_i_5349_, lean_object* v_b_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_){
_start:
{
size_t v_sz_boxed_5361_; size_t v_i_boxed_5362_; lean_object* v_res_5363_; 
v_sz_boxed_5361_ = lean_unbox_usize(v_sz_5348_);
lean_dec(v_sz_5348_);
v_i_boxed_5362_ = lean_unbox_usize(v_i_5349_);
lean_dec(v_i_5349_);
v_res_5363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5346_, v_as_5347_, v_sz_boxed_5361_, v_i_boxed_5362_, v_b_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
lean_dec(v___y_5359_);
lean_dec_ref(v___y_5358_);
lean_dec(v___y_5357_);
lean_dec_ref(v___y_5356_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
lean_dec(v___y_5353_);
lean_dec_ref(v___y_5352_);
lean_dec(v___y_5351_);
lean_dec_ref(v_as_5347_);
lean_dec_ref(v_init_5346_);
return v_res_5363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5364_, lean_object* v_n_5365_, lean_object* v_b_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5364_, v_n_5365_, v_b_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_);
lean_dec(v___y_5375_);
lean_dec_ref(v___y_5374_);
lean_dec(v___y_5373_);
lean_dec_ref(v___y_5372_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
lean_dec(v___y_5369_);
lean_dec_ref(v___y_5368_);
lean_dec(v___y_5367_);
lean_dec_ref(v_n_5365_);
lean_dec_ref(v_init_5364_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5378_, lean_object* v_init_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_){
_start:
{
lean_object* v_root_5390_; lean_object* v_tail_5391_; lean_object* v___x_5392_; 
v_root_5390_ = lean_ctor_get(v_t_5378_, 0);
v_tail_5391_ = lean_ctor_get(v_t_5378_, 1);
lean_inc_ref(v_init_5379_);
v___x_5392_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5379_, v_root_5390_, v_init_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
lean_dec_ref(v_init_5379_);
if (lean_obj_tag(v___x_5392_) == 0)
{
lean_object* v_a_5393_; lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5429_; 
v_a_5393_ = lean_ctor_get(v___x_5392_, 0);
v_isSharedCheck_5429_ = !lean_is_exclusive(v___x_5392_);
if (v_isSharedCheck_5429_ == 0)
{
v___x_5395_ = v___x_5392_;
v_isShared_5396_ = v_isSharedCheck_5429_;
goto v_resetjp_5394_;
}
else
{
lean_inc(v_a_5393_);
lean_dec(v___x_5392_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5429_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
if (lean_obj_tag(v_a_5393_) == 0)
{
lean_object* v_a_5397_; lean_object* v___x_5399_; 
v_a_5397_ = lean_ctor_get(v_a_5393_, 0);
lean_inc(v_a_5397_);
lean_dec_ref(v_a_5393_);
if (v_isShared_5396_ == 0)
{
lean_ctor_set(v___x_5395_, 0, v_a_5397_);
v___x_5399_ = v___x_5395_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_a_5397_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
else
{
lean_object* v_a_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; size_t v_sz_5404_; size_t v___x_5405_; lean_object* v___x_5406_; 
lean_del_object(v___x_5395_);
v_a_5401_ = lean_ctor_get(v_a_5393_, 0);
lean_inc(v_a_5401_);
lean_dec_ref(v_a_5393_);
v___x_5402_ = lean_box(0);
v___x_5403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5403_, 0, v___x_5402_);
lean_ctor_set(v___x_5403_, 1, v_a_5401_);
v_sz_5404_ = lean_array_size(v_tail_5391_);
v___x_5405_ = ((size_t)0ULL);
v___x_5406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5391_, v_sz_5404_, v___x_5405_, v___x_5403_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
if (lean_obj_tag(v___x_5406_) == 0)
{
lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5420_; 
v_a_5407_ = lean_ctor_get(v___x_5406_, 0);
v_isSharedCheck_5420_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5420_ == 0)
{
v___x_5409_ = v___x_5406_;
v_isShared_5410_ = v_isSharedCheck_5420_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v___x_5406_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5420_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v_fst_5411_; 
v_fst_5411_ = lean_ctor_get(v_a_5407_, 0);
if (lean_obj_tag(v_fst_5411_) == 0)
{
lean_object* v_snd_5412_; lean_object* v___x_5414_; 
v_snd_5412_ = lean_ctor_get(v_a_5407_, 1);
lean_inc(v_snd_5412_);
lean_dec(v_a_5407_);
if (v_isShared_5410_ == 0)
{
lean_ctor_set(v___x_5409_, 0, v_snd_5412_);
v___x_5414_ = v___x_5409_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_snd_5412_);
v___x_5414_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
return v___x_5414_;
}
}
else
{
lean_object* v_val_5416_; lean_object* v___x_5418_; 
lean_inc_ref(v_fst_5411_);
lean_dec(v_a_5407_);
v_val_5416_ = lean_ctor_get(v_fst_5411_, 0);
lean_inc(v_val_5416_);
lean_dec_ref(v_fst_5411_);
if (v_isShared_5410_ == 0)
{
lean_ctor_set(v___x_5409_, 0, v_val_5416_);
v___x_5418_ = v___x_5409_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_val_5416_);
v___x_5418_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
return v___x_5418_;
}
}
}
}
else
{
lean_object* v_a_5421_; lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5428_; 
v_a_5421_ = lean_ctor_get(v___x_5406_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5423_ = v___x_5406_;
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
else
{
lean_inc(v_a_5421_);
lean_dec(v___x_5406_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v___x_5426_; 
if (v_isShared_5424_ == 0)
{
v___x_5426_ = v___x_5423_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
return v___x_5426_;
}
}
}
}
}
}
else
{
lean_object* v_a_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5437_; 
v_a_5430_ = lean_ctor_get(v___x_5392_, 0);
v_isSharedCheck_5437_ = !lean_is_exclusive(v___x_5392_);
if (v_isSharedCheck_5437_ == 0)
{
v___x_5432_ = v___x_5392_;
v_isShared_5433_ = v_isSharedCheck_5437_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_a_5430_);
lean_dec(v___x_5392_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5437_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
lean_object* v___x_5435_; 
if (v_isShared_5433_ == 0)
{
v___x_5435_ = v___x_5432_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v_a_5430_);
v___x_5435_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
return v___x_5435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5438_, lean_object* v_init_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_){
_start:
{
lean_object* v_res_5450_; 
v_res_5450_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5438_, v_init_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec(v___y_5446_);
lean_dec_ref(v___y_5445_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec_ref(v___y_5441_);
lean_dec(v___y_5440_);
lean_dec_ref(v_t_5438_);
return v_res_5450_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; 
v___x_5451_ = lean_unsigned_to_nat(32u);
v___x_5452_ = lean_mk_empty_array_with_capacity(v___x_5451_);
v___x_5453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5453_, 0, v___x_5452_);
return v___x_5453_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v_result_5459_; 
v___x_5454_ = ((size_t)5ULL);
v___x_5455_ = lean_unsigned_to_nat(0u);
v___x_5456_ = lean_unsigned_to_nat(32u);
v___x_5457_ = lean_mk_empty_array_with_capacity(v___x_5456_);
v___x_5458_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5459_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5459_, 0, v___x_5458_);
lean_ctor_set(v_result_5459_, 1, v___x_5457_);
lean_ctor_set(v_result_5459_, 2, v___x_5455_);
lean_ctor_set(v_result_5459_, 3, v___x_5455_);
lean_ctor_set_usize(v_result_5459_, 4, v___x_5454_);
return v_result_5459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_){
_start:
{
lean_object* v_result_5471_; lean_object* v___x_5472_; 
v_result_5471_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5472_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5460_, v_result_5471_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_);
return v___x_5472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_){
_start:
{
lean_object* v_res_5484_; 
v_res_5484_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5473_, v_a_5474_, v_a_5475_, v_a_5476_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_);
lean_dec(v_a_5482_);
lean_dec_ref(v_a_5481_);
lean_dec(v_a_5480_);
lean_dec_ref(v_a_5479_);
lean_dec(v_a_5478_);
lean_dec_ref(v_a_5477_);
lean_dec(v_a_5476_);
lean_dec_ref(v_a_5475_);
lean_dec(v_a_5474_);
lean_dec_ref(v_thms_5473_);
return v_res_5484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_5487_, lean_object* v_newThms_5488_, lean_object* v_gmt_5489_, lean_object* v_numInstances_5490_, lean_object* v_numDelayedInstances_5491_, lean_object* v_num_5492_, lean_object* v_preInstances_5493_, lean_object* v_nextThmIdx_5494_, lean_object* v_matchEqNames_5495_, lean_object* v_delayedThmInsts_5496_, lean_object* v_nextDeclIdx_5497_, lean_object* v_enodeMap_5498_, lean_object* v_exprs_5499_, lean_object* v_parents_5500_, lean_object* v_congrTable_5501_, lean_object* v_appMap_5502_, lean_object* v_indicesFound_5503_, lean_object* v_newFacts_5504_, uint8_t v_inconsistent_5505_, lean_object* v_nextIdx_5506_, lean_object* v_newRawFacts_5507_, lean_object* v_facts_5508_, lean_object* v_extThms_5509_, lean_object* v_inj_5510_, lean_object* v_split_5511_, lean_object* v_clean_5512_, lean_object* v_sstates_5513_, lean_object* v_mvarId_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_){
_start:
{
lean_object* v___x_5525_; 
v___x_5525_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5487_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_);
if (lean_obj_tag(v___x_5525_) == 0)
{
lean_object* v_a_5526_; lean_object* v___x_5527_; 
v_a_5526_ = lean_ctor_get(v___x_5525_, 0);
lean_inc(v_a_5526_);
lean_dec_ref(v___x_5525_);
v___x_5527_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_5488_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_);
if (lean_obj_tag(v___x_5527_) == 0)
{
lean_object* v_a_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5539_; 
v_a_5528_ = lean_ctor_get(v___x_5527_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v___x_5527_);
if (v_isSharedCheck_5539_ == 0)
{
v___x_5530_ = v___x_5527_;
v_isShared_5531_ = v_isSharedCheck_5539_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_a_5528_);
lean_dec(v___x_5527_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5539_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5537_; 
v___x_5532_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_5533_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5533_, 0, v___x_5532_);
lean_ctor_set(v___x_5533_, 1, v_gmt_5489_);
lean_ctor_set(v___x_5533_, 2, v_a_5526_);
lean_ctor_set(v___x_5533_, 3, v_a_5528_);
lean_ctor_set(v___x_5533_, 4, v_numInstances_5490_);
lean_ctor_set(v___x_5533_, 5, v_numDelayedInstances_5491_);
lean_ctor_set(v___x_5533_, 6, v_num_5492_);
lean_ctor_set(v___x_5533_, 7, v_preInstances_5493_);
lean_ctor_set(v___x_5533_, 8, v_nextThmIdx_5494_);
lean_ctor_set(v___x_5533_, 9, v_matchEqNames_5495_);
lean_ctor_set(v___x_5533_, 10, v_delayedThmInsts_5496_);
v___x_5534_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_5534_, 0, v_nextDeclIdx_5497_);
lean_ctor_set(v___x_5534_, 1, v_enodeMap_5498_);
lean_ctor_set(v___x_5534_, 2, v_exprs_5499_);
lean_ctor_set(v___x_5534_, 3, v_parents_5500_);
lean_ctor_set(v___x_5534_, 4, v_congrTable_5501_);
lean_ctor_set(v___x_5534_, 5, v_appMap_5502_);
lean_ctor_set(v___x_5534_, 6, v_indicesFound_5503_);
lean_ctor_set(v___x_5534_, 7, v_newFacts_5504_);
lean_ctor_set(v___x_5534_, 8, v_nextIdx_5506_);
lean_ctor_set(v___x_5534_, 9, v_newRawFacts_5507_);
lean_ctor_set(v___x_5534_, 10, v_facts_5508_);
lean_ctor_set(v___x_5534_, 11, v_extThms_5509_);
lean_ctor_set(v___x_5534_, 12, v___x_5533_);
lean_ctor_set(v___x_5534_, 13, v_inj_5510_);
lean_ctor_set(v___x_5534_, 14, v_split_5511_);
lean_ctor_set(v___x_5534_, 15, v_clean_5512_);
lean_ctor_set(v___x_5534_, 16, v_sstates_5513_);
lean_ctor_set_uint8(v___x_5534_, sizeof(void*)*17, v_inconsistent_5505_);
v___x_5535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5535_, 0, v___x_5534_);
lean_ctor_set(v___x_5535_, 1, v_mvarId_5514_);
if (v_isShared_5531_ == 0)
{
lean_ctor_set(v___x_5530_, 0, v___x_5535_);
v___x_5537_ = v___x_5530_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v___x_5535_);
v___x_5537_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
return v___x_5537_;
}
}
}
else
{
lean_object* v_a_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5547_; 
lean_dec(v_a_5526_);
lean_dec(v_mvarId_5514_);
lean_dec_ref(v_sstates_5513_);
lean_dec_ref(v_clean_5512_);
lean_dec_ref(v_split_5511_);
lean_dec_ref(v_inj_5510_);
lean_dec_ref(v_extThms_5509_);
lean_dec_ref(v_facts_5508_);
lean_dec_ref(v_newRawFacts_5507_);
lean_dec(v_nextIdx_5506_);
lean_dec_ref(v_newFacts_5504_);
lean_dec_ref(v_indicesFound_5503_);
lean_dec_ref(v_appMap_5502_);
lean_dec_ref(v_congrTable_5501_);
lean_dec_ref(v_parents_5500_);
lean_dec_ref(v_exprs_5499_);
lean_dec_ref(v_enodeMap_5498_);
lean_dec(v_nextDeclIdx_5497_);
lean_dec_ref(v_delayedThmInsts_5496_);
lean_dec_ref(v_matchEqNames_5495_);
lean_dec(v_nextThmIdx_5494_);
lean_dec_ref(v_preInstances_5493_);
lean_dec(v_num_5492_);
lean_dec(v_numDelayedInstances_5491_);
lean_dec(v_numInstances_5490_);
lean_dec(v_gmt_5489_);
v_a_5540_ = lean_ctor_get(v___x_5527_, 0);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5527_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5542_ = v___x_5527_;
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_a_5540_);
lean_dec(v___x_5527_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5545_; 
if (v_isShared_5543_ == 0)
{
v___x_5545_ = v___x_5542_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_a_5540_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
return v___x_5545_;
}
}
}
}
else
{
lean_object* v_a_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5555_; 
lean_dec(v_mvarId_5514_);
lean_dec_ref(v_sstates_5513_);
lean_dec_ref(v_clean_5512_);
lean_dec_ref(v_split_5511_);
lean_dec_ref(v_inj_5510_);
lean_dec_ref(v_extThms_5509_);
lean_dec_ref(v_facts_5508_);
lean_dec_ref(v_newRawFacts_5507_);
lean_dec(v_nextIdx_5506_);
lean_dec_ref(v_newFacts_5504_);
lean_dec_ref(v_indicesFound_5503_);
lean_dec_ref(v_appMap_5502_);
lean_dec_ref(v_congrTable_5501_);
lean_dec_ref(v_parents_5500_);
lean_dec_ref(v_exprs_5499_);
lean_dec_ref(v_enodeMap_5498_);
lean_dec(v_nextDeclIdx_5497_);
lean_dec_ref(v_delayedThmInsts_5496_);
lean_dec_ref(v_matchEqNames_5495_);
lean_dec(v_nextThmIdx_5494_);
lean_dec_ref(v_preInstances_5493_);
lean_dec(v_num_5492_);
lean_dec(v_numDelayedInstances_5491_);
lean_dec(v_numInstances_5490_);
lean_dec(v_gmt_5489_);
v_a_5548_ = lean_ctor_get(v___x_5525_, 0);
v_isSharedCheck_5555_ = !lean_is_exclusive(v___x_5525_);
if (v_isSharedCheck_5555_ == 0)
{
v___x_5550_ = v___x_5525_;
v_isShared_5551_ = v_isSharedCheck_5555_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_a_5548_);
lean_dec(v___x_5525_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5555_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
lean_object* v___x_5553_; 
if (v_isShared_5551_ == 0)
{
v___x_5553_ = v___x_5550_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v_a_5548_);
v___x_5553_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
return v___x_5553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_5556_ = _args[0];
lean_object* v_newThms_5557_ = _args[1];
lean_object* v_gmt_5558_ = _args[2];
lean_object* v_numInstances_5559_ = _args[3];
lean_object* v_numDelayedInstances_5560_ = _args[4];
lean_object* v_num_5561_ = _args[5];
lean_object* v_preInstances_5562_ = _args[6];
lean_object* v_nextThmIdx_5563_ = _args[7];
lean_object* v_matchEqNames_5564_ = _args[8];
lean_object* v_delayedThmInsts_5565_ = _args[9];
lean_object* v_nextDeclIdx_5566_ = _args[10];
lean_object* v_enodeMap_5567_ = _args[11];
lean_object* v_exprs_5568_ = _args[12];
lean_object* v_parents_5569_ = _args[13];
lean_object* v_congrTable_5570_ = _args[14];
lean_object* v_appMap_5571_ = _args[15];
lean_object* v_indicesFound_5572_ = _args[16];
lean_object* v_newFacts_5573_ = _args[17];
lean_object* v_inconsistent_5574_ = _args[18];
lean_object* v_nextIdx_5575_ = _args[19];
lean_object* v_newRawFacts_5576_ = _args[20];
lean_object* v_facts_5577_ = _args[21];
lean_object* v_extThms_5578_ = _args[22];
lean_object* v_inj_5579_ = _args[23];
lean_object* v_split_5580_ = _args[24];
lean_object* v_clean_5581_ = _args[25];
lean_object* v_sstates_5582_ = _args[26];
lean_object* v_mvarId_5583_ = _args[27];
lean_object* v___y_5584_ = _args[28];
lean_object* v___y_5585_ = _args[29];
lean_object* v___y_5586_ = _args[30];
lean_object* v___y_5587_ = _args[31];
lean_object* v___y_5588_ = _args[32];
lean_object* v___y_5589_ = _args[33];
lean_object* v___y_5590_ = _args[34];
lean_object* v___y_5591_ = _args[35];
lean_object* v___y_5592_ = _args[36];
lean_object* v___y_5593_ = _args[37];
_start:
{
uint8_t v_inconsistent_boxed_5594_; lean_object* v_res_5595_; 
v_inconsistent_boxed_5594_ = lean_unbox(v_inconsistent_5574_);
v_res_5595_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_5556_, v_newThms_5557_, v_gmt_5558_, v_numInstances_5559_, v_numDelayedInstances_5560_, v_num_5561_, v_preInstances_5562_, v_nextThmIdx_5563_, v_matchEqNames_5564_, v_delayedThmInsts_5565_, v_nextDeclIdx_5566_, v_enodeMap_5567_, v_exprs_5568_, v_parents_5569_, v_congrTable_5570_, v_appMap_5571_, v_indicesFound_5572_, v_newFacts_5573_, v_inconsistent_boxed_5594_, v_nextIdx_5575_, v_newRawFacts_5576_, v_facts_5577_, v_extThms_5578_, v_inj_5579_, v_split_5580_, v_clean_5581_, v_sstates_5582_, v_mvarId_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_);
lean_dec(v___y_5592_);
lean_dec_ref(v___y_5591_);
lean_dec(v___y_5590_);
lean_dec_ref(v___y_5589_);
lean_dec(v___y_5588_);
lean_dec_ref(v___y_5587_);
lean_dec(v___y_5586_);
lean_dec_ref(v___y_5585_);
lean_dec(v___y_5584_);
lean_dec_ref(v_newThms_5557_);
lean_dec_ref(v_thms_5556_);
return v_res_5595_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5596_; 
v___x_5596_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return v___x_5596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_5597_, size_t v_i_5598_, lean_object* v_bs_5599_){
_start:
{
uint8_t v___x_5600_; 
v___x_5600_ = lean_usize_dec_lt(v_i_5598_, v_sz_5597_);
if (v___x_5600_ == 0)
{
return v_bs_5599_;
}
else
{
lean_object* v_v_5601_; lean_object* v_casesTypes_5602_; lean_object* v_extThms_5603_; lean_object* v_funCC_5604_; lean_object* v_inj_5605_; lean_object* v___x_5607_; uint8_t v_isShared_5608_; uint8_t v_isSharedCheck_5619_; 
v_v_5601_ = lean_array_uget(v_bs_5599_, v_i_5598_);
v_casesTypes_5602_ = lean_ctor_get(v_v_5601_, 0);
v_extThms_5603_ = lean_ctor_get(v_v_5601_, 1);
v_funCC_5604_ = lean_ctor_get(v_v_5601_, 2);
v_inj_5605_ = lean_ctor_get(v_v_5601_, 4);
v_isSharedCheck_5619_ = !lean_is_exclusive(v_v_5601_);
if (v_isSharedCheck_5619_ == 0)
{
lean_object* v_unused_5620_; 
v_unused_5620_ = lean_ctor_get(v_v_5601_, 3);
lean_dec(v_unused_5620_);
v___x_5607_ = v_v_5601_;
v_isShared_5608_ = v_isSharedCheck_5619_;
goto v_resetjp_5606_;
}
else
{
lean_inc(v_inj_5605_);
lean_inc(v_funCC_5604_);
lean_inc(v_extThms_5603_);
lean_inc(v_casesTypes_5602_);
lean_dec(v_v_5601_);
v___x_5607_ = lean_box(0);
v_isShared_5608_ = v_isSharedCheck_5619_;
goto v_resetjp_5606_;
}
v_resetjp_5606_:
{
lean_object* v___x_5609_; lean_object* v_bs_x27_5610_; lean_object* v___x_5611_; lean_object* v___x_5613_; 
v___x_5609_ = lean_unsigned_to_nat(0u);
v_bs_x27_5610_ = lean_array_uset(v_bs_5599_, v_i_5598_, v___x_5609_);
v___x_5611_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_5608_ == 0)
{
lean_ctor_set(v___x_5607_, 3, v___x_5611_);
v___x_5613_ = v___x_5607_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_casesTypes_5602_);
lean_ctor_set(v_reuseFailAlloc_5618_, 1, v_extThms_5603_);
lean_ctor_set(v_reuseFailAlloc_5618_, 2, v_funCC_5604_);
lean_ctor_set(v_reuseFailAlloc_5618_, 3, v___x_5611_);
lean_ctor_set(v_reuseFailAlloc_5618_, 4, v_inj_5605_);
v___x_5613_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
size_t v___x_5614_; size_t v___x_5615_; lean_object* v___x_5616_; 
v___x_5614_ = ((size_t)1ULL);
v___x_5615_ = lean_usize_add(v_i_5598_, v___x_5614_);
v___x_5616_ = lean_array_uset(v_bs_x27_5610_, v_i_5598_, v___x_5613_);
v_i_5598_ = v___x_5615_;
v_bs_5599_ = v___x_5616_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_5621_, lean_object* v_i_5622_, lean_object* v_bs_5623_){
_start:
{
size_t v_sz_boxed_5624_; size_t v_i_boxed_5625_; lean_object* v_res_5626_; 
v_sz_boxed_5624_ = lean_unbox_usize(v_sz_5621_);
lean_dec(v_sz_5621_);
v_i_boxed_5625_ = lean_unbox_usize(v_i_5622_);
lean_dec(v_i_5622_);
v_res_5626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_5624_, v_i_boxed_5625_, v_bs_5623_);
return v_res_5626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_5627_, lean_object* v_ps_5628_, uint8_t v_only_5629_, lean_object* v_k_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_){
_start:
{
lean_object* v___y_5641_; lean_object* v___y_5642_; lean_object* v___y_5643_; lean_object* v___y_5644_; lean_object* v___y_5645_; lean_object* v___y_5646_; lean_object* v___y_5647_; lean_object* v___y_5648_; lean_object* v___y_5649_; uint8_t v___y_5662_; uint8_t v___y_5663_; lean_object* v_params_5664_; lean_object* v___y_5665_; lean_object* v___y_5666_; lean_object* v___y_5667_; lean_object* v___y_5668_; lean_object* v___y_5669_; lean_object* v___y_5670_; lean_object* v___y_5671_; lean_object* v___y_5672_; uint8_t v___y_5773_; 
if (v_only_5629_ == 0)
{
lean_object* v___x_5795_; lean_object* v___x_5796_; uint8_t v___x_5797_; 
v___x_5795_ = lean_array_get_size(v_ps_5628_);
v___x_5796_ = lean_unsigned_to_nat(0u);
v___x_5797_ = lean_nat_dec_eq(v___x_5795_, v___x_5796_);
if (v___x_5797_ == 0)
{
v___y_5773_ = v___x_5797_;
goto v___jp_5772_;
}
else
{
lean_object* v___x_5798_; 
lean_dec_ref(v_params_5627_);
lean_inc(v_a_5638_);
lean_inc_ref(v_a_5637_);
lean_inc(v_a_5636_);
lean_inc_ref(v_a_5635_);
lean_inc(v_a_5634_);
lean_inc_ref(v_a_5633_);
lean_inc(v_a_5632_);
lean_inc_ref(v_a_5631_);
v___x_5798_ = lean_apply_9(v_k_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_, v_a_5638_, lean_box(0));
return v___x_5798_;
}
}
else
{
uint8_t v___x_5799_; 
v___x_5799_ = 0;
v___y_5773_ = v___x_5799_;
goto v___jp_5772_;
}
v___jp_5640_:
{
lean_object* v___x_5650_; lean_object* v___x_5651_; 
v___x_5650_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_5650_, 0, v___y_5641_);
v___x_5651_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_5650_, v___y_5642_, v___y_5643_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
if (lean_obj_tag(v___x_5651_) == 0)
{
lean_object* v___x_5652_; 
lean_dec_ref(v___x_5651_);
lean_inc(v___y_5649_);
lean_inc_ref(v___y_5648_);
lean_inc(v___y_5647_);
lean_inc_ref(v___y_5646_);
lean_inc(v___y_5645_);
lean_inc_ref(v___y_5644_);
lean_inc(v___y_5643_);
v___x_5652_ = lean_apply_9(v_k_5630_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_, lean_box(0));
return v___x_5652_;
}
else
{
lean_object* v_a_5653_; lean_object* v___x_5655_; uint8_t v_isShared_5656_; uint8_t v_isSharedCheck_5660_; 
lean_dec_ref(v___y_5642_);
lean_dec_ref(v_k_5630_);
v_a_5653_ = lean_ctor_get(v___x_5651_, 0);
v_isSharedCheck_5660_ = !lean_is_exclusive(v___x_5651_);
if (v_isSharedCheck_5660_ == 0)
{
v___x_5655_ = v___x_5651_;
v_isShared_5656_ = v_isSharedCheck_5660_;
goto v_resetjp_5654_;
}
else
{
lean_inc(v_a_5653_);
lean_dec(v___x_5651_);
v___x_5655_ = lean_box(0);
v_isShared_5656_ = v_isSharedCheck_5660_;
goto v_resetjp_5654_;
}
v_resetjp_5654_:
{
lean_object* v___x_5658_; 
if (v_isShared_5656_ == 0)
{
v___x_5658_ = v___x_5655_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_a_5653_);
v___x_5658_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
return v___x_5658_;
}
}
}
}
v___jp_5661_:
{
lean_object* v___x_5673_; 
v___x_5673_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5664_, v_ps_5628_, v_only_5629_, v___y_5662_, v___y_5663_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_);
if (lean_obj_tag(v___x_5673_) == 0)
{
lean_object* v_a_5674_; lean_object* v_ctx_5675_; lean_object* v_anchorRefs_x3f_5676_; lean_object* v_toContext_5677_; lean_object* v_sctx_5678_; lean_object* v_methods_5679_; uint8_t v_sym_5680_; lean_object* v_simp_5681_; lean_object* v_simpMethods_5682_; lean_object* v_config_5683_; uint8_t v_cheapCases_5684_; uint8_t v_reportMVarIssue_5685_; lean_object* v_splitSource_5686_; lean_object* v_ematchDiagSource_5687_; lean_object* v_symPrios_5688_; lean_object* v_extensions_5689_; uint8_t v_debug_5690_; uint8_t v_ematchDiag_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; 
v_a_5674_ = lean_ctor_get(v___x_5673_, 0);
lean_inc_n(v_a_5674_, 2);
lean_dec_ref(v___x_5673_);
v_ctx_5675_ = lean_ctor_get(v___y_5665_, 1);
v_anchorRefs_x3f_5676_ = lean_ctor_get(v_a_5674_, 8);
v_toContext_5677_ = lean_ctor_get(v___y_5665_, 0);
v_sctx_5678_ = lean_ctor_get(v___y_5665_, 2);
v_methods_5679_ = lean_ctor_get(v___y_5665_, 3);
v_sym_5680_ = lean_ctor_get_uint8(v___y_5665_, sizeof(void*)*5);
v_simp_5681_ = lean_ctor_get(v_ctx_5675_, 0);
v_simpMethods_5682_ = lean_ctor_get(v_ctx_5675_, 1);
v_config_5683_ = lean_ctor_get(v_ctx_5675_, 2);
v_cheapCases_5684_ = lean_ctor_get_uint8(v_ctx_5675_, sizeof(void*)*8);
v_reportMVarIssue_5685_ = lean_ctor_get_uint8(v_ctx_5675_, sizeof(void*)*8 + 1);
v_splitSource_5686_ = lean_ctor_get(v_ctx_5675_, 4);
v_ematchDiagSource_5687_ = lean_ctor_get(v_ctx_5675_, 5);
v_symPrios_5688_ = lean_ctor_get(v_ctx_5675_, 6);
v_extensions_5689_ = lean_ctor_get(v_ctx_5675_, 7);
v_debug_5690_ = lean_ctor_get_uint8(v_ctx_5675_, sizeof(void*)*8 + 2);
v_ematchDiag_5691_ = lean_ctor_get_uint8(v_ctx_5675_, sizeof(void*)*8 + 3);
lean_inc_ref(v_extensions_5689_);
lean_inc_ref(v_symPrios_5688_);
lean_inc(v_ematchDiagSource_5687_);
lean_inc(v_splitSource_5686_);
lean_inc(v_anchorRefs_x3f_5676_);
lean_inc_ref(v_config_5683_);
lean_inc_ref(v_simpMethods_5682_);
lean_inc_ref(v_simp_5681_);
v___x_5692_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_5692_, 0, v_simp_5681_);
lean_ctor_set(v___x_5692_, 1, v_simpMethods_5682_);
lean_ctor_set(v___x_5692_, 2, v_config_5683_);
lean_ctor_set(v___x_5692_, 3, v_anchorRefs_x3f_5676_);
lean_ctor_set(v___x_5692_, 4, v_splitSource_5686_);
lean_ctor_set(v___x_5692_, 5, v_ematchDiagSource_5687_);
lean_ctor_set(v___x_5692_, 6, v_symPrios_5688_);
lean_ctor_set(v___x_5692_, 7, v_extensions_5689_);
lean_ctor_set_uint8(v___x_5692_, sizeof(void*)*8, v_cheapCases_5684_);
lean_ctor_set_uint8(v___x_5692_, sizeof(void*)*8 + 1, v_reportMVarIssue_5685_);
lean_ctor_set_uint8(v___x_5692_, sizeof(void*)*8 + 2, v_debug_5690_);
lean_ctor_set_uint8(v___x_5692_, sizeof(void*)*8 + 3, v_ematchDiag_5691_);
lean_inc_ref(v_methods_5679_);
lean_inc_ref(v_sctx_5678_);
lean_inc_ref(v_toContext_5677_);
v___x_5693_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_5693_, 0, v_toContext_5677_);
lean_ctor_set(v___x_5693_, 1, v___x_5692_);
lean_ctor_set(v___x_5693_, 2, v_sctx_5678_);
lean_ctor_set(v___x_5693_, 3, v_methods_5679_);
lean_ctor_set(v___x_5693_, 4, v_a_5674_);
lean_ctor_set_uint8(v___x_5693_, sizeof(void*)*5, v_sym_5680_);
if (v_only_5629_ == 0)
{
v___y_5641_ = v_a_5674_;
v___y_5642_ = v___x_5693_;
v___y_5643_ = v___y_5666_;
v___y_5644_ = v___y_5667_;
v___y_5645_ = v___y_5668_;
v___y_5646_ = v___y_5669_;
v___y_5647_ = v___y_5670_;
v___y_5648_ = v___y_5671_;
v___y_5649_ = v___y_5672_;
goto v___jp_5640_;
}
else
{
lean_object* v___x_5694_; 
v___x_5694_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_5666_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_);
if (lean_obj_tag(v___x_5694_) == 0)
{
lean_object* v_a_5695_; lean_object* v_toGoalState_5696_; lean_object* v_ematch_5697_; lean_object* v_mvarId_5698_; lean_object* v___x_5700_; uint8_t v_isShared_5701_; uint8_t v_isSharedCheck_5754_; 
v_a_5695_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_a_5695_);
lean_dec_ref(v___x_5694_);
v_toGoalState_5696_ = lean_ctor_get(v_a_5695_, 0);
lean_inc_ref(v_toGoalState_5696_);
v_ematch_5697_ = lean_ctor_get(v_toGoalState_5696_, 12);
lean_inc_ref(v_ematch_5697_);
v_mvarId_5698_ = lean_ctor_get(v_a_5695_, 1);
v_isSharedCheck_5754_ = !lean_is_exclusive(v_a_5695_);
if (v_isSharedCheck_5754_ == 0)
{
lean_object* v_unused_5755_; 
v_unused_5755_ = lean_ctor_get(v_a_5695_, 0);
lean_dec(v_unused_5755_);
v___x_5700_ = v_a_5695_;
v_isShared_5701_ = v_isSharedCheck_5754_;
goto v_resetjp_5699_;
}
else
{
lean_inc(v_mvarId_5698_);
lean_dec(v_a_5695_);
v___x_5700_ = lean_box(0);
v_isShared_5701_ = v_isSharedCheck_5754_;
goto v_resetjp_5699_;
}
v_resetjp_5699_:
{
lean_object* v_nextDeclIdx_5702_; lean_object* v_enodeMap_5703_; lean_object* v_exprs_5704_; lean_object* v_parents_5705_; lean_object* v_congrTable_5706_; lean_object* v_appMap_5707_; lean_object* v_indicesFound_5708_; lean_object* v_newFacts_5709_; uint8_t v_inconsistent_5710_; lean_object* v_nextIdx_5711_; lean_object* v_newRawFacts_5712_; lean_object* v_facts_5713_; lean_object* v_extThms_5714_; lean_object* v_inj_5715_; lean_object* v_split_5716_; lean_object* v_clean_5717_; lean_object* v_sstates_5718_; lean_object* v_gmt_5719_; lean_object* v_thms_5720_; lean_object* v_newThms_5721_; lean_object* v_numInstances_5722_; lean_object* v_numDelayedInstances_5723_; lean_object* v_num_5724_; lean_object* v_preInstances_5725_; lean_object* v_nextThmIdx_5726_; lean_object* v_matchEqNames_5727_; lean_object* v_delayedThmInsts_5728_; lean_object* v___x_5729_; lean_object* v___f_5730_; lean_object* v___x_5731_; 
v_nextDeclIdx_5702_ = lean_ctor_get(v_toGoalState_5696_, 0);
lean_inc(v_nextDeclIdx_5702_);
v_enodeMap_5703_ = lean_ctor_get(v_toGoalState_5696_, 1);
lean_inc_ref(v_enodeMap_5703_);
v_exprs_5704_ = lean_ctor_get(v_toGoalState_5696_, 2);
lean_inc_ref(v_exprs_5704_);
v_parents_5705_ = lean_ctor_get(v_toGoalState_5696_, 3);
lean_inc_ref(v_parents_5705_);
v_congrTable_5706_ = lean_ctor_get(v_toGoalState_5696_, 4);
lean_inc_ref(v_congrTable_5706_);
v_appMap_5707_ = lean_ctor_get(v_toGoalState_5696_, 5);
lean_inc_ref(v_appMap_5707_);
v_indicesFound_5708_ = lean_ctor_get(v_toGoalState_5696_, 6);
lean_inc_ref(v_indicesFound_5708_);
v_newFacts_5709_ = lean_ctor_get(v_toGoalState_5696_, 7);
lean_inc_ref(v_newFacts_5709_);
v_inconsistent_5710_ = lean_ctor_get_uint8(v_toGoalState_5696_, sizeof(void*)*17);
v_nextIdx_5711_ = lean_ctor_get(v_toGoalState_5696_, 8);
lean_inc(v_nextIdx_5711_);
v_newRawFacts_5712_ = lean_ctor_get(v_toGoalState_5696_, 9);
lean_inc_ref(v_newRawFacts_5712_);
v_facts_5713_ = lean_ctor_get(v_toGoalState_5696_, 10);
lean_inc_ref(v_facts_5713_);
v_extThms_5714_ = lean_ctor_get(v_toGoalState_5696_, 11);
lean_inc_ref(v_extThms_5714_);
v_inj_5715_ = lean_ctor_get(v_toGoalState_5696_, 13);
lean_inc_ref(v_inj_5715_);
v_split_5716_ = lean_ctor_get(v_toGoalState_5696_, 14);
lean_inc_ref(v_split_5716_);
v_clean_5717_ = lean_ctor_get(v_toGoalState_5696_, 15);
lean_inc_ref(v_clean_5717_);
v_sstates_5718_ = lean_ctor_get(v_toGoalState_5696_, 16);
lean_inc_ref(v_sstates_5718_);
lean_dec_ref(v_toGoalState_5696_);
v_gmt_5719_ = lean_ctor_get(v_ematch_5697_, 1);
lean_inc(v_gmt_5719_);
v_thms_5720_ = lean_ctor_get(v_ematch_5697_, 2);
lean_inc_ref(v_thms_5720_);
v_newThms_5721_ = lean_ctor_get(v_ematch_5697_, 3);
lean_inc_ref(v_newThms_5721_);
v_numInstances_5722_ = lean_ctor_get(v_ematch_5697_, 4);
lean_inc(v_numInstances_5722_);
v_numDelayedInstances_5723_ = lean_ctor_get(v_ematch_5697_, 5);
lean_inc(v_numDelayedInstances_5723_);
v_num_5724_ = lean_ctor_get(v_ematch_5697_, 6);
lean_inc(v_num_5724_);
v_preInstances_5725_ = lean_ctor_get(v_ematch_5697_, 7);
lean_inc_ref(v_preInstances_5725_);
v_nextThmIdx_5726_ = lean_ctor_get(v_ematch_5697_, 8);
lean_inc(v_nextThmIdx_5726_);
v_matchEqNames_5727_ = lean_ctor_get(v_ematch_5697_, 9);
lean_inc_ref(v_matchEqNames_5727_);
v_delayedThmInsts_5728_ = lean_ctor_get(v_ematch_5697_, 10);
lean_inc_ref(v_delayedThmInsts_5728_);
lean_dec_ref(v_ematch_5697_);
v___x_5729_ = lean_box(v_inconsistent_5710_);
v___f_5730_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 38, 28);
lean_closure_set(v___f_5730_, 0, v_thms_5720_);
lean_closure_set(v___f_5730_, 1, v_newThms_5721_);
lean_closure_set(v___f_5730_, 2, v_gmt_5719_);
lean_closure_set(v___f_5730_, 3, v_numInstances_5722_);
lean_closure_set(v___f_5730_, 4, v_numDelayedInstances_5723_);
lean_closure_set(v___f_5730_, 5, v_num_5724_);
lean_closure_set(v___f_5730_, 6, v_preInstances_5725_);
lean_closure_set(v___f_5730_, 7, v_nextThmIdx_5726_);
lean_closure_set(v___f_5730_, 8, v_matchEqNames_5727_);
lean_closure_set(v___f_5730_, 9, v_delayedThmInsts_5728_);
lean_closure_set(v___f_5730_, 10, v_nextDeclIdx_5702_);
lean_closure_set(v___f_5730_, 11, v_enodeMap_5703_);
lean_closure_set(v___f_5730_, 12, v_exprs_5704_);
lean_closure_set(v___f_5730_, 13, v_parents_5705_);
lean_closure_set(v___f_5730_, 14, v_congrTable_5706_);
lean_closure_set(v___f_5730_, 15, v_appMap_5707_);
lean_closure_set(v___f_5730_, 16, v_indicesFound_5708_);
lean_closure_set(v___f_5730_, 17, v_newFacts_5709_);
lean_closure_set(v___f_5730_, 18, v___x_5729_);
lean_closure_set(v___f_5730_, 19, v_nextIdx_5711_);
lean_closure_set(v___f_5730_, 20, v_newRawFacts_5712_);
lean_closure_set(v___f_5730_, 21, v_facts_5713_);
lean_closure_set(v___f_5730_, 22, v_extThms_5714_);
lean_closure_set(v___f_5730_, 23, v_inj_5715_);
lean_closure_set(v___f_5730_, 24, v_split_5716_);
lean_closure_set(v___f_5730_, 25, v_clean_5717_);
lean_closure_set(v___f_5730_, 26, v_sstates_5718_);
lean_closure_set(v___f_5730_, 27, v_mvarId_5698_);
v___x_5731_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_5730_, v___x_5693_, v___y_5666_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_);
if (lean_obj_tag(v___x_5731_) == 0)
{
lean_object* v_a_5732_; lean_object* v___x_5733_; lean_object* v___x_5735_; 
v_a_5732_ = lean_ctor_get(v___x_5731_, 0);
lean_inc(v_a_5732_);
lean_dec_ref(v___x_5731_);
v___x_5733_ = lean_box(0);
if (v_isShared_5701_ == 0)
{
lean_ctor_set_tag(v___x_5700_, 1);
lean_ctor_set(v___x_5700_, 1, v___x_5733_);
lean_ctor_set(v___x_5700_, 0, v_a_5732_);
v___x_5735_ = v___x_5700_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5745_; 
v_reuseFailAlloc_5745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5745_, 0, v_a_5732_);
lean_ctor_set(v_reuseFailAlloc_5745_, 1, v___x_5733_);
v___x_5735_ = v_reuseFailAlloc_5745_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
lean_object* v___x_5736_; 
v___x_5736_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_5735_, v___y_5666_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_);
if (lean_obj_tag(v___x_5736_) == 0)
{
lean_dec_ref(v___x_5736_);
v___y_5641_ = v_a_5674_;
v___y_5642_ = v___x_5693_;
v___y_5643_ = v___y_5666_;
v___y_5644_ = v___y_5667_;
v___y_5645_ = v___y_5668_;
v___y_5646_ = v___y_5669_;
v___y_5647_ = v___y_5670_;
v___y_5648_ = v___y_5671_;
v___y_5649_ = v___y_5672_;
goto v___jp_5640_;
}
else
{
lean_object* v_a_5737_; lean_object* v___x_5739_; uint8_t v_isShared_5740_; uint8_t v_isSharedCheck_5744_; 
lean_dec_ref(v___x_5693_);
lean_dec(v_a_5674_);
lean_dec_ref(v_k_5630_);
v_a_5737_ = lean_ctor_get(v___x_5736_, 0);
v_isSharedCheck_5744_ = !lean_is_exclusive(v___x_5736_);
if (v_isSharedCheck_5744_ == 0)
{
v___x_5739_ = v___x_5736_;
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
else
{
lean_inc(v_a_5737_);
lean_dec(v___x_5736_);
v___x_5739_ = lean_box(0);
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
v_resetjp_5738_:
{
lean_object* v___x_5742_; 
if (v_isShared_5740_ == 0)
{
v___x_5742_ = v___x_5739_;
goto v_reusejp_5741_;
}
else
{
lean_object* v_reuseFailAlloc_5743_; 
v_reuseFailAlloc_5743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5737_);
v___x_5742_ = v_reuseFailAlloc_5743_;
goto v_reusejp_5741_;
}
v_reusejp_5741_:
{
return v___x_5742_;
}
}
}
}
}
else
{
lean_object* v_a_5746_; lean_object* v___x_5748_; uint8_t v_isShared_5749_; uint8_t v_isSharedCheck_5753_; 
lean_del_object(v___x_5700_);
lean_dec_ref(v___x_5693_);
lean_dec(v_a_5674_);
lean_dec_ref(v_k_5630_);
v_a_5746_ = lean_ctor_get(v___x_5731_, 0);
v_isSharedCheck_5753_ = !lean_is_exclusive(v___x_5731_);
if (v_isSharedCheck_5753_ == 0)
{
v___x_5748_ = v___x_5731_;
v_isShared_5749_ = v_isSharedCheck_5753_;
goto v_resetjp_5747_;
}
else
{
lean_inc(v_a_5746_);
lean_dec(v___x_5731_);
v___x_5748_ = lean_box(0);
v_isShared_5749_ = v_isSharedCheck_5753_;
goto v_resetjp_5747_;
}
v_resetjp_5747_:
{
lean_object* v___x_5751_; 
if (v_isShared_5749_ == 0)
{
v___x_5751_ = v___x_5748_;
goto v_reusejp_5750_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_a_5746_);
v___x_5751_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5750_;
}
v_reusejp_5750_:
{
return v___x_5751_;
}
}
}
}
}
else
{
lean_object* v_a_5756_; lean_object* v___x_5758_; uint8_t v_isShared_5759_; uint8_t v_isSharedCheck_5763_; 
lean_dec_ref(v___x_5693_);
lean_dec(v_a_5674_);
lean_dec_ref(v_k_5630_);
v_a_5756_ = lean_ctor_get(v___x_5694_, 0);
v_isSharedCheck_5763_ = !lean_is_exclusive(v___x_5694_);
if (v_isSharedCheck_5763_ == 0)
{
v___x_5758_ = v___x_5694_;
v_isShared_5759_ = v_isSharedCheck_5763_;
goto v_resetjp_5757_;
}
else
{
lean_inc(v_a_5756_);
lean_dec(v___x_5694_);
v___x_5758_ = lean_box(0);
v_isShared_5759_ = v_isSharedCheck_5763_;
goto v_resetjp_5757_;
}
v_resetjp_5757_:
{
lean_object* v___x_5761_; 
if (v_isShared_5759_ == 0)
{
v___x_5761_ = v___x_5758_;
goto v_reusejp_5760_;
}
else
{
lean_object* v_reuseFailAlloc_5762_; 
v_reuseFailAlloc_5762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5762_, 0, v_a_5756_);
v___x_5761_ = v_reuseFailAlloc_5762_;
goto v_reusejp_5760_;
}
v_reusejp_5760_:
{
return v___x_5761_;
}
}
}
}
}
else
{
lean_object* v_a_5764_; lean_object* v___x_5766_; uint8_t v_isShared_5767_; uint8_t v_isSharedCheck_5771_; 
lean_dec_ref(v_k_5630_);
v_a_5764_ = lean_ctor_get(v___x_5673_, 0);
v_isSharedCheck_5771_ = !lean_is_exclusive(v___x_5673_);
if (v_isSharedCheck_5771_ == 0)
{
v___x_5766_ = v___x_5673_;
v_isShared_5767_ = v_isSharedCheck_5771_;
goto v_resetjp_5765_;
}
else
{
lean_inc(v_a_5764_);
lean_dec(v___x_5673_);
v___x_5766_ = lean_box(0);
v_isShared_5767_ = v_isSharedCheck_5771_;
goto v_resetjp_5765_;
}
v_resetjp_5765_:
{
lean_object* v___x_5769_; 
if (v_isShared_5767_ == 0)
{
v___x_5769_ = v___x_5766_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v_a_5764_);
v___x_5769_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5768_;
}
v_reusejp_5768_:
{
return v___x_5769_;
}
}
}
}
v___jp_5772_:
{
uint8_t v___x_5774_; 
v___x_5774_ = 1;
if (v_only_5629_ == 0)
{
v___y_5662_ = v___y_5773_;
v___y_5663_ = v___x_5774_;
v_params_5664_ = v_params_5627_;
v___y_5665_ = v_a_5631_;
v___y_5666_ = v_a_5632_;
v___y_5667_ = v_a_5633_;
v___y_5668_ = v_a_5634_;
v___y_5669_ = v_a_5635_;
v___y_5670_ = v_a_5636_;
v___y_5671_ = v_a_5637_;
v___y_5672_ = v_a_5638_;
goto v___jp_5661_;
}
else
{
lean_object* v_config_5775_; lean_object* v_extensions_5776_; lean_object* v_extra_5777_; lean_object* v_extraInj_5778_; lean_object* v_extraFacts_5779_; lean_object* v_symPrios_5780_; lean_object* v_norm_5781_; lean_object* v_normProcs_5782_; lean_object* v___x_5784_; uint8_t v_isShared_5785_; uint8_t v_isSharedCheck_5793_; 
v_config_5775_ = lean_ctor_get(v_params_5627_, 0);
v_extensions_5776_ = lean_ctor_get(v_params_5627_, 1);
v_extra_5777_ = lean_ctor_get(v_params_5627_, 2);
v_extraInj_5778_ = lean_ctor_get(v_params_5627_, 3);
v_extraFacts_5779_ = lean_ctor_get(v_params_5627_, 4);
v_symPrios_5780_ = lean_ctor_get(v_params_5627_, 5);
v_norm_5781_ = lean_ctor_get(v_params_5627_, 6);
v_normProcs_5782_ = lean_ctor_get(v_params_5627_, 7);
v_isSharedCheck_5793_ = !lean_is_exclusive(v_params_5627_);
if (v_isSharedCheck_5793_ == 0)
{
lean_object* v_unused_5794_; 
v_unused_5794_ = lean_ctor_get(v_params_5627_, 8);
lean_dec(v_unused_5794_);
v___x_5784_ = v_params_5627_;
v_isShared_5785_ = v_isSharedCheck_5793_;
goto v_resetjp_5783_;
}
else
{
lean_inc(v_normProcs_5782_);
lean_inc(v_norm_5781_);
lean_inc(v_symPrios_5780_);
lean_inc(v_extraFacts_5779_);
lean_inc(v_extraInj_5778_);
lean_inc(v_extra_5777_);
lean_inc(v_extensions_5776_);
lean_inc(v_config_5775_);
lean_dec(v_params_5627_);
v___x_5784_ = lean_box(0);
v_isShared_5785_ = v_isSharedCheck_5793_;
goto v_resetjp_5783_;
}
v_resetjp_5783_:
{
size_t v_sz_5786_; size_t v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v_params_5791_; 
v_sz_5786_ = lean_array_size(v_extensions_5776_);
v___x_5787_ = ((size_t)0ULL);
v___x_5788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_5786_, v___x_5787_, v_extensions_5776_);
v___x_5789_ = lean_box(0);
if (v_isShared_5785_ == 0)
{
lean_ctor_set(v___x_5784_, 8, v___x_5789_);
lean_ctor_set(v___x_5784_, 1, v___x_5788_);
v_params_5791_ = v___x_5784_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v_config_5775_);
lean_ctor_set(v_reuseFailAlloc_5792_, 1, v___x_5788_);
lean_ctor_set(v_reuseFailAlloc_5792_, 2, v_extra_5777_);
lean_ctor_set(v_reuseFailAlloc_5792_, 3, v_extraInj_5778_);
lean_ctor_set(v_reuseFailAlloc_5792_, 4, v_extraFacts_5779_);
lean_ctor_set(v_reuseFailAlloc_5792_, 5, v_symPrios_5780_);
lean_ctor_set(v_reuseFailAlloc_5792_, 6, v_norm_5781_);
lean_ctor_set(v_reuseFailAlloc_5792_, 7, v_normProcs_5782_);
lean_ctor_set(v_reuseFailAlloc_5792_, 8, v___x_5789_);
v_params_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
v___y_5662_ = v___y_5773_;
v___y_5663_ = v___x_5774_;
v_params_5664_ = v_params_5791_;
v___y_5665_ = v_a_5631_;
v___y_5666_ = v_a_5632_;
v___y_5667_ = v_a_5633_;
v___y_5668_ = v_a_5634_;
v___y_5669_ = v_a_5635_;
v___y_5670_ = v_a_5636_;
v___y_5671_ = v_a_5637_;
v___y_5672_ = v_a_5638_;
goto v___jp_5661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_5800_, lean_object* v_ps_5801_, lean_object* v_only_5802_, lean_object* v_k_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_, lean_object* v_a_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_){
_start:
{
uint8_t v_only_boxed_5813_; lean_object* v_res_5814_; 
v_only_boxed_5813_ = lean_unbox(v_only_5802_);
v_res_5814_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5800_, v_ps_5801_, v_only_boxed_5813_, v_k_5803_, v_a_5804_, v_a_5805_, v_a_5806_, v_a_5807_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_);
lean_dec(v_a_5811_);
lean_dec_ref(v_a_5810_);
lean_dec(v_a_5809_);
lean_dec_ref(v_a_5808_);
lean_dec(v_a_5807_);
lean_dec_ref(v_a_5806_);
lean_dec(v_a_5805_);
lean_dec_ref(v_a_5804_);
lean_dec_ref(v_ps_5801_);
return v_res_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_5815_, lean_object* v_params_5816_, lean_object* v_ps_5817_, uint8_t v_only_5818_, lean_object* v_k_5819_, lean_object* v_a_5820_, lean_object* v_a_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_, lean_object* v_a_5826_, lean_object* v_a_5827_){
_start:
{
lean_object* v___x_5829_; 
v___x_5829_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5816_, v_ps_5817_, v_only_5818_, v_k_5819_, v_a_5820_, v_a_5821_, v_a_5822_, v_a_5823_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_);
return v___x_5829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_5830_, lean_object* v_params_5831_, lean_object* v_ps_5832_, lean_object* v_only_5833_, lean_object* v_k_5834_, lean_object* v_a_5835_, lean_object* v_a_5836_, lean_object* v_a_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_){
_start:
{
uint8_t v_only_boxed_5844_; lean_object* v_res_5845_; 
v_only_boxed_5844_ = lean_unbox(v_only_5833_);
v_res_5845_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_5830_, v_params_5831_, v_ps_5832_, v_only_boxed_5844_, v_k_5834_, v_a_5835_, v_a_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_);
lean_dec(v_a_5842_);
lean_dec_ref(v_a_5841_);
lean_dec(v_a_5840_);
lean_dec_ref(v_a_5839_);
lean_dec(v_a_5838_);
lean_dec_ref(v_a_5837_);
lean_dec(v_a_5836_);
lean_dec_ref(v_a_5835_);
lean_dec_ref(v_ps_5832_);
return v_res_5845_;
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
