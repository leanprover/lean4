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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
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
lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Meta_Grind_CasesTypes_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
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
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "extra"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 97, 194, 195, 68, 28, 219, 173)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "invalid `grind` parameter, failed to infer patterns"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "invalid `grind` parameter, only global declarations are allowed with this kind of modifier"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(lean_object* v_params_1_, lean_object* v_declName_2_, uint8_t v_eager_3_){
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
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_1_ = stack[0].m_obj;
lean_object* v_declName_2_ = stack[1].m_obj;
uint8_t v_eager_3_ = stack[2].m_num;
lean_object* v_res_49_;
v_res_49_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_1_, v_declName_2_, v_eager_3_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes___boxed(lean_object* v_params_50_, lean_object* v_declName_51_, lean_object* v_eager_52_){
_start:
{
uint8_t v_eager_boxed_53_; lean_object* v_res_54_; 
v_eager_boxed_53_ = lean_unbox(v_eager_52_);
v_res_54_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_50_, v_declName_51_, v_eager_boxed_53_);
return v_res_54_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(lean_object* v_declName_55_, lean_object* v_as_56_, size_t v_i_57_, size_t v_stop_58_){
_start:
{
uint8_t v___x_59_; 
v___x_59_ = lean_usize_dec_eq(v_i_57_, v_stop_58_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; lean_object* v_casesTypes_61_; uint8_t v___x_62_; 
v___x_60_ = lean_array_uget_borrowed(v_as_56_, v_i_57_);
v_casesTypes_61_ = lean_ctor_get(v___x_60_, 0);
v___x_62_ = l_Lean_Meta_Grind_CasesTypes_contains(v_casesTypes_61_, v_declName_55_);
if (v___x_62_ == 0)
{
size_t v___x_63_; size_t v___x_64_; 
v___x_63_ = ((size_t)1ULL);
v___x_64_ = lean_usize_add(v_i_57_, v___x_63_);
v_i_57_ = v___x_64_;
goto _start;
}
else
{
return v___x_62_;
}
}
else
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_55_ = stack[0].m_obj;
lean_object* v_as_56_ = stack[1].m_obj;
size_t v_i_57_ = stack[2].m_num;
size_t v_stop_58_ = stack[3].m_num;
uint8_t v_res_67_;
v_res_67_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(v_declName_55_, v_as_56_, v_i_57_, v_stop_58_);
stack->m_num = v_res_67_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0___boxed(lean_object* v_declName_68_, lean_object* v_as_69_, lean_object* v_i_70_, lean_object* v_stop_71_){
_start:
{
size_t v_i_boxed_72_; size_t v_stop_boxed_73_; uint8_t v_res_74_; lean_object* v_r_75_; 
v_i_boxed_72_ = lean_unbox_usize(v_i_70_);
lean_dec(v_i_70_);
v_stop_boxed_73_ = lean_unbox_usize(v_stop_71_);
lean_dec(v_stop_71_);
v_res_74_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(v_declName_68_, v_as_69_, v_i_boxed_72_, v_stop_boxed_73_);
lean_dec_ref(v_as_69_);
lean_dec(v_declName_68_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(lean_object* v_params_76_, lean_object* v_declName_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___y_82_; lean_object* v___y_83_; lean_object* v___y_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v___y_89_; lean_object* v___y_90_; lean_object* v_config_93_; lean_object* v_extensions_94_; lean_object* v_extra_95_; lean_object* v_extraInj_96_; lean_object* v_extraFacts_97_; lean_object* v_symPrios_98_; lean_object* v_norm_99_; lean_object* v_normProcs_100_; lean_object* v_anchorRefs_x3f_101_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_config_93_ = lean_ctor_get(v_params_76_, 0);
lean_inc_ref(v_config_93_);
v_extensions_94_ = lean_ctor_get(v_params_76_, 1);
lean_inc_ref(v_extensions_94_);
v_extra_95_ = lean_ctor_get(v_params_76_, 2);
lean_inc_ref(v_extra_95_);
v_extraInj_96_ = lean_ctor_get(v_params_76_, 3);
lean_inc_ref(v_extraInj_96_);
v_extraFacts_97_ = lean_ctor_get(v_params_76_, 4);
lean_inc_ref(v_extraFacts_97_);
v_symPrios_98_ = lean_ctor_get(v_params_76_, 5);
lean_inc_ref(v_symPrios_98_);
v_norm_99_ = lean_ctor_get(v_params_76_, 6);
lean_inc_ref(v_norm_99_);
v_normProcs_100_ = lean_ctor_get(v_params_76_, 7);
lean_inc_ref(v_normProcs_100_);
v_anchorRefs_x3f_101_ = lean_ctor_get(v_params_76_, 8);
lean_inc(v_anchorRefs_x3f_101_);
lean_dec_ref(v_params_76_);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_array_get_size(v_extensions_94_);
v___x_135_ = lean_nat_dec_lt(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
goto v___jp_123_;
}
else
{
if (v___x_135_ == 0)
{
goto v___jp_123_;
}
else
{
size_t v___x_136_; size_t v___x_137_; uint8_t v___x_138_; 
v___x_136_ = ((size_t)0ULL);
v___x_137_ = lean_usize_of_nat(v___x_134_);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(v_declName_77_, v_extensions_94_, v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
goto v___jp_123_;
}
else
{
goto v___jp_102_;
}
}
}
v___jp_81_:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_91_, 0, v___y_84_);
lean_ctor_set(v___x_91_, 1, v___y_90_);
lean_ctor_set(v___x_91_, 2, v___y_85_);
lean_ctor_set(v___x_91_, 3, v___y_89_);
lean_ctor_set(v___x_91_, 4, v___y_88_);
lean_ctor_set(v___x_91_, 5, v___y_87_);
lean_ctor_set(v___x_91_, 6, v___y_83_);
lean_ctor_set(v___x_91_, 7, v___y_86_);
lean_ctor_set(v___x_91_, 8, v___y_82_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
v___jp_102_:
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_array_get_size(v_extensions_94_);
v___x_105_ = lean_nat_dec_lt(v___x_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_dec(v_declName_77_);
v___y_82_ = v_anchorRefs_x3f_101_;
v___y_83_ = v_norm_99_;
v___y_84_ = v_config_93_;
v___y_85_ = v_extra_95_;
v___y_86_ = v_normProcs_100_;
v___y_87_ = v_symPrios_98_;
v___y_88_ = v_extraFacts_97_;
v___y_89_ = v_extraInj_96_;
v___y_90_ = v_extensions_94_;
goto v___jp_81_;
}
else
{
lean_object* v_v_106_; lean_object* v_casesTypes_107_; lean_object* v_extThms_108_; lean_object* v_funCC_109_; lean_object* v_ematch_110_; lean_object* v_inj_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_122_; 
v_v_106_ = lean_array_fget(v_extensions_94_, v___x_103_);
v_casesTypes_107_ = lean_ctor_get(v_v_106_, 0);
v_extThms_108_ = lean_ctor_get(v_v_106_, 1);
v_funCC_109_ = lean_ctor_get(v_v_106_, 2);
v_ematch_110_ = lean_ctor_get(v_v_106_, 3);
v_inj_111_ = lean_ctor_get(v_v_106_, 4);
v_isSharedCheck_122_ = !lean_is_exclusive(v_v_106_);
if (v_isSharedCheck_122_ == 0)
{
v___x_113_ = v_v_106_;
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_inj_111_);
lean_inc(v_ematch_110_);
lean_inc(v_funCC_109_);
lean_inc(v_extThms_108_);
lean_inc(v_casesTypes_107_);
lean_dec(v_v_106_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v_xs_x27_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_115_ = lean_box(0);
v_xs_x27_116_ = lean_array_fset(v_extensions_94_, v___x_103_, v___x_115_);
v___x_117_ = l_Lean_Meta_Grind_CasesTypes_erase(v_casesTypes_107_, v_declName_77_);
lean_dec(v_declName_77_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_117_);
v___x_119_ = v___x_113_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_extThms_108_);
lean_ctor_set(v_reuseFailAlloc_121_, 2, v_funCC_109_);
lean_ctor_set(v_reuseFailAlloc_121_, 3, v_ematch_110_);
lean_ctor_set(v_reuseFailAlloc_121_, 4, v_inj_111_);
v___x_119_ = v_reuseFailAlloc_121_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_120_; 
v___x_120_ = lean_array_fset(v_xs_x27_116_, v___x_103_, v___x_119_);
v___y_82_ = v_anchorRefs_x3f_101_;
v___y_83_ = v_norm_99_;
v___y_84_ = v_config_93_;
v___y_85_ = v_extra_95_;
v___y_86_ = v_normProcs_100_;
v___y_87_ = v_symPrios_98_;
v___y_88_ = v_extraFacts_97_;
v___y_89_ = v_extraInj_96_;
v___y_90_ = v___x_120_;
goto v___jp_81_;
}
}
}
}
v___jp_123_:
{
lean_object* v___x_124_; 
lean_inc(v_declName_77_);
v___x_124_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_77_, v_a_78_, v_a_79_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_dec_ref_known(v___x_124_, 1);
goto v___jp_102_;
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_dec(v_anchorRefs_x3f_101_);
lean_dec_ref(v_normProcs_100_);
lean_dec_ref(v_norm_99_);
lean_dec_ref(v_symPrios_98_);
lean_dec_ref(v_extraFacts_97_);
lean_dec_ref(v_extraInj_96_);
lean_dec_ref(v_extra_95_);
lean_dec_ref(v_extensions_94_);
lean_dec_ref(v_config_93_);
lean_dec(v_declName_77_);
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_76_ = stack[0].m_obj;
lean_object* v_declName_77_ = stack[1].m_obj;
lean_object* v_a_78_ = stack[2].m_obj;
lean_object* v_a_79_ = stack[3].m_obj;
lean_object* v_res_139_;
v_res_139_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_params_76_, v_declName_77_, v_a_78_, v_a_79_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes___boxed(lean_object* v_params_140_, lean_object* v_declName_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_params_140_, v_declName_141_, v_a_142_, v_a_143_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(lean_object* v_params_146_, lean_object* v_declName_147_){
_start:
{
lean_object* v_config_148_; lean_object* v_extensions_149_; lean_object* v_extra_150_; lean_object* v_extraInj_151_; lean_object* v_extraFacts_152_; lean_object* v_symPrios_153_; lean_object* v_norm_154_; lean_object* v_normProcs_155_; lean_object* v_anchorRefs_x3f_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_config_148_ = lean_ctor_get(v_params_146_, 0);
v_extensions_149_ = lean_ctor_get(v_params_146_, 1);
v_extra_150_ = lean_ctor_get(v_params_146_, 2);
v_extraInj_151_ = lean_ctor_get(v_params_146_, 3);
v_extraFacts_152_ = lean_ctor_get(v_params_146_, 4);
v_symPrios_153_ = lean_ctor_get(v_params_146_, 5);
v_norm_154_ = lean_ctor_get(v_params_146_, 6);
v_normProcs_155_ = lean_ctor_get(v_params_146_, 7);
v_anchorRefs_x3f_156_ = lean_ctor_get(v_params_146_, 8);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_array_get_size(v_extensions_149_);
v___x_159_ = lean_nat_dec_lt(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_dec(v_declName_147_);
return v_params_146_;
}
else
{
lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_183_; 
lean_inc(v_anchorRefs_x3f_156_);
lean_inc_ref(v_normProcs_155_);
lean_inc_ref(v_norm_154_);
lean_inc_ref(v_symPrios_153_);
lean_inc_ref(v_extraFacts_152_);
lean_inc_ref(v_extraInj_151_);
lean_inc_ref(v_extra_150_);
lean_inc_ref(v_extensions_149_);
lean_inc_ref(v_config_148_);
v_isSharedCheck_183_ = !lean_is_exclusive(v_params_146_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; lean_object* v_unused_185_; lean_object* v_unused_186_; lean_object* v_unused_187_; lean_object* v_unused_188_; lean_object* v_unused_189_; lean_object* v_unused_190_; lean_object* v_unused_191_; lean_object* v_unused_192_; 
v_unused_184_ = lean_ctor_get(v_params_146_, 8);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_params_146_, 7);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_params_146_, 6);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_params_146_, 5);
lean_dec(v_unused_187_);
v_unused_188_ = lean_ctor_get(v_params_146_, 4);
lean_dec(v_unused_188_);
v_unused_189_ = lean_ctor_get(v_params_146_, 3);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_params_146_, 2);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_params_146_, 1);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_params_146_, 0);
lean_dec(v_unused_192_);
v___x_161_ = v_params_146_;
v_isShared_162_ = v_isSharedCheck_183_;
goto v_resetjp_160_;
}
else
{
lean_dec(v_params_146_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_183_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v_v_163_; lean_object* v_casesTypes_164_; lean_object* v_extThms_165_; lean_object* v_funCC_166_; lean_object* v_ematch_167_; lean_object* v_inj_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_182_; 
v_v_163_ = lean_array_fget(v_extensions_149_, v___x_157_);
v_casesTypes_164_ = lean_ctor_get(v_v_163_, 0);
v_extThms_165_ = lean_ctor_get(v_v_163_, 1);
v_funCC_166_ = lean_ctor_get(v_v_163_, 2);
v_ematch_167_ = lean_ctor_get(v_v_163_, 3);
v_inj_168_ = lean_ctor_get(v_v_163_, 4);
v_isSharedCheck_182_ = !lean_is_exclusive(v_v_163_);
if (v_isSharedCheck_182_ == 0)
{
v___x_170_ = v_v_163_;
v_isShared_171_ = v_isSharedCheck_182_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_inj_168_);
lean_inc(v_ematch_167_);
lean_inc(v_funCC_166_);
lean_inc(v_extThms_165_);
lean_inc(v_casesTypes_164_);
lean_dec(v_v_163_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_182_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v_xs_x27_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_172_ = lean_box(0);
v_xs_x27_173_ = lean_array_fset(v_extensions_149_, v___x_157_, v___x_172_);
v___x_174_ = l_Lean_NameSet_insert(v_funCC_166_, v_declName_147_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 2, v___x_174_);
v___x_176_ = v___x_170_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_casesTypes_164_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_extThms_165_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v_ematch_167_);
lean_ctor_set(v_reuseFailAlloc_181_, 4, v_inj_168_);
v___x_176_ = v_reuseFailAlloc_181_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_array_fset(v_xs_x27_173_, v___x_157_, v___x_176_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v___x_177_);
v___x_179_ = v___x_161_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_config_148_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_180_, 2, v_extra_150_);
lean_ctor_set(v_reuseFailAlloc_180_, 3, v_extraInj_151_);
lean_ctor_set(v_reuseFailAlloc_180_, 4, v_extraFacts_152_);
lean_ctor_set(v_reuseFailAlloc_180_, 5, v_symPrios_153_);
lean_ctor_set(v_reuseFailAlloc_180_, 6, v_norm_154_);
lean_ctor_set(v_reuseFailAlloc_180_, 7, v_normProcs_155_);
lean_ctor_set(v_reuseFailAlloc_180_, 8, v_anchorRefs_x3f_156_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(lean_object* v_declName_193_, lean_object* v_as_194_, size_t v_i_195_, size_t v_stop_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = lean_usize_dec_eq(v_i_195_, v_stop_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v_ematch_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_198_ = lean_array_uget_borrowed(v_as_194_, v_i_195_);
v_ematch_199_ = lean_ctor_get(v___x_198_, 3);
lean_inc(v_declName_193_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v_declName_193_);
v___x_201_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_ematch_199_, v___x_200_);
lean_dec_ref_known(v___x_200_, 1);
if (v___x_201_ == 0)
{
size_t v___x_202_; size_t v___x_203_; 
v___x_202_ = ((size_t)1ULL);
v___x_203_ = lean_usize_add(v_i_195_, v___x_202_);
v_i_195_ = v___x_203_;
goto _start;
}
else
{
lean_dec(v_declName_193_);
return v___x_201_;
}
}
else
{
uint8_t v___x_205_; 
lean_dec(v_declName_193_);
v___x_205_ = 0;
return v___x_205_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_193_ = stack[0].m_obj;
lean_object* v_as_194_ = stack[1].m_obj;
size_t v_i_195_ = stack[2].m_num;
size_t v_stop_196_ = stack[3].m_num;
uint8_t v_res_206_;
v_res_206_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(v_declName_193_, v_as_194_, v_i_195_, v_stop_196_);
stack->m_num = v_res_206_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0___boxed(lean_object* v_declName_207_, lean_object* v_as_208_, lean_object* v_i_209_, lean_object* v_stop_210_){
_start:
{
size_t v_i_boxed_211_; size_t v_stop_boxed_212_; uint8_t v_res_213_; lean_object* v_r_214_; 
v_i_boxed_211_ = lean_unbox_usize(v_i_209_);
lean_dec(v_i_209_);
v_stop_boxed_212_ = lean_unbox_usize(v_stop_210_);
lean_dec(v_stop_210_);
v_res_213_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(v_declName_207_, v_as_208_, v_i_boxed_211_, v_stop_boxed_212_);
lean_dec_ref(v_as_208_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(lean_object* v_params_215_, lean_object* v_declName_216_){
_start:
{
lean_object* v_extensions_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_extensions_217_ = lean_ctor_get(v_params_215_, 1);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_array_get_size(v_extensions_217_);
v___x_220_ = lean_nat_dec_lt(v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_dec(v_declName_216_);
return v___x_220_;
}
else
{
if (v___x_220_ == 0)
{
lean_dec(v_declName_216_);
return v___x_220_;
}
else
{
size_t v___x_221_; size_t v___x_222_; uint8_t v___x_223_; 
v___x_221_ = ((size_t)0ULL);
v___x_222_ = lean_usize_of_nat(v___x_219_);
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(v_declName_216_, v_extensions_217_, v___x_221_, v___x_222_);
return v___x_223_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_215_ = stack[0].m_obj;
lean_object* v_declName_216_ = stack[1].m_obj;
uint8_t v_res_224_;
v_res_224_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_215_, v_declName_216_);
stack->m_num = v_res_224_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch___boxed(lean_object* v_params_225_, lean_object* v_declName_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_225_, v_declName_226_);
lean_dec_ref(v_params_225_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(lean_object* v_declName_229_, lean_object* v_as_230_, size_t v_i_231_, size_t v_stop_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = lean_usize_dec_eq(v_i_231_, v_stop_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v_inj_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_234_ = lean_array_uget_borrowed(v_as_230_, v_i_231_);
v_inj_235_ = lean_ctor_get(v___x_234_, 4);
lean_inc(v_declName_229_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v_declName_229_);
v___x_237_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_235_, v___x_236_);
lean_dec_ref_known(v___x_236_, 1);
if (v___x_237_ == 0)
{
size_t v___x_238_; size_t v___x_239_; 
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_add(v_i_231_, v___x_238_);
v_i_231_ = v___x_239_;
goto _start;
}
else
{
lean_dec(v_declName_229_);
return v___x_237_;
}
}
else
{
uint8_t v___x_241_; 
lean_dec(v_declName_229_);
v___x_241_ = 0;
return v___x_241_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_229_ = stack[0].m_obj;
lean_object* v_as_230_ = stack[1].m_obj;
size_t v_i_231_ = stack[2].m_num;
size_t v_stop_232_ = stack[3].m_num;
uint8_t v_res_242_;
v_res_242_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(v_declName_229_, v_as_230_, v_i_231_, v_stop_232_);
stack->m_num = v_res_242_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0___boxed(lean_object* v_declName_243_, lean_object* v_as_244_, lean_object* v_i_245_, lean_object* v_stop_246_){
_start:
{
size_t v_i_boxed_247_; size_t v_stop_boxed_248_; uint8_t v_res_249_; lean_object* v_r_250_; 
v_i_boxed_247_ = lean_unbox_usize(v_i_245_);
lean_dec(v_i_245_);
v_stop_boxed_248_ = lean_unbox_usize(v_stop_246_);
lean_dec(v_stop_246_);
v_res_249_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(v_declName_243_, v_as_244_, v_i_boxed_247_, v_stop_boxed_248_);
lean_dec_ref(v_as_244_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(lean_object* v_params_251_, lean_object* v_declName_252_){
_start:
{
lean_object* v_extensions_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_extensions_253_ = lean_ctor_get(v_params_251_, 1);
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_array_get_size(v_extensions_253_);
v___x_256_ = lean_nat_dec_lt(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec(v_declName_252_);
return v___x_256_;
}
else
{
if (v___x_256_ == 0)
{
lean_dec(v_declName_252_);
return v___x_256_;
}
else
{
size_t v___x_257_; size_t v___x_258_; uint8_t v___x_259_; 
v___x_257_ = ((size_t)0ULL);
v___x_258_ = lean_usize_of_nat(v___x_255_);
v___x_259_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(v_declName_252_, v_extensions_253_, v___x_257_, v___x_258_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_251_ = stack[0].m_obj;
lean_object* v_declName_252_ = stack[1].m_obj;
uint8_t v_res_260_;
v_res_260_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_params_251_, v_declName_252_);
stack->m_num = v_res_260_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem___boxed(lean_object* v_params_261_, lean_object* v_declName_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_params_261_, v_declName_262_);
lean_dec_ref(v_params_261_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(lean_object* v_params_265_, lean_object* v_declName_266_){
_start:
{
lean_object* v_config_267_; lean_object* v_extensions_268_; lean_object* v_extra_269_; lean_object* v_extraInj_270_; lean_object* v_extraFacts_271_; lean_object* v_symPrios_272_; lean_object* v_norm_273_; lean_object* v_normProcs_274_; lean_object* v_anchorRefs_x3f_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_config_267_ = lean_ctor_get(v_params_265_, 0);
v_extensions_268_ = lean_ctor_get(v_params_265_, 1);
v_extra_269_ = lean_ctor_get(v_params_265_, 2);
v_extraInj_270_ = lean_ctor_get(v_params_265_, 3);
v_extraFacts_271_ = lean_ctor_get(v_params_265_, 4);
v_symPrios_272_ = lean_ctor_get(v_params_265_, 5);
v_norm_273_ = lean_ctor_get(v_params_265_, 6);
v_normProcs_274_ = lean_ctor_get(v_params_265_, 7);
v_anchorRefs_x3f_275_ = lean_ctor_get(v_params_265_, 8);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_array_get_size(v_extensions_268_);
v___x_278_ = lean_nat_dec_lt(v___x_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_dec(v_declName_266_);
return v_params_265_;
}
else
{
lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_303_; 
lean_inc(v_anchorRefs_x3f_275_);
lean_inc_ref(v_normProcs_274_);
lean_inc_ref(v_norm_273_);
lean_inc_ref(v_symPrios_272_);
lean_inc_ref(v_extraFacts_271_);
lean_inc_ref(v_extraInj_270_);
lean_inc_ref(v_extra_269_);
lean_inc_ref(v_extensions_268_);
lean_inc_ref(v_config_267_);
v_isSharedCheck_303_ = !lean_is_exclusive(v_params_265_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; lean_object* v_unused_305_; lean_object* v_unused_306_; lean_object* v_unused_307_; lean_object* v_unused_308_; lean_object* v_unused_309_; lean_object* v_unused_310_; lean_object* v_unused_311_; lean_object* v_unused_312_; 
v_unused_304_ = lean_ctor_get(v_params_265_, 8);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_params_265_, 7);
lean_dec(v_unused_305_);
v_unused_306_ = lean_ctor_get(v_params_265_, 6);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_params_265_, 5);
lean_dec(v_unused_307_);
v_unused_308_ = lean_ctor_get(v_params_265_, 4);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_params_265_, 3);
lean_dec(v_unused_309_);
v_unused_310_ = lean_ctor_get(v_params_265_, 2);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v_params_265_, 1);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_params_265_, 0);
lean_dec(v_unused_312_);
v___x_280_ = v_params_265_;
v_isShared_281_ = v_isSharedCheck_303_;
goto v_resetjp_279_;
}
else
{
lean_dec(v_params_265_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_303_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_v_282_; lean_object* v_casesTypes_283_; lean_object* v_extThms_284_; lean_object* v_funCC_285_; lean_object* v_ematch_286_; lean_object* v_inj_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_302_; 
v_v_282_ = lean_array_fget(v_extensions_268_, v___x_276_);
v_casesTypes_283_ = lean_ctor_get(v_v_282_, 0);
v_extThms_284_ = lean_ctor_get(v_v_282_, 1);
v_funCC_285_ = lean_ctor_get(v_v_282_, 2);
v_ematch_286_ = lean_ctor_get(v_v_282_, 3);
v_inj_287_ = lean_ctor_get(v_v_282_, 4);
v_isSharedCheck_302_ = !lean_is_exclusive(v_v_282_);
if (v_isSharedCheck_302_ == 0)
{
v___x_289_ = v_v_282_;
v_isShared_290_ = v_isSharedCheck_302_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_inj_287_);
lean_inc(v_ematch_286_);
lean_inc(v_funCC_285_);
lean_inc(v_extThms_284_);
lean_inc(v_casesTypes_283_);
lean_dec(v_v_282_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_302_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v_xs_x27_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_291_ = lean_box(0);
v_xs_x27_292_ = lean_array_fset(v_extensions_268_, v___x_276_, v___x_291_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v_declName_266_);
v___x_294_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_ematch_286_, v___x_293_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 3, v___x_294_);
v___x_296_ = v___x_289_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_casesTypes_283_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_extThms_284_);
lean_ctor_set(v_reuseFailAlloc_301_, 2, v_funCC_285_);
lean_ctor_set(v_reuseFailAlloc_301_, 3, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_301_, 4, v_inj_287_);
v___x_296_ = v_reuseFailAlloc_301_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_array_fset(v_xs_x27_292_, v___x_276_, v___x_296_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v___x_297_);
v___x_299_ = v___x_280_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_config_267_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v_extra_269_);
lean_ctor_set(v_reuseFailAlloc_300_, 3, v_extraInj_270_);
lean_ctor_set(v_reuseFailAlloc_300_, 4, v_extraFacts_271_);
lean_ctor_set(v_reuseFailAlloc_300_, 5, v_symPrios_272_);
lean_ctor_set(v_reuseFailAlloc_300_, 6, v_norm_273_);
lean_ctor_set(v_reuseFailAlloc_300_, 7, v_normProcs_274_);
lean_ctor_set(v_reuseFailAlloc_300_, 8, v_anchorRefs_x3f_275_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(lean_object* v_params_313_, uint8_t v___x_314_, lean_object* v_as_315_, size_t v_i_316_, size_t v_stop_317_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = lean_usize_dec_eq(v_i_316_, v_stop_317_);
if (v___x_318_ == 0)
{
uint8_t v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_319_ = 1;
v___x_320_ = lean_array_uget_borrowed(v_as_315_, v_i_316_);
lean_inc(v___x_320_);
v___x_321_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_313_, v___x_320_);
if (v___x_321_ == 0)
{
return v___x_319_;
}
else
{
if (v___x_314_ == 0)
{
size_t v___x_322_; size_t v___x_323_; 
v___x_322_ = ((size_t)1ULL);
v___x_323_ = lean_usize_add(v_i_316_, v___x_322_);
v_i_316_ = v___x_323_;
goto _start;
}
else
{
return v___x_319_;
}
}
}
else
{
uint8_t v___x_325_; 
v___x_325_ = 0;
return v___x_325_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_313_ = stack[0].m_obj;
uint8_t v___x_314_ = stack[1].m_num;
lean_object* v_as_315_ = stack[2].m_obj;
size_t v_i_316_ = stack[3].m_num;
size_t v_stop_317_ = stack[4].m_num;
uint8_t v_res_326_;
v_res_326_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_313_, v___x_314_, v_as_315_, v_i_316_, v_stop_317_);
stack->m_num = v_res_326_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1___boxed(lean_object* v_params_327_, lean_object* v___x_328_, lean_object* v_as_329_, lean_object* v_i_330_, lean_object* v_stop_331_){
_start:
{
uint8_t v___x_1646__boxed_332_; size_t v_i_boxed_333_; size_t v_stop_boxed_334_; uint8_t v_res_335_; lean_object* v_r_336_; 
v___x_1646__boxed_332_ = lean_unbox(v___x_328_);
v_i_boxed_333_ = lean_unbox_usize(v_i_330_);
lean_dec(v_i_330_);
v_stop_boxed_334_ = lean_unbox_usize(v_stop_331_);
lean_dec(v_stop_331_);
v_res_335_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_327_, v___x_1646__boxed_332_, v_as_329_, v_i_boxed_333_, v_stop_boxed_334_);
lean_dec_ref(v_as_329_);
lean_dec_ref(v_params_327_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(lean_object* v_as_337_, size_t v_i_338_, size_t v_stop_339_, lean_object* v_b_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = lean_usize_dec_eq(v_i_338_, v_stop_339_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; size_t v___x_344_; size_t v___x_345_; 
v___x_342_ = lean_array_uget_borrowed(v_as_337_, v_i_338_);
lean_inc(v___x_342_);
v___x_343_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(v_b_340_, v___x_342_);
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_add(v_i_338_, v___x_344_);
v_i_338_ = v___x_345_;
v_b_340_ = v___x_343_;
goto _start;
}
else
{
return v_b_340_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_337_ = stack[0].m_obj;
size_t v_i_338_ = stack[1].m_num;
size_t v_stop_339_ = stack[2].m_num;
lean_object* v_b_340_ = stack[3].m_obj;
lean_object* v_res_347_;
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_as_337_, v_i_338_, v_stop_339_, v_b_340_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0___boxed(lean_object* v_as_348_, lean_object* v_i_349_, lean_object* v_stop_350_, lean_object* v_b_351_){
_start:
{
size_t v_i_boxed_352_; size_t v_stop_boxed_353_; lean_object* v_res_354_; 
v_i_boxed_352_ = lean_unbox_usize(v_i_349_);
lean_dec(v_i_349_);
v_stop_boxed_353_ = lean_unbox_usize(v_stop_350_);
lean_dec(v_stop_350_);
v_res_354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_as_348_, v_i_boxed_352_, v_stop_boxed_353_, v_b_351_);
lean_dec_ref(v_as_348_);
return v_res_354_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(lean_object* v_params_355_, lean_object* v_declName_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_365_; lean_object* v_env_366_; uint8_t v___x_367_; 
v___x_365_ = lean_st_ref_get(v_a_360_);
v_env_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_env_366_);
lean_dec(v___x_365_);
lean_inc(v_declName_356_);
v___x_367_ = l_Lean_wasOriginallyTheorem(v_env_366_, v_declName_356_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
lean_inc(v_declName_356_);
v___x_368_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_413_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_413_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_413_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_413_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
if (lean_obj_tag(v_a_369_) == 1)
{
lean_object* v_val_373_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_val_373_ = lean_ctor_get(v_a_369_, 0);
lean_inc(v_val_373_);
lean_dec_ref_known(v_a_369_, 1);
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_array_get_size(v_val_373_);
v___x_399_ = lean_nat_dec_lt(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_dec(v_declName_356_);
goto v___jp_374_;
}
else
{
if (v___x_399_ == 0)
{
lean_dec(v_declName_356_);
goto v___jp_374_;
}
else
{
size_t v___x_400_; size_t v___x_401_; uint8_t v___x_402_; 
v___x_400_ = ((size_t)0ULL);
v___x_401_ = lean_usize_of_nat(v___x_398_);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_355_, v___x_367_, v_val_373_, v___x_400_, v___x_401_);
if (v___x_402_ == 0)
{
lean_dec(v_declName_356_);
goto v___jp_374_;
}
else
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_356_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_dec_ref_known(v___x_403_, 1);
goto v___jp_374_;
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec(v_val_373_);
lean_del_object(v___x_371_);
lean_dec_ref(v_params_355_);
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
}
v___jp_374_:
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_array_get_size(v_val_373_);
v___x_377_ = lean_nat_dec_lt(v___x_375_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_379_; 
lean_dec(v_val_373_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v_params_355_);
v___x_379_ = v___x_371_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_params_355_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
else
{
uint8_t v___x_381_; 
v___x_381_ = lean_nat_dec_le(v___x_376_, v___x_376_);
if (v___x_381_ == 0)
{
if (v___x_377_ == 0)
{
lean_object* v___x_383_; 
lean_dec(v_val_373_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v_params_355_);
v___x_383_ = v___x_371_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_params_355_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
else
{
size_t v___x_385_; size_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_385_ = ((size_t)0ULL);
v___x_386_ = lean_usize_of_nat(v___x_376_);
v___x_387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_val_373_, v___x_385_, v___x_386_, v_params_355_);
lean_dec(v_val_373_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_387_);
v___x_389_ = v___x_371_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
size_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_391_ = ((size_t)0ULL);
v___x_392_ = lean_usize_of_nat(v___x_376_);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_val_373_, v___x_391_, v___x_392_, v_params_355_);
lean_dec(v_val_373_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_393_);
v___x_395_ = v___x_371_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
else
{
lean_object* v___x_412_; 
lean_del_object(v___x_371_);
lean_dec(v_a_369_);
lean_dec_ref(v_params_355_);
v___x_412_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_356_, v_a_359_, v_a_360_);
return v___x_412_;
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_declName_356_);
lean_dec_ref(v_params_355_);
v_a_414_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_368_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_368_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
uint8_t v___x_422_; 
lean_inc(v_declName_356_);
v___x_422_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_355_, v_declName_356_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_inc(v_declName_356_);
v___x_423_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_356_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_dec_ref_known(v___x_423_, 1);
goto v___jp_362_;
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v_declName_356_);
lean_dec_ref(v_params_355_);
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
goto v___jp_362_;
}
}
v___jp_362_:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(v_params_355_, v_declName_356_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_355_ = stack[0].m_obj;
lean_object* v_declName_356_ = stack[1].m_obj;
lean_object* v_a_357_ = stack[2].m_obj;
lean_object* v_a_358_ = stack[3].m_obj;
lean_object* v_a_359_ = stack[4].m_obj;
lean_object* v_a_360_ = stack[5].m_obj;
lean_object* v_res_432_;
v_res_432_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_params_355_, v_declName_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch___boxed(lean_object* v_params_433_, lean_object* v_declName_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_params_433_, v_declName_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(lean_object* v_params_441_, lean_object* v_declName_442_){
_start:
{
lean_object* v_config_443_; lean_object* v_extensions_444_; lean_object* v_extra_445_; lean_object* v_extraInj_446_; lean_object* v_extraFacts_447_; lean_object* v_symPrios_448_; lean_object* v_norm_449_; lean_object* v_normProcs_450_; lean_object* v_anchorRefs_x3f_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_config_443_ = lean_ctor_get(v_params_441_, 0);
v_extensions_444_ = lean_ctor_get(v_params_441_, 1);
v_extra_445_ = lean_ctor_get(v_params_441_, 2);
v_extraInj_446_ = lean_ctor_get(v_params_441_, 3);
v_extraFacts_447_ = lean_ctor_get(v_params_441_, 4);
v_symPrios_448_ = lean_ctor_get(v_params_441_, 5);
v_norm_449_ = lean_ctor_get(v_params_441_, 6);
v_normProcs_450_ = lean_ctor_get(v_params_441_, 7);
v_anchorRefs_x3f_451_ = lean_ctor_get(v_params_441_, 8);
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_array_get_size(v_extensions_444_);
v___x_454_ = lean_nat_dec_lt(v___x_452_, v___x_453_);
if (v___x_454_ == 0)
{
lean_dec(v_declName_442_);
return v_params_441_;
}
else
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_479_; 
lean_inc(v_anchorRefs_x3f_451_);
lean_inc_ref(v_normProcs_450_);
lean_inc_ref(v_norm_449_);
lean_inc_ref(v_symPrios_448_);
lean_inc_ref(v_extraFacts_447_);
lean_inc_ref(v_extraInj_446_);
lean_inc_ref(v_extra_445_);
lean_inc_ref(v_extensions_444_);
lean_inc_ref(v_config_443_);
v_isSharedCheck_479_ = !lean_is_exclusive(v_params_441_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; lean_object* v_unused_481_; lean_object* v_unused_482_; lean_object* v_unused_483_; lean_object* v_unused_484_; lean_object* v_unused_485_; lean_object* v_unused_486_; lean_object* v_unused_487_; lean_object* v_unused_488_; 
v_unused_480_ = lean_ctor_get(v_params_441_, 8);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_params_441_, 7);
lean_dec(v_unused_481_);
v_unused_482_ = lean_ctor_get(v_params_441_, 6);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v_params_441_, 5);
lean_dec(v_unused_483_);
v_unused_484_ = lean_ctor_get(v_params_441_, 4);
lean_dec(v_unused_484_);
v_unused_485_ = lean_ctor_get(v_params_441_, 3);
lean_dec(v_unused_485_);
v_unused_486_ = lean_ctor_get(v_params_441_, 2);
lean_dec(v_unused_486_);
v_unused_487_ = lean_ctor_get(v_params_441_, 1);
lean_dec(v_unused_487_);
v_unused_488_ = lean_ctor_get(v_params_441_, 0);
lean_dec(v_unused_488_);
v___x_456_ = v_params_441_;
v_isShared_457_ = v_isSharedCheck_479_;
goto v_resetjp_455_;
}
else
{
lean_dec(v_params_441_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_479_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_v_458_; lean_object* v_casesTypes_459_; lean_object* v_extThms_460_; lean_object* v_funCC_461_; lean_object* v_ematch_462_; lean_object* v_inj_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_478_; 
v_v_458_ = lean_array_fget(v_extensions_444_, v___x_452_);
v_casesTypes_459_ = lean_ctor_get(v_v_458_, 0);
v_extThms_460_ = lean_ctor_get(v_v_458_, 1);
v_funCC_461_ = lean_ctor_get(v_v_458_, 2);
v_ematch_462_ = lean_ctor_get(v_v_458_, 3);
v_inj_463_ = lean_ctor_get(v_v_458_, 4);
v_isSharedCheck_478_ = !lean_is_exclusive(v_v_458_);
if (v_isSharedCheck_478_ == 0)
{
v___x_465_ = v_v_458_;
v_isShared_466_ = v_isSharedCheck_478_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_inj_463_);
lean_inc(v_ematch_462_);
lean_inc(v_funCC_461_);
lean_inc(v_extThms_460_);
lean_inc(v_casesTypes_459_);
lean_dec(v_v_458_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_478_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v_xs_x27_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_467_ = lean_box(0);
v_xs_x27_468_ = lean_array_fset(v_extensions_444_, v___x_452_, v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v_declName_442_);
v___x_470_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_inj_463_, v___x_469_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 4, v___x_470_);
v___x_472_ = v___x_465_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_casesTypes_459_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_extThms_460_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_funCC_461_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_ematch_462_);
lean_ctor_set(v_reuseFailAlloc_477_, 4, v___x_470_);
v___x_472_ = v_reuseFailAlloc_477_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = lean_array_fset(v_xs_x27_468_, v___x_452_, v___x_472_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 1, v___x_473_);
v___x_475_ = v___x_456_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_config_443_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v_extra_445_);
lean_ctor_set(v_reuseFailAlloc_476_, 3, v_extraInj_446_);
lean_ctor_set(v_reuseFailAlloc_476_, 4, v_extraFacts_447_);
lean_ctor_set(v_reuseFailAlloc_476_, 5, v_symPrios_448_);
lean_ctor_set(v_reuseFailAlloc_476_, 6, v_norm_449_);
lean_ctor_set(v_reuseFailAlloc_476_, 7, v_normProcs_450_);
lean_ctor_set(v_reuseFailAlloc_476_, 8, v_anchorRefs_x3f_451_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(lean_object* v_origin_489_, lean_object* v_as_490_, size_t v_sz_491_, size_t v_i_492_, lean_object* v_b_493_){
_start:
{
lean_object* v_a_495_; uint8_t v___x_499_; 
v___x_499_ = lean_usize_dec_lt(v_i_492_, v_sz_491_);
if (v___x_499_ == 0)
{
return v_b_493_;
}
else
{
lean_object* v_a_500_; lean_object* v_ematch_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_a_500_ = lean_array_uget_borrowed(v_as_490_, v_i_492_);
v_ematch_501_ = lean_ctor_get(v_a_500_, 3);
v___x_502_ = l_Lean_Meta_Grind_EMatchTheorems_getKindsFor(v_ematch_501_, v_origin_489_);
v___x_503_ = l_List_isEmpty___redArg(v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
v___x_504_ = l_List_appendTR___redArg(v_b_493_, v___x_502_);
v_a_495_ = v___x_504_;
goto v___jp_494_;
}
else
{
lean_dec(v___x_502_);
v_a_495_ = v_b_493_;
goto v___jp_494_;
}
}
v___jp_494_:
{
size_t v___x_496_; size_t v___x_497_; 
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_492_, v___x_496_);
v_i_492_ = v___x_497_;
v_b_493_ = v_a_495_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_origin_489_ = stack[0].m_obj;
lean_object* v_as_490_ = stack[1].m_obj;
size_t v_sz_491_ = stack[2].m_num;
size_t v_i_492_ = stack[3].m_num;
lean_object* v_b_493_ = stack[4].m_obj;
lean_object* v_res_505_;
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_489_, v_as_490_, v_sz_491_, v_i_492_, v_b_493_);
stack->m_obj
 = v_res_505_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0___boxed(lean_object* v_origin_506_, lean_object* v_as_507_, lean_object* v_sz_508_, lean_object* v_i_509_, lean_object* v_b_510_){
_start:
{
size_t v_sz_boxed_511_; size_t v_i_boxed_512_; lean_object* v_res_513_; 
v_sz_boxed_511_ = lean_unbox_usize(v_sz_508_);
lean_dec(v_sz_508_);
v_i_boxed_512_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_506_, v_as_507_, v_sz_boxed_511_, v_i_boxed_512_, v_b_510_);
lean_dec_ref(v_as_507_);
lean_dec_ref(v_origin_506_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(lean_object* v_s_514_, lean_object* v_origin_515_){
_start:
{
lean_object* v_result_516_; size_t v_sz_517_; size_t v___x_518_; lean_object* v___x_519_; 
v_result_516_ = lean_box(0);
v_sz_517_ = lean_array_size(v_s_514_);
v___x_518_ = ((size_t)0ULL);
v___x_519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_515_, v_s_514_, v_sz_517_, v___x_518_, v_result_516_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor___boxed(lean_object* v_s_520_, lean_object* v_origin_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_520_, v_origin_521_);
lean_dec_ref(v_origin_521_);
lean_dec_ref(v_s_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(lean_object* v_upperBound_523_, lean_object* v_s_524_, lean_object* v_origin_525_, lean_object* v_a_526_, lean_object* v_b_527_){
_start:
{
lean_object* v_a_529_; uint8_t v___x_533_; 
v___x_533_ = lean_nat_dec_lt(v_a_526_, v_upperBound_523_);
if (v___x_533_ == 0)
{
lean_dec(v_a_526_);
return v_b_527_;
}
else
{
lean_object* v___x_534_; lean_object* v_ematch_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_534_ = lean_array_fget_borrowed(v_s_524_, v_a_526_);
v_ematch_535_ = lean_ctor_get(v___x_534_, 3);
v___x_536_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_ematch_535_, v_origin_525_);
v___x_537_ = l_List_isEmpty___redArg(v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
v___x_538_ = l_List_appendTR___redArg(v_b_527_, v___x_536_);
v_a_529_ = v___x_538_;
goto v___jp_528_;
}
else
{
lean_dec(v___x_536_);
v_a_529_ = v_b_527_;
goto v___jp_528_;
}
}
v___jp_528_:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_add(v_a_526_, v___x_530_);
lean_dec(v_a_526_);
v_a_526_ = v___x_531_;
v_b_527_ = v_a_529_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg___boxed(lean_object* v_upperBound_539_, lean_object* v_s_540_, lean_object* v_origin_541_, lean_object* v_a_542_, lean_object* v_b_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v_upperBound_539_, v_s_540_, v_origin_541_, v_a_542_, v_b_543_);
lean_dec_ref(v_origin_541_);
lean_dec_ref(v_s_540_);
lean_dec(v_upperBound_539_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find(lean_object* v_s_545_, lean_object* v_origin_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_r_549_; lean_object* v___x_550_; 
v___x_547_ = lean_array_get_size(v_s_545_);
v___x_548_ = lean_unsigned_to_nat(0u);
v_r_549_ = lean_box(0);
v___x_550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v___x_547_, v_s_545_, v_origin_546_, v___x_548_, v_r_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find___boxed(lean_object* v_s_551_, lean_object* v_origin_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Meta_Grind_ExtensionStateArray_find(v_s_551_, v_origin_552_);
lean_dec_ref(v_origin_552_);
lean_dec_ref(v_s_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(lean_object* v_upperBound_554_, lean_object* v_s_555_, lean_object* v_origin_556_, lean_object* v_inst_557_, lean_object* v_R_558_, lean_object* v_a_559_, lean_object* v_b_560_, lean_object* v_c_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v_upperBound_554_, v_s_555_, v_origin_556_, v_a_559_, v_b_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___boxed(lean_object* v_upperBound_563_, lean_object* v_s_564_, lean_object* v_origin_565_, lean_object* v_inst_566_, lean_object* v_R_567_, lean_object* v_a_568_, lean_object* v_b_569_, lean_object* v_c_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(v_upperBound_563_, v_s_564_, v_origin_565_, v_inst_566_, v_R_567_, v_a_568_, v_b_569_, v_c_570_);
lean_dec_ref(v_origin_565_);
lean_dec_ref(v_s_564_);
lean_dec(v_upperBound_563_);
return v_res_571_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(lean_object* v_msgData_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; lean_object* v_env_579_; uint8_t v___x_580_; lean_object* v_env_581_; lean_object* v___x_582_; lean_object* v_toCold_583_; lean_object* v_mctx_584_; lean_object* v_lctx_585_; lean_object* v_options_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_578_ = lean_st_ref_get(v___y_576_);
v_env_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc_ref(v_env_579_);
lean_dec(v___x_578_);
v___x_580_ = 0;
v_env_581_ = l_Lean_Environment_setRecordingDeps(v_env_579_, v___x_580_);
v___x_582_ = lean_st_ref_get(v___y_574_);
v_toCold_583_ = lean_ctor_get(v___y_575_, 0);
v_mctx_584_ = lean_ctor_get(v___x_582_, 0);
lean_inc_ref(v_mctx_584_);
lean_dec(v___x_582_);
v_lctx_585_ = lean_ctor_get(v___y_573_, 2);
v_options_586_ = lean_ctor_get(v_toCold_583_, 2);
lean_inc_ref(v_options_586_);
lean_inc_ref(v_lctx_585_);
v___x_587_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_587_, 0, v_env_581_);
lean_ctor_set(v___x_587_, 1, v_mctx_584_);
lean_ctor_set(v___x_587_, 2, v_lctx_585_);
lean_ctor_set(v___x_587_, 3, v_options_586_);
v___x_588_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_msgData_572_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_572_ = stack[0].m_obj;
lean_object* v___y_573_ = stack[1].m_obj;
lean_object* v___y_574_ = stack[2].m_obj;
lean_object* v___y_575_ = stack[3].m_obj;
lean_object* v___y_576_ = stack[4].m_obj;
lean_object* v_res_590_;
v_res_590_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msgData_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
stack->m_obj
 = v_res_590_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_msgData_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msgData_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
return v_res_597_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_598_, lean_object* v_opt_599_){
_start:
{
lean_object* v_name_600_; lean_object* v_defValue_601_; lean_object* v_map_602_; lean_object* v___x_603_; 
v_name_600_ = lean_ctor_get(v_opt_599_, 0);
v_defValue_601_ = lean_ctor_get(v_opt_599_, 1);
v_map_602_ = lean_ctor_get(v_opts_598_, 0);
v___x_603_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_602_, v_name_600_);
if (lean_obj_tag(v___x_603_) == 0)
{
uint8_t v___x_604_; 
v___x_604_ = lean_unbox(v_defValue_601_);
return v___x_604_;
}
else
{
lean_object* v_val_605_; 
v_val_605_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v___x_603_, 1);
if (lean_obj_tag(v_val_605_) == 1)
{
uint8_t v_v_606_; 
v_v_606_ = lean_ctor_get_uint8(v_val_605_, 0);
lean_dec_ref_known(v_val_605_, 0);
return v_v_606_;
}
else
{
uint8_t v___x_607_; 
lean_dec(v_val_605_);
v___x_607_ = lean_unbox(v_defValue_601_);
return v___x_607_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_598_ = stack[0].m_obj;
lean_object* v_opt_599_ = stack[1].m_obj;
uint8_t v_res_608_;
v_res_608_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_opts_598_, v_opt_599_);
stack->m_num = v_res_608_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_609_, lean_object* v_opt_610_){
_start:
{
uint8_t v_res_611_; lean_object* v_r_612_; 
v_res_611_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_opts_609_, v_opt_610_);
lean_dec_ref(v_opt_610_);
lean_dec_ref(v_opts_609_);
v_r_612_ = lean_box(v_res_611_);
return v_r_612_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_621_, uint8_t v___y_622_, lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_623_) == 1)
{
lean_object* v_pre_624_; 
v_pre_624_ = lean_ctor_get(v_x_623_, 0);
switch(lean_obj_tag(v_pre_624_))
{
case 1:
{
lean_object* v_pre_625_; 
v_pre_625_ = lean_ctor_get(v_pre_624_, 0);
switch(lean_obj_tag(v_pre_625_))
{
case 0:
{
lean_object* v_str_626_; lean_object* v_str_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v_str_626_ = lean_ctor_get(v_x_623_, 1);
v_str_627_ = lean_ctor_get(v_pre_624_, 1);
v___x_628_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_629_ = lean_string_dec_eq(v_str_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_631_ = lean_string_dec_eq(v_str_627_, v___x_630_);
if (v___x_631_ == 0)
{
return v___x_631_;
}
else
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_633_ = lean_string_dec_eq(v_str_626_, v___x_632_);
if (v___x_633_ == 0)
{
return v___x_633_;
}
else
{
return v_suppressElabErrors_621_;
}
}
}
else
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_635_ = lean_string_dec_eq(v_str_626_, v___x_634_);
if (v___x_635_ == 0)
{
return v___x_635_;
}
else
{
return v_suppressElabErrors_621_;
}
}
}
case 1:
{
lean_object* v_pre_636_; 
v_pre_636_ = lean_ctor_get(v_pre_625_, 0);
if (lean_obj_tag(v_pre_636_) == 0)
{
lean_object* v_str_637_; lean_object* v_str_638_; lean_object* v_str_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_str_637_ = lean_ctor_get(v_x_623_, 1);
v_str_638_ = lean_ctor_get(v_pre_624_, 1);
v_str_639_ = lean_ctor_get(v_pre_625_, 1);
v___x_640_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_641_ = lean_string_dec_eq(v_str_639_, v___x_640_);
if (v___x_641_ == 0)
{
return v___x_641_;
}
else
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_643_ = lean_string_dec_eq(v_str_638_, v___x_642_);
if (v___x_643_ == 0)
{
return v___x_643_;
}
else
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_645_ = lean_string_dec_eq(v_str_637_, v___x_644_);
if (v___x_645_ == 0)
{
return v___x_645_;
}
else
{
return v_suppressElabErrors_621_;
}
}
}
}
else
{
return v___y_622_;
}
}
default: 
{
return v___y_622_;
}
}
}
case 0:
{
lean_object* v_str_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_str_646_ = lean_ctor_get(v_x_623_, 1);
v___x_647_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_648_ = lean_string_dec_eq(v_str_646_, v___x_647_);
if (v___x_648_ == 0)
{
return v___x_648_;
}
else
{
return v_suppressElabErrors_621_;
}
}
default: 
{
return v___y_622_;
}
}
}
else
{
return v___y_622_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_621_ = stack[0].m_num;
uint8_t v___y_622_ = stack[1].m_num;
lean_object* v_x_623_ = stack[2].m_obj;
uint8_t v_res_649_;
v_res_649_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_621_, v___y_622_, v_x_623_);
stack->m_num = v_res_649_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_650_, lean_object* v___y_651_, lean_object* v_x_652_){
_start:
{
uint8_t v_suppressElabErrors_boxed_653_; uint8_t v___y_4568__boxed_654_; uint8_t v_res_655_; lean_object* v_r_656_; 
v_suppressElabErrors_boxed_653_ = lean_unbox(v_suppressElabErrors_650_);
v___y_4568__boxed_654_ = lean_unbox(v___y_651_);
v_res_655_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_653_, v___y_4568__boxed_654_, v_x_652_);
lean_dec(v_x_652_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* v_ref_658_, lean_object* v_msgData_659_, uint8_t v_severity_660_, uint8_t v_isSilent_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; uint8_t v___y_671_; lean_object* v___y_672_; uint8_t v___y_673_; lean_object* v___y_674_; lean_object* v_toCold_675_; lean_object* v___y_676_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; uint8_t v___y_708_; uint8_t v___y_709_; lean_object* v___y_710_; uint8_t v___y_711_; lean_object* v___y_712_; lean_object* v___y_732_; lean_object* v___y_733_; uint8_t v___y_734_; lean_object* v___y_735_; uint8_t v___y_736_; uint8_t v___y_737_; lean_object* v___y_738_; uint8_t v___y_742_; uint8_t v___y_743_; uint8_t v___y_744_; uint8_t v___x_755_; uint8_t v___y_757_; uint8_t v___y_758_; uint8_t v___y_759_; uint8_t v___y_761_; uint8_t v___x_769_; 
v___x_755_ = 2;
v___x_769_ = l_Lean_instBEqMessageSeverity_beq(v_severity_660_, v___x_755_);
if (v___x_769_ == 0)
{
v___y_761_ = v___x_769_;
goto v___jp_760_;
}
else
{
uint8_t v___x_770_; 
lean_inc_ref(v_msgData_659_);
v___x_770_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_659_);
v___y_761_ = v___x_770_;
goto v___jp_760_;
}
v___jp_667_:
{
lean_object* v_currNamespace_677_; lean_object* v_openDecls_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_env_683_; lean_object* v_nextMacroScope_684_; lean_object* v_ngen_685_; lean_object* v_auxDeclNGen_686_; lean_object* v_traceState_687_; lean_object* v_cache_688_; lean_object* v_recordedDeps_689_; lean_object* v_messages_690_; lean_object* v_infoState_691_; lean_object* v_snapshotTasks_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_703_; 
v_currNamespace_677_ = lean_ctor_get(v_toCold_675_, 4);
v_openDecls_678_ = lean_ctor_get(v_toCold_675_, 5);
lean_inc(v_openDecls_678_);
lean_inc(v_currNamespace_677_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v_currNamespace_677_);
lean_ctor_set(v___x_679_, 1, v_openDecls_678_);
v___x_680_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___y_669_);
lean_inc_ref(v___y_668_);
lean_inc_ref(v___y_674_);
v___x_681_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_681_, 0, v___y_674_);
lean_ctor_set(v___x_681_, 1, v___y_672_);
lean_ctor_set(v___x_681_, 2, v___y_670_);
lean_ctor_set(v___x_681_, 3, v___y_668_);
lean_ctor_set(v___x_681_, 4, v___x_680_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*5, v___y_671_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*5 + 1, v___y_673_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*5 + 2, v_isSilent_661_);
v___x_682_ = lean_st_ref_take(v___y_676_);
v_env_683_ = lean_ctor_get(v___x_682_, 0);
v_nextMacroScope_684_ = lean_ctor_get(v___x_682_, 1);
v_ngen_685_ = lean_ctor_get(v___x_682_, 2);
v_auxDeclNGen_686_ = lean_ctor_get(v___x_682_, 3);
v_traceState_687_ = lean_ctor_get(v___x_682_, 4);
v_cache_688_ = lean_ctor_get(v___x_682_, 5);
v_recordedDeps_689_ = lean_ctor_get(v___x_682_, 6);
v_messages_690_ = lean_ctor_get(v___x_682_, 7);
v_infoState_691_ = lean_ctor_get(v___x_682_, 8);
v_snapshotTasks_692_ = lean_ctor_get(v___x_682_, 9);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_703_ == 0)
{
v___x_694_ = v___x_682_;
v_isShared_695_ = v_isSharedCheck_703_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_snapshotTasks_692_);
lean_inc(v_infoState_691_);
lean_inc(v_messages_690_);
lean_inc(v_recordedDeps_689_);
lean_inc(v_cache_688_);
lean_inc(v_traceState_687_);
lean_inc(v_auxDeclNGen_686_);
lean_inc(v_ngen_685_);
lean_inc(v_nextMacroScope_684_);
lean_inc(v_env_683_);
lean_dec(v___x_682_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_703_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_696_ = lean_box(0);
v___x_697_ = l_Lean_MessageLog_add(v___x_681_, v_messages_690_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 7, v___x_697_);
v___x_699_ = v___x_694_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_env_683_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_nextMacroScope_684_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_ngen_685_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_auxDeclNGen_686_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_traceState_687_);
lean_ctor_set(v_reuseFailAlloc_702_, 5, v_cache_688_);
lean_ctor_set(v_reuseFailAlloc_702_, 6, v_recordedDeps_689_);
lean_ctor_set(v_reuseFailAlloc_702_, 7, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_702_, 8, v_infoState_691_);
lean_ctor_set(v_reuseFailAlloc_702_, 9, v_snapshotTasks_692_);
v___x_699_ = v_reuseFailAlloc_702_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_st_ref_put(v___y_676_, v___x_699_);
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_696_);
return v___x_701_;
}
}
}
v___jp_704_:
{
lean_object* v_fileName_713_; lean_object* v_fileMap_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_730_; 
v_fileName_713_ = lean_ctor_get(v___y_707_, 0);
v_fileMap_714_ = lean_ctor_get(v___y_707_, 1);
v___x_715_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_659_);
v___x_716_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_715_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_730_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_730_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_730_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_inc_ref_n(v_fileMap_714_, 2);
v___x_721_ = l_Lean_FileMap_toPosition(v_fileMap_714_, v___y_710_);
lean_dec(v___y_710_);
v___x_722_ = l_Lean_FileMap_toPosition(v_fileMap_714_, v___y_712_);
lean_dec(v___y_712_);
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
v___x_724_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_708_ == 0)
{
lean_del_object(v___x_719_);
lean_dec_ref(v___y_706_);
v___y_668_ = v___x_724_;
v___y_669_ = v_a_717_;
v___y_670_ = v___x_723_;
v___y_671_ = v___y_709_;
v___y_672_ = v___x_721_;
v___y_673_ = v___y_711_;
v___y_674_ = v_fileName_713_;
v_toCold_675_ = v___y_705_;
v___y_676_ = v___y_665_;
goto v___jp_667_;
}
else
{
uint8_t v___x_725_; 
lean_inc(v_a_717_);
v___x_725_ = l_Lean_MessageData_hasTag(v___y_706_, v_a_717_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_728_; 
lean_dec_ref_known(v___x_723_, 1);
lean_dec_ref(v___x_721_);
lean_dec(v_a_717_);
v___x_726_ = lean_box(0);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_726_);
v___x_728_ = v___x_719_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
else
{
lean_del_object(v___x_719_);
v___y_668_ = v___x_724_;
v___y_669_ = v_a_717_;
v___y_670_ = v___x_723_;
v___y_671_ = v___y_709_;
v___y_672_ = v___x_721_;
v___y_673_ = v___y_711_;
v___y_674_ = v_fileName_713_;
v_toCold_675_ = v___y_705_;
v___y_676_ = v___y_665_;
goto v___jp_667_;
}
}
}
}
v___jp_731_:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Syntax_getTailPos_x3f(v___y_735_, v___y_736_);
lean_dec(v___y_735_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_inc(v___y_738_);
v___y_705_ = v___y_732_;
v___y_706_ = v___y_733_;
v___y_707_ = v___y_732_;
v___y_708_ = v___y_734_;
v___y_709_ = v___y_736_;
v___y_710_ = v___y_738_;
v___y_711_ = v___y_737_;
v___y_712_ = v___y_738_;
goto v___jp_704_;
}
else
{
lean_object* v_val_740_; 
v_val_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v___x_739_, 1);
v___y_705_ = v___y_732_;
v___y_706_ = v___y_733_;
v___y_707_ = v___y_732_;
v___y_708_ = v___y_734_;
v___y_709_ = v___y_736_;
v___y_710_ = v___y_738_;
v___y_711_ = v___y_737_;
v___y_712_ = v_val_740_;
goto v___jp_704_;
}
}
v___jp_741_:
{
lean_object* v_toCold_745_; lean_object* v_ref_746_; uint8_t v_suppressElabErrors_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___f_750_; lean_object* v_ref_751_; lean_object* v___x_752_; 
v_toCold_745_ = lean_ctor_get(v___y_664_, 0);
v_ref_746_ = lean_ctor_get(v___y_664_, 2);
v_suppressElabErrors_747_ = lean_ctor_get_uint8(v___y_664_, sizeof(void*)*3 + 2);
v___x_748_ = lean_box(v_suppressElabErrors_747_);
v___x_749_ = lean_box(v___y_742_);
v___f_750_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_750_, 0, v___x_748_);
lean_closure_set(v___f_750_, 1, v___x_749_);
v_ref_751_ = l_Lean_replaceRef(v_ref_658_, v_ref_746_);
v___x_752_ = l_Lean_Syntax_getPos_x3f(v_ref_751_, v___y_743_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v___x_753_; 
v___x_753_ = lean_unsigned_to_nat(0u);
v___y_732_ = v_toCold_745_;
v___y_733_ = v___f_750_;
v___y_734_ = v_suppressElabErrors_747_;
v___y_735_ = v_ref_751_;
v___y_736_ = v___y_743_;
v___y_737_ = v___y_744_;
v___y_738_ = v___x_753_;
goto v___jp_731_;
}
else
{
lean_object* v_val_754_; 
v_val_754_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_val_754_);
lean_dec_ref_known(v___x_752_, 1);
v___y_732_ = v_toCold_745_;
v___y_733_ = v___f_750_;
v___y_734_ = v_suppressElabErrors_747_;
v___y_735_ = v_ref_751_;
v___y_736_ = v___y_743_;
v___y_737_ = v___y_744_;
v___y_738_ = v_val_754_;
goto v___jp_731_;
}
}
v___jp_756_:
{
if (v___y_759_ == 0)
{
v___y_742_ = v___y_757_;
v___y_743_ = v___y_758_;
v___y_744_ = v_severity_660_;
goto v___jp_741_;
}
else
{
v___y_742_ = v___y_757_;
v___y_743_ = v___y_758_;
v___y_744_ = v___x_755_;
goto v___jp_741_;
}
}
v___jp_760_:
{
if (v___y_761_ == 0)
{
uint8_t v___x_762_; uint8_t v___x_763_; 
v___x_762_ = 1;
v___x_763_ = l_Lean_instBEqMessageSeverity_beq(v_severity_660_, v___x_762_);
if (v___x_763_ == 0)
{
v___y_757_ = v___y_761_;
v___y_758_ = v___y_761_;
v___y_759_ = v___x_763_;
goto v___jp_756_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_764_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_664_);
v___x_765_ = l_Lean_warningAsError;
v___x_766_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_764_, v___x_765_);
lean_dec_ref(v___x_764_);
v___y_757_ = v___y_761_;
v___y_758_ = v___y_761_;
v___y_759_ = v___x_766_;
goto v___jp_756_;
}
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec_ref(v_msgData_659_);
v___x_767_ = lean_box(0);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_658_ = stack[0].m_obj;
lean_object* v_msgData_659_ = stack[1].m_obj;
uint8_t v_severity_660_ = stack[2].m_num;
uint8_t v_isSilent_661_ = stack[3].m_num;
lean_object* v___y_662_ = stack[4].m_obj;
lean_object* v___y_663_ = stack[5].m_obj;
lean_object* v___y_664_ = stack[6].m_obj;
lean_object* v___y_665_ = stack[7].m_obj;
lean_object* v_res_771_;
v_res_771_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_658_, v_msgData_659_, v_severity_660_, v_isSilent_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
stack->m_obj
 = v_res_771_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_772_, lean_object* v_msgData_773_, lean_object* v_severity_774_, lean_object* v_isSilent_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
uint8_t v_severity_boxed_781_; uint8_t v_isSilent_boxed_782_; lean_object* v_res_783_; 
v_severity_boxed_781_ = lean_unbox(v_severity_774_);
v_isSilent_boxed_782_ = lean_unbox(v_isSilent_775_);
v_res_783_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_772_, v_msgData_773_, v_severity_boxed_781_, v_isSilent_boxed_782_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v_ref_772_);
return v_res_783_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object* v_msgData_784_, uint8_t v_severity_785_, uint8_t v_isSilent_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_ref_792_; lean_object* v___x_793_; 
v_ref_792_ = lean_ctor_get(v___y_789_, 2);
v___x_793_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_792_, v_msgData_784_, v_severity_785_, v_isSilent_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
return v___x_793_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_784_ = stack[0].m_obj;
uint8_t v_severity_785_ = stack[1].m_num;
uint8_t v_isSilent_786_ = stack[2].m_num;
lean_object* v___y_787_ = stack[3].m_obj;
lean_object* v___y_788_ = stack[4].m_obj;
lean_object* v___y_789_ = stack[5].m_obj;
lean_object* v___y_790_ = stack[6].m_obj;
lean_object* v_res_794_;
v_res_794_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_784_, v_severity_785_, v_isSilent_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object* v_msgData_795_, lean_object* v_severity_796_, lean_object* v_isSilent_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
uint8_t v_severity_boxed_803_; uint8_t v_isSilent_boxed_804_; lean_object* v_res_805_; 
v_severity_boxed_803_ = lean_unbox(v_severity_796_);
v_isSilent_boxed_804_ = lean_unbox(v_isSilent_797_);
v_res_805_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_795_, v_severity_boxed_803_, v_isSilent_boxed_804_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_805_;
}
}
lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object* v_msgData_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
uint8_t v___x_812_; uint8_t v___x_813_; lean_object* v___x_814_; 
v___x_812_ = 1;
v___x_813_ = 0;
v___x_814_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_806_, v___x_812_, v___x_813_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
return v___x_814_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_806_ = stack[0].m_obj;
lean_object* v___y_807_ = stack[1].m_obj;
lean_object* v___y_808_ = stack[2].m_obj;
lean_object* v___y_809_ = stack[3].m_obj;
lean_object* v___y_810_ = stack[4].m_obj;
lean_object* v_res_815_;
v_res_815_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v_msgData_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
stack->m_obj
 = v_res_815_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object* v_msgData_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v_msgData_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_822_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0));
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
if (lean_obj_tag(v_a_826_) == 0)
{
lean_object* v___x_828_; 
v___x_828_ = l_List_reverse___redArg(v_a_827_);
return v___x_828_;
}
else
{
lean_object* v_head_829_; lean_object* v_tail_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_843_; 
v_head_829_ = lean_ctor_get(v_a_826_, 0);
v_tail_830_ = lean_ctor_get(v_a_826_, 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v_a_826_);
if (v_isSharedCheck_843_ == 0)
{
v___x_832_ = v_a_826_;
v_isShared_833_ = v_isSharedCheck_843_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_tail_830_);
lean_inc(v_head_829_);
lean_dec(v_a_826_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_843_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
uint8_t v_minIndexable_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v_minIndexable_834_ = 0;
v___x_835_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_836_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_829_, v_minIndexable_834_);
lean_dec(v_head_829_);
v___x_837_ = l_Lean_stringToMessageData(v___x_836_);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_835_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_a_827_);
lean_ctor_set(v___x_832_, 0, v___x_838_);
v___x_840_ = v___x_832_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_a_827_);
v___x_840_ = v_reuseFailAlloc_842_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
v_a_826_ = v_tail_830_;
v_a_827_ = v___x_840_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
if (lean_obj_tag(v_a_844_) == 0)
{
lean_object* v___x_846_; 
v___x_846_ = l_List_reverse___redArg(v_a_845_);
return v___x_846_;
}
else
{
lean_object* v_head_847_; lean_object* v_tail_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_856_; 
v_head_847_ = lean_ctor_get(v_a_844_, 0);
v_tail_848_ = lean_ctor_get(v_a_844_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v_a_844_);
if (v_isSharedCheck_856_ == 0)
{
v___x_850_ = v_a_844_;
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_tail_848_);
lean_inc(v_head_847_);
lean_dec(v_a_844_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_a_845_);
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_head_847_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_a_845_);
v___x_853_ = v_reuseFailAlloc_855_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
v_a_844_ = v_tail_848_;
v_a_845_ = v___x_853_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0));
v___x_859_ = l_Lean_stringToMessageData(v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2));
v___x_862_ = l_Lean_stringToMessageData(v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4));
v___x_865_ = l_Lean_stringToMessageData(v___x_864_);
return v___x_865_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object* v_s_866_, lean_object* v_declName_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_kinds_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v_ks_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_inc(v_declName_867_);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v_declName_867_);
v___x_899_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_866_, v___x_898_);
lean_dec_ref_known(v___x_898_, 1);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec(v_declName_867_);
v___x_900_ = lean_box(0);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
else
{
lean_object* v_head_902_; lean_object* v_tail_903_; uint8_t v_minIndexable_904_; uint8_t v_gen_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; 
v_head_902_ = lean_ctor_get(v___x_899_, 0);
v_tail_903_ = lean_ctor_get(v___x_899_, 1);
v_minIndexable_904_ = 0;
if (lean_obj_tag(v_tail_903_) == 0)
{
lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_925_; 
lean_inc(v_head_902_);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; lean_object* v_unused_927_; 
v_unused_926_ = lean_ctor_get(v___x_899_, 1);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v___x_899_, 0);
lean_dec(v_unused_927_);
v___x_917_ = v___x_899_;
v_isShared_918_ = v_isSharedCheck_925_;
goto v_resetjp_916_;
}
else
{
lean_dec(v___x_899_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_925_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_919_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_920_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_902_, v_minIndexable_904_);
lean_dec(v_head_902_);
v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 7);
lean_ctor_set(v___x_917_, 1, v___x_921_);
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_923_ = v___x_917_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
v_kinds_874_ = v___x_923_;
v___y_875_ = v_a_868_;
v___y_876_ = v_a_869_;
v___y_877_ = v_a_870_;
v___y_878_ = v_a_871_;
goto v___jp_873_;
}
}
}
else
{
lean_object* v_head_928_; 
v_head_928_ = lean_ctor_get(v_tail_903_, 0);
switch(lean_obj_tag(v_head_928_))
{
case 1:
{
lean_object* v_tail_929_; 
v_tail_929_ = lean_ctor_get(v_tail_903_, 1);
if (lean_obj_tag(v_tail_929_) == 0)
{
if (lean_obj_tag(v_head_902_) == 0)
{
uint8_t v_gen_930_; 
lean_inc_ref(v_head_902_);
lean_dec_ref_known(v___x_899_, 2);
v_gen_930_ = lean_ctor_get_uint8(v_head_902_, 0);
lean_dec_ref_known(v_head_902_, 0);
v_gen_906_ = v_gen_930_;
v___y_907_ = v_a_868_;
v___y_908_ = v_a_869_;
v___y_909_ = v_a_870_;
v___y_910_ = v_a_871_;
goto v___jp_905_;
}
else
{
v_ks_889_ = v___x_899_;
v___y_890_ = v_a_868_;
v___y_891_ = v_a_869_;
v___y_892_ = v_a_870_;
v___y_893_ = v_a_871_;
goto v___jp_888_;
}
}
else
{
v_ks_889_ = v___x_899_;
v___y_890_ = v_a_868_;
v___y_891_ = v_a_869_;
v___y_892_ = v_a_870_;
v___y_893_ = v_a_871_;
goto v___jp_888_;
}
}
case 0:
{
lean_object* v_tail_931_; 
v_tail_931_ = lean_ctor_get(v_tail_903_, 1);
if (lean_obj_tag(v_tail_931_) == 0)
{
if (lean_obj_tag(v_head_902_) == 1)
{
uint8_t v_gen_932_; 
lean_inc_ref(v_head_902_);
lean_dec_ref_known(v___x_899_, 2);
v_gen_932_ = lean_ctor_get_uint8(v_head_902_, 0);
lean_dec_ref_known(v_head_902_, 0);
v_gen_906_ = v_gen_932_;
v___y_907_ = v_a_868_;
v___y_908_ = v_a_869_;
v___y_909_ = v_a_870_;
v___y_910_ = v_a_871_;
goto v___jp_905_;
}
else
{
v_ks_889_ = v___x_899_;
v___y_890_ = v_a_868_;
v___y_891_ = v_a_869_;
v___y_892_ = v_a_870_;
v___y_893_ = v_a_871_;
goto v___jp_888_;
}
}
else
{
v_ks_889_ = v___x_899_;
v___y_890_ = v_a_868_;
v___y_891_ = v_a_869_;
v___y_892_ = v_a_870_;
v___y_893_ = v_a_871_;
goto v___jp_888_;
}
}
default: 
{
v_ks_889_ = v___x_899_;
v___y_890_ = v_a_868_;
v___y_891_ = v_a_869_;
v___y_892_ = v_a_870_;
v___y_893_ = v_a_871_;
goto v___jp_888_;
}
}
}
v___jp_905_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_911_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_912_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_912_, 0, v_gen_906_);
v___x_913_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v___x_912_, v_minIndexable_904_);
lean_dec_ref_known(v___x_912_, 0);
v___x_914_ = l_Lean_stringToMessageData(v___x_913_);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_911_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v_kinds_874_ = v___x_915_;
v___y_875_ = v___y_907_;
v___y_876_ = v___y_908_;
v___y_877_ = v___y_909_;
v___y_878_ = v___y_910_;
goto v___jp_873_;
}
}
v___jp_873_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_879_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1);
v___x_880_ = l_Lean_MessageData_ofName(v_declName_867_);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v_kinds_874_);
v___x_885_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v___x_886_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
return v___x_887_;
}
v___jp_888_:
{
lean_object* v___x_894_; lean_object* v_ks_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_894_ = lean_box(0);
v_ks_895_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(v_ks_889_, v___x_894_);
v___x_896_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(v_ks_895_, v___x_894_);
v___x_897_ = l_Lean_MessageData_ofList(v___x_896_);
v_kinds_874_ = v___x_897_;
v___y_875_ = v___y_890_;
v___y_876_ = v___y_891_;
v___y_877_ = v___y_892_;
v___y_878_ = v___y_893_;
goto v___jp_873_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_866_ = stack[0].m_obj;
lean_object* v_declName_867_ = stack[1].m_obj;
lean_object* v_a_868_ = stack[2].m_obj;
lean_object* v_a_869_ = stack[3].m_obj;
lean_object* v_a_870_ = stack[4].m_obj;
lean_object* v_a_871_ = stack[5].m_obj;
lean_object* v_res_933_;
v_res_933_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_s_866_, v_declName_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
stack->m_obj
 = v_res_933_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object* v_s_934_, lean_object* v_declName_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_s_934_, v_declName_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec_ref(v_s_934_);
return v_res_941_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_942_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_945_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_946_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
lean_ctor_set(v___x_948_, 2, v___x_947_);
lean_ctor_set(v___x_948_, 3, v___x_947_);
lean_ctor_set(v___x_948_, 4, v___x_946_);
lean_ctor_set(v___x_948_, 5, v___x_946_);
lean_ctor_set(v___x_948_, 6, v___x_946_);
lean_ctor_set(v___x_948_, 7, v___x_946_);
lean_ctor_set(v___x_948_, 8, v___x_946_);
lean_ctor_set(v___x_948_, 9, v___x_946_);
lean_ctor_set(v___x_948_, 10, v___x_946_);
lean_ctor_set(v___x_948_, 11, v___x_945_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_unsigned_to_nat(32u);
v___x_950_ = lean_mk_empty_array_with_capacity(v___x_949_);
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_952_ = ((size_t)5ULL);
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = lean_unsigned_to_nat(32u);
v___x_955_ = lean_mk_empty_array_with_capacity(v___x_954_);
v___x_956_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3);
v___x_957_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_955_);
lean_ctor_set(v___x_957_, 2, v___x_953_);
lean_ctor_set(v___x_957_, 3, v___x_953_);
lean_ctor_set_usize(v___x_957_, 4, v___x_952_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_958_ = lean_box(1);
v___x_959_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4);
v___x_960_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_959_);
lean_ctor_set(v___x_961_, 2, v___x_958_);
return v___x_961_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object* v_msgData_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; lean_object* v_toCold_967_; lean_object* v_env_968_; lean_object* v_options_969_; uint8_t v___x_970_; lean_object* v_env_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_966_ = lean_st_ref_get(v___y_964_);
v_toCold_967_ = lean_ctor_get(v___y_963_, 0);
v_env_968_ = lean_ctor_get(v___x_966_, 0);
lean_inc_ref(v_env_968_);
lean_dec(v___x_966_);
v_options_969_ = lean_ctor_get(v_toCold_967_, 2);
v___x_970_ = 0;
v_env_971_ = l_Lean_Environment_setRecordingDeps(v_env_968_, v___x_970_);
v___x_972_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_973_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_969_);
v___x_974_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_974_, 0, v_env_971_);
lean_ctor_set(v___x_974_, 1, v___x_972_);
lean_ctor_set(v___x_974_, 2, v___x_973_);
lean_ctor_set(v___x_974_, 3, v_options_969_);
v___x_975_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v_msgData_962_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_962_ = stack[0].m_obj;
lean_object* v___y_963_ = stack[1].m_obj;
lean_object* v___y_964_ = stack[2].m_obj;
lean_object* v_res_977_;
v_res_977_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msgData_962_, v___y_963_, v___y_964_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object* v_msgData_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msgData_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
return v_res_982_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object* v_msg_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_ref_987_; lean_object* v___x_988_; lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_997_; 
v_ref_987_ = lean_ctor_get(v___y_984_, 2);
v___x_988_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msg_983_, v___y_984_, v___y_985_);
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_997_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
lean_inc(v_ref_987_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v_ref_987_);
lean_ctor_set(v___x_993_, 1, v_a_989_);
if (v_isShared_992_ == 0)
{
lean_ctor_set_tag(v___x_991_, 1);
lean_ctor_set(v___x_991_, 0, v___x_993_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_983_ = stack[0].m_obj;
lean_object* v___y_984_ = stack[1].m_obj;
lean_object* v___y_985_ = stack[2].m_obj;
lean_object* v_res_998_;
v_res_998_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_983_, v___y_984_, v___y_985_);
stack->m_obj
 = v_res_998_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object* v_msg_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1003_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object* v_s_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v_env_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1021_ = lean_st_ref_get(v_a_1019_);
v_env_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc_ref(v_env_1022_);
lean_dec(v___x_1021_);
v___x_1023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
v___x_1024_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5));
lean_inc_ref(v_s_1017_);
v___x_1025_ = l_Lean_Parser_runParserCategory(v_env_1022_, v___x_1023_, v_s_1017_, v___x_1024_);
if (lean_obj_tag(v___x_1025_) == 1)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
lean_dec_ref(v_s_1017_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v___x_1027_ = l_Lean_Meta_Grind_getAttrKindCore(v_a_1026_, v_a_1018_, v_a_1019_);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_dec_ref(v___x_1025_);
v___x_1028_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7);
v___x_1029_ = l_Lean_stringToMessageData(v_s_1017_);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1030_, v_a_1018_, v_a_1019_);
return v___x_1031_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1017_ = stack[0].m_obj;
lean_object* v_a_1018_ = stack[1].m_obj;
lean_object* v_a_1019_ = stack[2].m_obj;
lean_object* v_res_1032_;
v_res_1032_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(v_s_1017_, v_a_1018_, v_a_1019_);
stack->m_obj
 = v_res_1032_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object* v_s_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(v_s_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
return v_res_1037_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object* v_00_u03b1_1038_, lean_object* v_msg_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_1039_, v___y_1040_, v___y_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1039_ = stack[1].m_obj;
lean_object* v___y_1040_ = stack[2].m_obj;
lean_object* v___y_1041_ = stack[3].m_obj;
lean_object* v_res_1044_;
v_res_1044_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_box(0), v_msg_1039_, v___y_1040_, v___y_1041_);
stack->m_obj
 = v_res_1044_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object* v_00_u03b1_1045_, lean_object* v_msg_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(v_00_u03b1_1045_, v_msg_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1050_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object* v_msg_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_ref_1057_; lean_object* v___x_1058_; lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1067_; 
v_ref_1057_ = lean_ctor_get(v___y_1054_, 2);
v___x_1058_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
lean_inc(v_ref_1057_);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v_ref_1057_);
lean_ctor_set(v___x_1063_, 1, v_a_1059_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 1);
lean_ctor_set(v___x_1061_, 0, v___x_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1051_ = stack[0].m_obj;
lean_object* v___y_1052_ = stack[1].m_obj;
lean_object* v___y_1053_ = stack[2].m_obj;
lean_object* v___y_1054_ = stack[3].m_obj;
lean_object* v___y_1055_ = stack[4].m_obj;
lean_object* v_res_1068_;
v_res_1068_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
stack->m_obj
 = v_res_1068_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object* v_msg_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1075_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0));
v___x_1078_ = l_Lean_stringToMessageData(v___x_1077_);
return v___x_1078_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t v_minIndexable_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
if (v_minIndexable_1079_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1);
v___x_1088_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1087_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
return v___x_1088_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_0interp(lean_interpreter_value* stack)
{
uint8_t v_minIndexable_1079_ = stack[0].m_num;
lean_object* v_a_1080_ = stack[1].m_obj;
lean_object* v_a_1081_ = stack[2].m_obj;
lean_object* v_a_1082_ = stack[3].m_obj;
lean_object* v_a_1083_ = stack[4].m_obj;
lean_object* v_res_1089_;
v_res_1089_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
stack->m_obj
 = v_res_1089_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object* v_minIndexable_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
uint8_t v_minIndexable_boxed_1096_; lean_object* v_res_1097_; 
v_minIndexable_boxed_1096_ = lean_unbox(v_minIndexable_1090_);
v_res_1097_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_boxed_1096_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
return v_res_1097_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object* v_00_u03b1_1098_, lean_object* v_msg_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1099_ = stack[1].m_obj;
lean_object* v___y_1100_ = stack[2].m_obj;
lean_object* v___y_1101_ = stack[3].m_obj;
lean_object* v___y_1102_ = stack[4].m_obj;
lean_object* v___y_1103_ = stack[5].m_obj;
lean_object* v_res_1106_;
v_res_1106_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_box(0), v_msg_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
stack->m_obj
 = v_res_1106_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object* v_00_u03b1_1107_, lean_object* v_msg_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(v_00_u03b1_1107_, v_msg_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
return v_res_1114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_1117_ = l_Lean_stringToMessageData(v___x_1116_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_1120_ = l_Lean_stringToMessageData(v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_1123_ = l_Lean_stringToMessageData(v___x_1122_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1126_ = l_Lean_stringToMessageData(v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1129_ = l_Lean_stringToMessageData(v___x_1128_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20));
v___x_1147_ = l_Lean_stringToMessageData(v___x_1146_);
return v___x_1147_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1148_, lean_object* v_declHint_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_env_1154_; uint8_t v___x_1155_; 
v___x_1152_ = lean_box(0);
v___x_1153_ = lean_st_ref_get(v___y_1150_);
v_env_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc_ref(v_env_1154_);
lean_dec(v___x_1153_);
v___x_1155_ = l_Lean_Name_isAnonymous(v_declHint_1149_);
if (v___x_1155_ == 0)
{
uint8_t v_isExporting_1156_; 
v_isExporting_1156_ = lean_ctor_get_uint8(v_env_1154_, sizeof(void*)*13);
if (v_isExporting_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec_ref(v_env_1154_);
lean_dec(v_declHint_1149_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v_msg_1148_);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
lean_inc_ref(v_env_1154_);
v___x_1158_ = l_Lean_Environment_setExporting(v_env_1154_, v___x_1155_);
lean_inc(v_declHint_1149_);
lean_inc_ref(v___x_1158_);
v___x_1159_ = l_Lean_Environment_contains(v___x_1158_, v_declHint_1149_, v_isExporting_1156_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_env_1154_);
lean_dec(v_declHint_1149_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_msg_1148_);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v_c_1166_; lean_object* v___x_1167_; 
v___x_1161_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_1162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
v___x_1163_ = l_Lean_Options_empty;
v___x_1164_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1158_);
lean_ctor_set(v___x_1164_, 1, v___x_1161_);
lean_ctor_set(v___x_1164_, 2, v___x_1162_);
lean_ctor_set(v___x_1164_, 3, v___x_1163_);
lean_inc(v_declHint_1149_);
v___x_1165_ = l_Lean_MessageData_ofConstName(v_declHint_1149_, v___x_1155_);
v_c_1166_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1166_, 0, v___x_1164_);
lean_ctor_set(v_c_1166_, 1, v___x_1165_);
v___x_1167_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1154_, v_declHint_1149_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec_ref(v_env_1154_);
lean_dec(v_declHint_1149_);
v___x_1168_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v_c_1166_);
v___x_1170_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = l_Lean_MessageData_note(v___x_1171_);
v___x_1173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1173_, 0, v_msg_1148_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
else
{
lean_object* v_val_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1231_; 
v_val_1175_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1177_ = v___x_1167_;
v_isShared_1178_ = v_isSharedCheck_1231_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_val_1175_);
lean_dec(v___x_1167_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1231_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v_modules_1180_; lean_object* v_moduleNames_1181_; lean_object* v_mod_1182_; uint8_t v___y_1184_; uint8_t v___x_1214_; 
v___x_1179_ = l_Lean_Environment_header(v_env_1154_);
lean_dec_ref(v_env_1154_);
v_modules_1180_ = lean_ctor_get(v___x_1179_, 3);
lean_inc_ref(v_modules_1180_);
v_moduleNames_1181_ = lean_ctor_get(v___x_1179_, 4);
lean_inc_ref(v_moduleNames_1181_);
lean_dec_ref(v___x_1179_);
v_mod_1182_ = lean_array_get(v___x_1152_, v_moduleNames_1181_, v_val_1175_);
lean_dec_ref(v_moduleNames_1181_);
v___x_1214_ = l_Lean_isPrivateName(v_declHint_1149_);
lean_dec(v_declHint_1149_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_array_get_size(v_modules_1180_);
v___x_1216_ = lean_nat_dec_lt(v_val_1175_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_dec_ref(v_modules_1180_);
lean_dec(v_val_1175_);
v___y_1184_ = v___x_1214_;
goto v___jp_1183_;
}
else
{
lean_object* v___x_1217_; lean_object* v_toImport_1218_; uint8_t v_isExported_1219_; 
v___x_1217_ = lean_array_fget(v_modules_1180_, v_val_1175_);
lean_dec(v_val_1175_);
lean_dec_ref(v_modules_1180_);
v_toImport_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_ref(v_toImport_1218_);
lean_dec(v___x_1217_);
v_isExported_1219_ = lean_ctor_get_uint8(v_toImport_1218_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1218_);
v___y_1184_ = v_isExported_1219_;
goto v___jp_1183_;
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec_ref(v_modules_1180_);
lean_del_object(v___x_1177_);
lean_dec(v_val_1175_);
v___x_1220_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v_c_1166_);
v___x_1222_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1221_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = l_Lean_MessageData_ofName(v_mod_1182_);
v___x_1225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21);
v___x_1227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = l_Lean_MessageData_note(v___x_1227_);
v___x_1229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_msg_1148_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
v___jp_1183_:
{
if (v___y_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1185_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v_c_1166_);
v___x_1187_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = l_Lean_MessageData_ofName(v_mod_1182_);
v___x_1190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Lean_MessageData_note(v___x_1192_);
v___x_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1194_, 0, v_msg_1148_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1194_);
v___x_1196_ = v___x_1177_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1198_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v_c_1166_);
v___x_1200_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = l_Lean_MessageData_ofName(v_mod_1182_);
lean_inc_ref(v___x_1202_);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1202_);
v___x_1207_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = l_Lean_MessageData_note(v___x_1208_);
v___x_1210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_msg_1148_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1210_);
v___x_1212_ = v___x_1177_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
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
lean_object* v___x_1232_; 
lean_dec_ref(v_env_1154_);
lean_dec(v_declHint_1149_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v_msg_1148_);
return v___x_1232_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1148_ = stack[0].m_obj;
lean_object* v_declHint_1149_ = stack[1].m_obj;
lean_object* v___y_1150_ = stack[2].m_obj;
lean_object* v_res_1233_;
v_res_1233_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1148_, v_declHint_1149_, v___y_1150_);
stack->m_obj
 = v_res_1233_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1234_, lean_object* v_declHint_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1234_, v_declHint_1235_, v___y_1236_);
lean_dec(v___y_1236_);
return v_res_1238_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1239_, lean_object* v_declHint_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1256_; 
v___x_1246_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1239_, v_declHint_1240_, v___y_1244_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1251_ = l_Lean_unknownIdentifierMessageTag;
v___x_1252_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v_a_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1252_);
v___x_1254_ = v___x_1249_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1239_ = stack[0].m_obj;
lean_object* v_declHint_1240_ = stack[1].m_obj;
lean_object* v___y_1241_ = stack[2].m_obj;
lean_object* v___y_1242_ = stack[3].m_obj;
lean_object* v___y_1243_ = stack[4].m_obj;
lean_object* v___y_1244_ = stack[5].m_obj;
lean_object* v_res_1257_;
v_res_1257_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1239_, v_declHint_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
stack->m_obj
 = v_res_1257_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1258_, lean_object* v_declHint_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1258_, v_declHint_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1265_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1266_, lean_object* v_msg_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_toCold_1273_; lean_object* v_currRecDepth_1274_; lean_object* v_ref_1275_; uint16_t v_optionFlags_1276_; uint8_t v_suppressElabErrors_1277_; uint8_t v_isRecordingDeps_1278_; lean_object* v_ref_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_toCold_1273_ = lean_ctor_get(v___y_1270_, 0);
v_currRecDepth_1274_ = lean_ctor_get(v___y_1270_, 1);
v_ref_1275_ = lean_ctor_get(v___y_1270_, 2);
v_optionFlags_1276_ = lean_ctor_get_uint16(v___y_1270_, sizeof(void*)*3);
v_suppressElabErrors_1277_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1278_ = lean_ctor_get_uint8(v___y_1270_, sizeof(void*)*3 + 3);
v_ref_1279_ = l_Lean_replaceRef(v_ref_1266_, v_ref_1275_);
lean_inc(v_currRecDepth_1274_);
lean_inc_ref(v_toCold_1273_);
v___x_1280_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1280_, 0, v_toCold_1273_);
lean_ctor_set(v___x_1280_, 1, v_currRecDepth_1274_);
lean_ctor_set(v___x_1280_, 2, v_ref_1279_);
lean_ctor_set_uint16(v___x_1280_, sizeof(void*)*3, v_optionFlags_1276_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*3 + 2, v_suppressElabErrors_1277_);
lean_ctor_set_uint8(v___x_1280_, sizeof(void*)*3 + 3, v_isRecordingDeps_1278_);
v___x_1281_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1267_, v___y_1268_, v___y_1269_, v___x_1280_, v___y_1271_);
lean_dec_ref_known(v___x_1280_, 3);
return v___x_1281_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1266_ = stack[0].m_obj;
lean_object* v_msg_1267_ = stack[1].m_obj;
lean_object* v___y_1268_ = stack[2].m_obj;
lean_object* v___y_1269_ = stack[3].m_obj;
lean_object* v___y_1270_ = stack[4].m_obj;
lean_object* v___y_1271_ = stack[5].m_obj;
lean_object* v_res_1282_;
v_res_1282_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1266_, v_msg_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
stack->m_obj
 = v_res_1282_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1283_, lean_object* v_msg_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1283_, v_msg_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v_ref_1283_);
return v_res_1290_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1291_, lean_object* v_msg_1292_, lean_object* v_declHint_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; lean_object* v_a_1300_; lean_object* v___x_1301_; 
v___x_1299_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1292_, v_declHint_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref(v___x_1299_);
v___x_1301_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1291_, v_a_1300_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v___x_1301_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1291_ = stack[0].m_obj;
lean_object* v_msg_1292_ = stack[1].m_obj;
lean_object* v_declHint_1293_ = stack[2].m_obj;
lean_object* v___y_1294_ = stack[3].m_obj;
lean_object* v___y_1295_ = stack[4].m_obj;
lean_object* v___y_1296_ = stack[5].m_obj;
lean_object* v___y_1297_ = stack[6].m_obj;
lean_object* v_res_1302_;
v_res_1302_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1291_, v_msg_1292_, v_declHint_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
stack->m_obj
 = v_res_1302_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1303_, lean_object* v_msg_1304_, lean_object* v_declHint_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1303_, v_msg_1304_, v_declHint_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v_ref_1303_);
return v_res_1311_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1314_ = l_Lean_stringToMessageData(v___x_1313_);
return v___x_1314_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1315_, lean_object* v_constName_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1322_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1323_ = 0;
lean_inc(v_constName_1316_);
v___x_1324_ = l_Lean_MessageData_ofConstName(v_constName_1316_, v___x_1323_);
v___x_1325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1322_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1325_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1315_, v___x_1327_, v_constName_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1328_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1315_ = stack[0].m_obj;
lean_object* v_constName_1316_ = stack[1].m_obj;
lean_object* v___y_1317_ = stack[2].m_obj;
lean_object* v___y_1318_ = stack[3].m_obj;
lean_object* v___y_1319_ = stack[4].m_obj;
lean_object* v___y_1320_ = stack[5].m_obj;
lean_object* v_res_1329_;
v_res_1329_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1315_, v_constName_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
stack->m_obj
 = v_res_1329_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1330_, lean_object* v_constName_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1330_, v_constName_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v_ref_1330_);
return v_res_1337_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_constName_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_ref_1344_; lean_object* v___x_1345_; 
v_ref_1344_ = lean_ctor_get(v___y_1341_, 2);
v___x_1345_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1344_, v_constName_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
return v___x_1345_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1338_ = stack[0].m_obj;
lean_object* v___y_1339_ = stack[1].m_obj;
lean_object* v___y_1340_ = stack[2].m_obj;
lean_object* v___y_1341_ = stack[3].m_obj;
lean_object* v___y_1342_ = stack[4].m_obj;
lean_object* v_res_1346_;
v_res_1346_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
stack->m_obj
 = v_res_1346_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1353_;
}
}
lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* v_constName_1354_, uint8_t v_skipRealize_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v_env_1362_; lean_object* v___x_1363_; 
v___x_1361_ = lean_st_ref_get(v___y_1359_);
v_env_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc_ref(v_env_1362_);
lean_dec(v___x_1361_);
lean_inc(v_constName_1354_);
v___x_1363_ = l_Lean_Environment_findAsync_x3f(v_env_1362_, v_constName_1354_, v_skipRealize_1355_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1354_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
return v___x_1364_;
}
else
{
lean_object* v_val_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v_constName_1354_);
v_val_1365_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1363_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_val_1365_);
lean_dec(v___x_1363_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set_tag(v___x_1367_, 0);
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_val_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1354_ = stack[0].m_obj;
uint8_t v_skipRealize_1355_ = stack[1].m_num;
lean_object* v___y_1356_ = stack[2].m_obj;
lean_object* v___y_1357_ = stack[3].m_obj;
lean_object* v___y_1358_ = stack[4].m_obj;
lean_object* v___y_1359_ = stack[5].m_obj;
lean_object* v_res_1373_;
v_res_1373_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1354_, v_skipRealize_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
stack->m_obj
 = v_res_1373_;
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* v_constName_1374_, lean_object* v_skipRealize_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v_skipRealize_boxed_1381_; lean_object* v_res_1382_; 
v_skipRealize_boxed_1381_ = lean_unbox(v_skipRealize_1375_);
v_res_1382_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1374_, v_skipRealize_boxed_1381_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1382_;
}
}
lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* v_declName_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v___x_1386_; lean_object* v_env_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1386_ = lean_st_ref_get(v___y_1384_);
v_env_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc_ref(v_env_1387_);
lean_dec(v___x_1386_);
v___x_1388_ = l_Lean_getReducibilityStatusCore(v_env_1387_, v_declName_1383_);
v___x_1389_ = lean_box(v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT void l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1383_ = stack[0].m_obj;
lean_object* v___y_1384_ = stack[1].m_obj;
lean_object* v_res_1391_;
v_res_1391_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1383_, v___y_1384_);
stack->m_obj
 = v_res_1391_;
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_declName_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1392_, v___y_1393_);
lean_dec(v___y_1393_);
return v_res_1395_;
}
}
lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* v_declName_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1418_; 
v___x_1402_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1396_, v___y_1400_);
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1418_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1418_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_unbox(v_a_1403_);
lean_dec(v_a_1403_);
if (v___x_1407_ == 0)
{
uint8_t v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1408_ = 1;
v___x_1409_ = lean_box(v___x_1408_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1409_);
v___x_1411_ = v___x_1405_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
else
{
uint8_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1413_ = 0;
v___x_1414_ = lean_box(v___x_1413_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1414_);
v___x_1416_ = v___x_1405_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1396_ = stack[0].m_obj;
lean_object* v___y_1397_ = stack[1].m_obj;
lean_object* v___y_1398_ = stack[2].m_obj;
lean_object* v___y_1399_ = stack[3].m_obj;
lean_object* v___y_1400_ = stack[4].m_obj;
lean_object* v_res_1419_;
v_res_1419_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
stack->m_obj
 = v_res_1419_;
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* v_declName_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1426_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
v___x_1429_ = l_Lean_stringToMessageData(v___x_1428_);
return v___x_1429_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
v___x_1432_ = l_Lean_stringToMessageData(v___x_1431_);
return v___x_1432_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
v___x_1435_ = l_Lean_stringToMessageData(v___x_1434_);
return v___x_1435_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
v___x_1438_ = l_Lean_stringToMessageData(v___x_1437_);
return v___x_1438_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
v___x_1441_ = l_Lean_stringToMessageData(v___x_1440_);
return v___x_1441_;
}
}
lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* v_params_1442_, lean_object* v_id_1443_, lean_object* v_declName_1444_, lean_object* v_kind_1445_, uint8_t v_minIndexable_1446_, uint8_t v_suggest_1447_, uint8_t v_warn_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___y_1455_; lean_object* v_thm_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; uint8_t v___x_1510_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___x_1707_; 
v___x_1510_ = 0;
lean_inc(v_declName_1444_);
v___x_1707_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1444_, v___x_1510_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; uint8_t v_kind_1709_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v_kind_1709_ = lean_ctor_get_uint8(v_a_1708_, sizeof(void*)*3);
lean_dec(v_a_1708_);
switch(v_kind_1709_)
{
case 1:
{
v___y_1638_ = v_a_1449_;
v___y_1639_ = v_a_1450_;
v___y_1640_ = v_a_1451_;
v___y_1641_ = v_a_1452_;
goto v___jp_1637_;
}
case 2:
{
v___y_1638_ = v_a_1449_;
v___y_1639_ = v_a_1450_;
v___y_1640_ = v_a_1451_;
v___y_1641_ = v_a_1452_;
goto v___jp_1637_;
}
case 6:
{
v___y_1638_ = v_a_1449_;
v___y_1639_ = v_a_1450_;
v___y_1640_ = v_a_1451_;
v___y_1641_ = v_a_1452_;
goto v___jp_1637_;
}
case 0:
{
lean_object* v___x_1710_; 
lean_dec(v_id_1443_);
lean_inc(v_declName_1444_);
v___x_1710_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1444_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; uint8_t v___x_1712_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = lean_unbox(v_a_1711_);
lean_dec(v_a_1711_);
if (v___x_1712_ == 0)
{
v___y_1568_ = v_a_1449_;
v___y_1569_ = v_a_1450_;
v___y_1570_ = v_a_1451_;
v___y_1571_ = v_a_1452_;
goto v___jp_1567_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_kind_1445_);
lean_dec_ref(v_params_1442_);
v___x_1713_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1714_ = l_Lean_MessageData_ofConstName(v_declName_1444_, v___x_1510_);
v___x_1715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1717_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_kind_1445_);
lean_dec(v_declName_1444_);
lean_dec_ref(v_params_1442_);
v_a_1727_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1710_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1710_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
default: 
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec(v_kind_1445_);
lean_dec(v_id_1443_);
lean_dec_ref(v_params_1442_);
v___x_1735_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1736_ = l_Lean_MessageData_ofConstName(v_declName_1444_, v___x_1510_);
v___x_1737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1735_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1737_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1739_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
return v___x_1740_;
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_kind_1445_);
lean_dec(v_declName_1444_);
lean_dec(v_id_1443_);
lean_dec_ref(v_params_1442_);
v_a_1741_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1707_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1707_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
v___jp_1454_:
{
lean_object* v_config_1456_; lean_object* v_extensions_1457_; lean_object* v_extra_1458_; lean_object* v_extraInj_1459_; lean_object* v_extraFacts_1460_; lean_object* v_symPrios_1461_; lean_object* v_norm_1462_; lean_object* v_normProcs_1463_; lean_object* v_anchorRefs_x3f_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1473_; 
v_config_1456_ = lean_ctor_get(v_params_1442_, 0);
v_extensions_1457_ = lean_ctor_get(v_params_1442_, 1);
v_extra_1458_ = lean_ctor_get(v_params_1442_, 2);
v_extraInj_1459_ = lean_ctor_get(v_params_1442_, 3);
v_extraFacts_1460_ = lean_ctor_get(v_params_1442_, 4);
v_symPrios_1461_ = lean_ctor_get(v_params_1442_, 5);
v_norm_1462_ = lean_ctor_get(v_params_1442_, 6);
v_normProcs_1463_ = lean_ctor_get(v_params_1442_, 7);
v_anchorRefs_x3f_1464_ = lean_ctor_get(v_params_1442_, 8);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_params_1442_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1466_ = v_params_1442_;
v_isShared_1467_ = v_isSharedCheck_1473_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_anchorRefs_x3f_1464_);
lean_inc(v_normProcs_1463_);
lean_inc(v_norm_1462_);
lean_inc(v_symPrios_1461_);
lean_inc(v_extraFacts_1460_);
lean_inc(v_extraInj_1459_);
lean_inc(v_extra_1458_);
lean_inc(v_extensions_1457_);
lean_inc(v_config_1456_);
lean_dec(v_params_1442_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1473_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1468_ = l_Lean_PersistentArray_push___redArg(v_extra_1458_, v___y_1455_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 2, v___x_1468_);
v___x_1470_ = v___x_1466_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_config_1456_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_extensions_1457_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v_extraInj_1459_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v_extraFacts_1460_);
lean_ctor_set(v_reuseFailAlloc_1472_, 5, v_symPrios_1461_);
lean_ctor_set(v_reuseFailAlloc_1472_, 6, v_norm_1462_);
lean_ctor_set(v_reuseFailAlloc_1472_, 7, v_normProcs_1463_);
lean_ctor_set(v_reuseFailAlloc_1472_, 8, v_anchorRefs_x3f_1464_);
v___x_1470_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
}
v___jp_1474_:
{
if (v_warn_1448_ == 0)
{
lean_dec(v_declName_1444_);
v___y_1455_ = v_thm_1475_;
goto v___jp_1454_;
}
else
{
lean_object* v_extensions_1480_; lean_object* v_patterns_1481_; lean_object* v_origin_1482_; lean_object* v_cnstrs_1483_; uint8_t v___x_1484_; 
v_extensions_1480_ = lean_ctor_get(v_params_1442_, 1);
v_patterns_1481_ = lean_ctor_get(v_thm_1475_, 3);
v_origin_1482_ = lean_ctor_get(v_thm_1475_, 5);
v_cnstrs_1483_ = lean_ctor_get(v_thm_1475_, 7);
v___x_1484_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1480_, v_origin_1482_, v_patterns_1481_, v_cnstrs_1483_);
if (v___x_1484_ == 0)
{
lean_dec(v_declName_1444_);
v___y_1455_ = v_thm_1475_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1485_; 
v___x_1485_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1480_, v_declName_1444_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_dec_ref_known(v___x_1485_, 1);
v___y_1455_ = v_thm_1475_;
goto v___jp_1454_;
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v_thm_1475_);
lean_dec_ref(v_params_1442_);
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
}
v___jp_1494_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1506_ = l_Lean_PersistentArray_push___redArg(v___y_1504_, v___y_1501_);
v___x_1507_ = l_Lean_PersistentArray_push___redArg(v___x_1506_, v___y_1499_);
v___x_1508_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1508_, 0, v___y_1495_);
lean_ctor_set(v___x_1508_, 1, v___y_1503_);
lean_ctor_set(v___x_1508_, 2, v___x_1507_);
lean_ctor_set(v___x_1508_, 3, v___y_1500_);
lean_ctor_set(v___x_1508_, 4, v___y_1497_);
lean_ctor_set(v___x_1508_, 5, v___y_1498_);
lean_ctor_set(v___x_1508_, 6, v___y_1505_);
lean_ctor_set(v___x_1508_, 7, v___y_1496_);
lean_ctor_set(v___x_1508_, 8, v___y_1502_);
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
return v___x_1509_;
}
v___jp_1511_:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1446_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v___x_1517_; 
lean_dec_ref_known(v___x_1516_, 1);
lean_inc(v_declName_1444_);
v___x_1517_ = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(v_declName_1444_, v___x_1510_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1550_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1550_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1550_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
if (lean_obj_tag(v_a_1518_) == 1)
{
lean_object* v_val_1522_; lean_object* v_config_1523_; lean_object* v_extensions_1524_; lean_object* v_extra_1525_; lean_object* v_extraInj_1526_; lean_object* v_extraFacts_1527_; lean_object* v_symPrios_1528_; lean_object* v_norm_1529_; lean_object* v_normProcs_1530_; lean_object* v_anchorRefs_x3f_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1543_; 
lean_dec(v_declName_1444_);
v_val_1522_ = lean_ctor_get(v_a_1518_, 0);
lean_inc(v_val_1522_);
lean_dec_ref_known(v_a_1518_, 1);
v_config_1523_ = lean_ctor_get(v_params_1442_, 0);
v_extensions_1524_ = lean_ctor_get(v_params_1442_, 1);
v_extra_1525_ = lean_ctor_get(v_params_1442_, 2);
v_extraInj_1526_ = lean_ctor_get(v_params_1442_, 3);
v_extraFacts_1527_ = lean_ctor_get(v_params_1442_, 4);
v_symPrios_1528_ = lean_ctor_get(v_params_1442_, 5);
v_norm_1529_ = lean_ctor_get(v_params_1442_, 6);
v_normProcs_1530_ = lean_ctor_get(v_params_1442_, 7);
v_anchorRefs_x3f_1531_ = lean_ctor_get(v_params_1442_, 8);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_params_1442_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1533_ = v_params_1442_;
v_isShared_1534_ = v_isSharedCheck_1543_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_anchorRefs_x3f_1531_);
lean_inc(v_normProcs_1530_);
lean_inc(v_norm_1529_);
lean_inc(v_symPrios_1528_);
lean_inc(v_extraFacts_1527_);
lean_inc(v_extraInj_1526_);
lean_inc(v_extra_1525_);
lean_inc(v_extensions_1524_);
lean_inc(v_config_1523_);
lean_dec(v_params_1442_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1543_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1535_ = l_Lean_Array_toPArray_x27___redArg(v_val_1522_);
lean_dec(v_val_1522_);
v___x_1536_ = l_Lean_PersistentArray_append___redArg(v_extra_1525_, v___x_1535_);
lean_dec_ref(v___x_1535_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 2, v___x_1536_);
v___x_1538_ = v___x_1533_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_config_1523_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_extensions_1524_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_extraInj_1526_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_extraFacts_1527_);
lean_ctor_set(v_reuseFailAlloc_1542_, 5, v_symPrios_1528_);
lean_ctor_set(v_reuseFailAlloc_1542_, 6, v_norm_1529_);
lean_ctor_set(v_reuseFailAlloc_1542_, 7, v_normProcs_1530_);
lean_ctor_set(v_reuseFailAlloc_1542_, 8, v_anchorRefs_x3f_1531_);
v___x_1538_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1540_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1538_);
v___x_1540_ = v___x_1520_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_del_object(v___x_1520_);
lean_dec(v_a_1518_);
lean_dec_ref(v_params_1442_);
v___x_1544_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__1, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
v___x_1545_ = l_Lean_MessageData_ofConstName(v_declName_1444_, v___x_1510_);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1548_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1549_;
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec(v_declName_1444_);
lean_dec_ref(v_params_1442_);
v_a_1551_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1517_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1517_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_declName_1444_);
lean_dec_ref(v_params_1442_);
v_a_1559_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1516_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1516_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
v___jp_1567_:
{
uint8_t v___x_1572_; 
v___x_1572_ = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(v_kind_1445_);
if (v___x_1572_ == 0)
{
uint8_t v___x_1573_; 
v___x_1573_ = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(v_kind_1445_);
lean_dec(v_kind_1445_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v_params_1442_);
v___x_1574_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1575_ = l_Lean_MessageData_ofConstName(v_declName_1444_, v___x_1510_);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__5, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
v___x_1578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1578_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
else
{
v___y_1512_ = v___y_1568_;
v___y_1513_ = v___y_1569_;
v___y_1514_ = v___y_1570_;
v___y_1515_ = v___y_1571_;
goto v___jp_1511_;
}
}
else
{
lean_dec(v_kind_1445_);
v___y_1512_ = v___y_1568_;
v___y_1513_ = v___y_1569_;
v___y_1514_ = v___y_1570_;
v___y_1515_ = v___y_1571_;
goto v___jp_1511_;
}
}
v___jp_1588_:
{
lean_object* v_symPrios_1593_; lean_object* v___x_1594_; 
v_symPrios_1593_ = lean_ctor_get(v_params_1442_, 5);
lean_inc_ref(v_symPrios_1593_);
lean_inc(v_declName_1444_);
v___x_1594_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1444_, v_kind_1445_, v_symPrios_1593_, v___x_1510_, v_minIndexable_1446_, v___y_1591_, v___y_1592_, v___y_1590_, v___y_1589_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v_thm_1475_ = v_a_1595_;
v___y_1476_ = v___y_1591_;
v___y_1477_ = v___y_1592_;
v___y_1478_ = v___y_1590_;
v___y_1479_ = v___y_1589_;
goto v___jp_1474_;
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_declName_1444_);
lean_dec_ref(v_params_1442_);
v_a_1596_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1594_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1594_);
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
v___jp_1604_:
{
if (v_suggest_1447_ == 0)
{
lean_dec(v_id_1443_);
v___y_1589_ = v___y_1608_;
v___y_1590_ = v___y_1607_;
v___y_1591_ = v___y_1605_;
v___y_1592_ = v___y_1606_;
goto v___jp_1588_;
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1609_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1607_);
v___x_1610_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1611_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_1609_, v___x_1610_);
lean_dec_ref(v___x_1609_);
if (v___x_1611_ == 0)
{
lean_object* v_symPrios_1612_; lean_object* v___x_1613_; 
lean_dec(v_kind_1445_);
v_symPrios_1612_ = lean_ctor_get(v_params_1442_, 5);
lean_inc_ref(v_symPrios_1612_);
lean_inc(v_declName_1444_);
v___x_1613_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1443_, v_declName_1444_, v_symPrios_1612_, v_minIndexable_1446_, v_suggest_1447_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v_thm_1475_ = v_a_1614_;
v___y_1476_ = v___y_1605_;
v___y_1477_ = v___y_1606_;
v___y_1478_ = v___y_1607_;
v___y_1479_ = v___y_1608_;
goto v___jp_1474_;
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v_declName_1444_);
lean_dec_ref(v_params_1442_);
v_a_1615_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1613_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1613_);
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
else
{
lean_dec(v_id_1443_);
v___y_1589_ = v___y_1608_;
v___y_1590_ = v___y_1607_;
v___y_1591_ = v___y_1605_;
v___y_1592_ = v___y_1606_;
goto v___jp_1588_;
}
}
}
v___jp_1623_:
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1446_, v___y_1625_, v___y_1627_, v___y_1626_, v___y_1624_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_dec_ref_known(v___x_1628_, 1);
v___y_1605_ = v___y_1625_;
v___y_1606_ = v___y_1627_;
v___y_1607_ = v___y_1626_;
v___y_1608_ = v___y_1624_;
goto v___jp_1604_;
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_kind_1445_);
lean_dec(v_declName_1444_);
lean_dec(v_id_1443_);
lean_dec_ref(v_params_1442_);
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
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
v___jp_1637_:
{
if (lean_obj_tag(v_kind_1445_) == 2)
{
uint8_t v_gen_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_id_1443_);
v_gen_1642_ = lean_ctor_get_uint8(v_kind_1445_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_kind_1445_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1644_ = v_kind_1445_;
v_isShared_1645_ = v_isSharedCheck_1706_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v_kind_1445_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1706_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; 
v___x_1646_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1446_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_config_1647_; lean_object* v_extensions_1648_; lean_object* v_extra_1649_; lean_object* v_extraInj_1650_; lean_object* v_extraFacts_1651_; lean_object* v_symPrios_1652_; lean_object* v_norm_1653_; lean_object* v_normProcs_1654_; lean_object* v_anchorRefs_x3f_1655_; lean_object* v___x_1657_; 
lean_dec_ref_known(v___x_1646_, 1);
v_config_1647_ = lean_ctor_get(v_params_1442_, 0);
lean_inc_ref(v_config_1647_);
v_extensions_1648_ = lean_ctor_get(v_params_1442_, 1);
lean_inc_ref(v_extensions_1648_);
v_extra_1649_ = lean_ctor_get(v_params_1442_, 2);
lean_inc_ref(v_extra_1649_);
v_extraInj_1650_ = lean_ctor_get(v_params_1442_, 3);
lean_inc_ref(v_extraInj_1650_);
v_extraFacts_1651_ = lean_ctor_get(v_params_1442_, 4);
lean_inc_ref(v_extraFacts_1651_);
v_symPrios_1652_ = lean_ctor_get(v_params_1442_, 5);
lean_inc_ref(v_symPrios_1652_);
v_norm_1653_ = lean_ctor_get(v_params_1442_, 6);
lean_inc_ref(v_norm_1653_);
v_normProcs_1654_ = lean_ctor_get(v_params_1442_, 7);
lean_inc_ref(v_normProcs_1654_);
v_anchorRefs_x3f_1655_ = lean_ctor_get(v_params_1442_, 8);
lean_inc(v_anchorRefs_x3f_1655_);
lean_dec_ref(v_params_1442_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set_tag(v___x_1644_, 0);
v___x_1657_ = v___x_1644_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_1697_, 0, v_gen_1642_);
v___x_1657_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; 
lean_inc_ref(v_symPrios_1652_);
lean_inc(v_declName_1444_);
v___x_1658_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1444_, v___x_1657_, v_symPrios_1652_, v___x_1510_, v___x_1510_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v___x_1660_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1660_, 0, v_gen_1642_);
lean_inc_ref(v_symPrios_1652_);
lean_inc(v_declName_1444_);
v___x_1661_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1444_, v___x_1660_, v_symPrios_1652_, v___x_1510_, v___x_1510_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1661_) == 0)
{
if (v_warn_1448_ == 0)
{
lean_object* v_a_1662_; 
lean_dec(v_declName_1444_);
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___y_1495_ = v_config_1647_;
v___y_1496_ = v_normProcs_1654_;
v___y_1497_ = v_extraFacts_1651_;
v___y_1498_ = v_symPrios_1652_;
v___y_1499_ = v_a_1662_;
v___y_1500_ = v_extraInj_1650_;
v___y_1501_ = v_a_1659_;
v___y_1502_ = v_anchorRefs_x3f_1655_;
v___y_1503_ = v_extensions_1648_;
v___y_1504_ = v_extra_1649_;
v___y_1505_ = v_norm_1653_;
goto v___jp_1494_;
}
else
{
lean_object* v_a_1663_; lean_object* v_patterns_1664_; lean_object* v_origin_1665_; lean_object* v_cnstrs_1666_; uint8_t v___x_1667_; 
v_a_1663_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1661_, 1);
v_patterns_1664_ = lean_ctor_get(v_a_1659_, 3);
v_origin_1665_ = lean_ctor_get(v_a_1659_, 5);
v_cnstrs_1666_ = lean_ctor_get(v_a_1659_, 7);
v___x_1667_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1648_, v_origin_1665_, v_patterns_1664_, v_cnstrs_1666_);
if (v___x_1667_ == 0)
{
lean_dec(v_declName_1444_);
v___y_1495_ = v_config_1647_;
v___y_1496_ = v_normProcs_1654_;
v___y_1497_ = v_extraFacts_1651_;
v___y_1498_ = v_symPrios_1652_;
v___y_1499_ = v_a_1663_;
v___y_1500_ = v_extraInj_1650_;
v___y_1501_ = v_a_1659_;
v___y_1502_ = v_anchorRefs_x3f_1655_;
v___y_1503_ = v_extensions_1648_;
v___y_1504_ = v_extra_1649_;
v___y_1505_ = v_norm_1653_;
goto v___jp_1494_;
}
else
{
lean_object* v_patterns_1668_; lean_object* v_origin_1669_; lean_object* v_cnstrs_1670_; uint8_t v___x_1671_; 
v_patterns_1668_ = lean_ctor_get(v_a_1663_, 3);
v_origin_1669_ = lean_ctor_get(v_a_1663_, 5);
v_cnstrs_1670_ = lean_ctor_get(v_a_1663_, 7);
v___x_1671_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1648_, v_origin_1669_, v_patterns_1668_, v_cnstrs_1670_);
if (v___x_1671_ == 0)
{
lean_dec(v_declName_1444_);
v___y_1495_ = v_config_1647_;
v___y_1496_ = v_normProcs_1654_;
v___y_1497_ = v_extraFacts_1651_;
v___y_1498_ = v_symPrios_1652_;
v___y_1499_ = v_a_1663_;
v___y_1500_ = v_extraInj_1650_;
v___y_1501_ = v_a_1659_;
v___y_1502_ = v_anchorRefs_x3f_1655_;
v___y_1503_ = v_extensions_1648_;
v___y_1504_ = v_extra_1649_;
v___y_1505_ = v_norm_1653_;
goto v___jp_1494_;
}
else
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1648_, v_declName_1444_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_dec_ref_known(v___x_1672_, 1);
v___y_1495_ = v_config_1647_;
v___y_1496_ = v_normProcs_1654_;
v___y_1497_ = v_extraFacts_1651_;
v___y_1498_ = v_symPrios_1652_;
v___y_1499_ = v_a_1663_;
v___y_1500_ = v_extraInj_1650_;
v___y_1501_ = v_a_1659_;
v___y_1502_ = v_anchorRefs_x3f_1655_;
v___y_1503_ = v_extensions_1648_;
v___y_1504_ = v_extra_1649_;
v___y_1505_ = v_norm_1653_;
goto v___jp_1494_;
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v_a_1663_);
lean_dec(v_a_1659_);
lean_dec(v_anchorRefs_x3f_1655_);
lean_dec_ref(v_normProcs_1654_);
lean_dec_ref(v_norm_1653_);
lean_dec_ref(v_symPrios_1652_);
lean_dec_ref(v_extraFacts_1651_);
lean_dec_ref(v_extraInj_1650_);
lean_dec_ref(v_extra_1649_);
lean_dec_ref(v_extensions_1648_);
lean_dec_ref(v_config_1647_);
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_a_1659_);
lean_dec(v_anchorRefs_x3f_1655_);
lean_dec_ref(v_normProcs_1654_);
lean_dec_ref(v_norm_1653_);
lean_dec_ref(v_symPrios_1652_);
lean_dec_ref(v_extraFacts_1651_);
lean_dec_ref(v_extraInj_1650_);
lean_dec_ref(v_extra_1649_);
lean_dec_ref(v_extensions_1648_);
lean_dec_ref(v_config_1647_);
lean_dec(v_declName_1444_);
v_a_1681_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1661_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1661_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_anchorRefs_x3f_1655_);
lean_dec_ref(v_normProcs_1654_);
lean_dec_ref(v_norm_1653_);
lean_dec_ref(v_symPrios_1652_);
lean_dec_ref(v_extraFacts_1651_);
lean_dec_ref(v_extraInj_1650_);
lean_dec_ref(v_extra_1649_);
lean_dec_ref(v_extensions_1648_);
lean_dec_ref(v_config_1647_);
lean_dec(v_declName_1444_);
v_a_1689_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1658_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1658_);
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
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_del_object(v___x_1644_);
lean_dec(v_declName_1444_);
lean_dec_ref(v_params_1442_);
v_a_1698_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1646_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1646_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
else
{
switch(lean_obj_tag(v_kind_1445_))
{
case 0:
{
v___y_1624_ = v___y_1641_;
v___y_1625_ = v___y_1638_;
v___y_1626_ = v___y_1640_;
v___y_1627_ = v___y_1639_;
goto v___jp_1623_;
}
case 1:
{
v___y_1624_ = v___y_1641_;
v___y_1625_ = v___y_1638_;
v___y_1626_ = v___y_1640_;
v___y_1627_ = v___y_1639_;
goto v___jp_1623_;
}
default: 
{
v___y_1605_ = v___y_1638_;
v___y_1606_ = v___y_1639_;
v___y_1607_ = v___y_1640_;
v___y_1608_ = v___y_1641_;
goto v___jp_1604_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_addEMatchTheorem_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_1442_ = stack[0].m_obj;
lean_object* v_id_1443_ = stack[1].m_obj;
lean_object* v_declName_1444_ = stack[2].m_obj;
lean_object* v_kind_1445_ = stack[3].m_obj;
uint8_t v_minIndexable_1446_ = stack[4].m_num;
uint8_t v_suggest_1447_ = stack[5].m_num;
uint8_t v_warn_1448_ = stack[6].m_num;
lean_object* v_a_1449_ = stack[7].m_obj;
lean_object* v_a_1450_ = stack[8].m_obj;
lean_object* v_a_1451_ = stack[9].m_obj;
lean_object* v_a_1452_ = stack[10].m_obj;
lean_object* v_res_1749_;
v_res_1749_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_1442_, v_id_1443_, v_declName_1444_, v_kind_1445_, v_minIndexable_1446_, v_suggest_1447_, v_warn_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
stack->m_obj
 = v_res_1749_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object* v_params_1750_, lean_object* v_id_1751_, lean_object* v_declName_1752_, lean_object* v_kind_1753_, lean_object* v_minIndexable_1754_, lean_object* v_suggest_1755_, lean_object* v_warn_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
uint8_t v_minIndexable_boxed_1762_; uint8_t v_suggest_boxed_1763_; uint8_t v_warn_boxed_1764_; lean_object* v_res_1765_; 
v_minIndexable_boxed_1762_ = lean_unbox(v_minIndexable_1754_);
v_suggest_boxed_1763_ = lean_unbox(v_suggest_1755_);
v_warn_boxed_1764_ = lean_unbox(v_warn_1756_);
v_res_1765_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_1750_, v_id_1751_, v_declName_1752_, v_kind_1753_, v_minIndexable_boxed_1762_, v_suggest_boxed_1763_, v_warn_boxed_1764_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
lean_dec(v_a_1760_);
lean_dec_ref(v_a_1759_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
return v_res_1765_;
}
}
lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object* v_declName_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1766_, v___y_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT void l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1766_ = stack[0].m_obj;
lean_object* v___y_1767_ = stack[1].m_obj;
lean_object* v___y_1768_ = stack[2].m_obj;
lean_object* v___y_1769_ = stack[3].m_obj;
lean_object* v___y_1770_ = stack[4].m_obj;
lean_object* v_res_1773_;
v_res_1773_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(v_declName_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
stack->m_obj
 = v_res_1773_;
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object* v_declName_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(v_declName_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
return v_res_1780_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_1781_, lean_object* v_constName_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
return v___x_1788_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1782_ = stack[1].m_obj;
lean_object* v___y_1783_ = stack[2].m_obj;
lean_object* v___y_1784_ = stack[3].m_obj;
lean_object* v___y_1785_ = stack[4].m_obj;
lean_object* v___y_1786_ = stack[5].m_obj;
lean_object* v_res_1789_;
v_res_1789_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_box(0), v_constName_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
stack->m_obj
 = v_res_1789_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1790_, lean_object* v_constName_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(v_00_u03b1_1790_, v_constName_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
return v_res_1797_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1798_, lean_object* v_ref_1799_, lean_object* v_constName_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1799_, v_constName_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1799_ = stack[1].m_obj;
lean_object* v_constName_1800_ = stack[2].m_obj;
lean_object* v___y_1801_ = stack[3].m_obj;
lean_object* v___y_1802_ = stack[4].m_obj;
lean_object* v___y_1803_ = stack[5].m_obj;
lean_object* v___y_1804_ = stack[6].m_obj;
lean_object* v_res_1807_;
v_res_1807_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_box(0), v_ref_1799_, v_constName_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
stack->m_obj
 = v_res_1807_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1808_, lean_object* v_ref_1809_, lean_object* v_constName_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(v_00_u03b1_1808_, v_ref_1809_, v_constName_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v_ref_1809_);
return v_res_1816_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1817_, lean_object* v_ref_1818_, lean_object* v_msg_1819_, lean_object* v_declHint_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1818_, v_msg_1819_, v_declHint_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
return v___x_1826_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1818_ = stack[1].m_obj;
lean_object* v_msg_1819_ = stack[2].m_obj;
lean_object* v_declHint_1820_ = stack[3].m_obj;
lean_object* v___y_1821_ = stack[4].m_obj;
lean_object* v___y_1822_ = stack[5].m_obj;
lean_object* v___y_1823_ = stack[6].m_obj;
lean_object* v___y_1824_ = stack[7].m_obj;
lean_object* v_res_1827_;
v_res_1827_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_box(0), v_ref_1818_, v_msg_1819_, v_declHint_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
stack->m_obj
 = v_res_1827_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1828_, lean_object* v_ref_1829_, lean_object* v_msg_1830_, lean_object* v_declHint_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1828_, v_ref_1829_, v_msg_1830_, v_declHint_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v_ref_1829_);
return v_res_1837_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1838_, lean_object* v_declHint_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1838_, v_declHint_1839_, v___y_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1838_ = stack[0].m_obj;
lean_object* v_declHint_1839_ = stack[1].m_obj;
lean_object* v___y_1840_ = stack[2].m_obj;
lean_object* v___y_1841_ = stack[3].m_obj;
lean_object* v___y_1842_ = stack[4].m_obj;
lean_object* v___y_1843_ = stack[5].m_obj;
lean_object* v_res_1846_;
v_res_1846_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1838_, v_declHint_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
stack->m_obj
 = v_res_1846_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1847_, lean_object* v_declHint_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1847_, v_declHint_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1854_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1855_, lean_object* v_ref_1856_, lean_object* v_msg_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1856_, v_msg_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
return v___x_1863_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1856_ = stack[1].m_obj;
lean_object* v_msg_1857_ = stack[2].m_obj;
lean_object* v___y_1858_ = stack[3].m_obj;
lean_object* v___y_1859_ = stack[4].m_obj;
lean_object* v___y_1860_ = stack[5].m_obj;
lean_object* v___y_1861_ = stack[6].m_obj;
lean_object* v_res_1864_;
v_res_1864_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_box(0), v_ref_1856_, v_msg_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
stack->m_obj
 = v_res_1864_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1865_, lean_object* v_ref_1866_, lean_object* v_msg_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1865_, v_ref_1866_, v_msg_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v_ref_1866_);
return v_res_1873_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1876_, lean_object* v_val_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v_config_1881_; lean_object* v_extensions_1882_; lean_object* v_extra_1883_; lean_object* v_extraInj_1884_; lean_object* v_extraFacts_1885_; lean_object* v_symPrios_1886_; lean_object* v_norm_1887_; lean_object* v_normProcs_1888_; lean_object* v_anchorRefs_x3f_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1919_; 
v_config_1881_ = lean_ctor_get(v_params_1876_, 0);
v_extensions_1882_ = lean_ctor_get(v_params_1876_, 1);
v_extra_1883_ = lean_ctor_get(v_params_1876_, 2);
v_extraInj_1884_ = lean_ctor_get(v_params_1876_, 3);
v_extraFacts_1885_ = lean_ctor_get(v_params_1876_, 4);
v_symPrios_1886_ = lean_ctor_get(v_params_1876_, 5);
v_norm_1887_ = lean_ctor_get(v_params_1876_, 6);
v_normProcs_1888_ = lean_ctor_get(v_params_1876_, 7);
v_anchorRefs_x3f_1889_ = lean_ctor_get(v_params_1876_, 8);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_params_1876_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1891_ = v_params_1876_;
v_isShared_1892_ = v_isSharedCheck_1919_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_anchorRefs_x3f_1889_);
lean_inc(v_normProcs_1888_);
lean_inc(v_norm_1887_);
lean_inc(v_symPrios_1886_);
lean_inc(v_extraFacts_1885_);
lean_inc(v_extraInj_1884_);
lean_inc(v_extra_1883_);
lean_inc(v_extensions_1882_);
lean_inc(v_config_1881_);
lean_dec(v_params_1876_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1919_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___y_1894_; 
if (lean_obj_tag(v_anchorRefs_x3f_1889_) == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_1894_ = v___x_1917_;
goto v___jp_1893_;
}
else
{
lean_object* v_val_1918_; 
v_val_1918_ = lean_ctor_get(v_anchorRefs_x3f_1889_, 0);
lean_inc(v_val_1918_);
lean_dec_ref_known(v_anchorRefs_x3f_1889_, 1);
v___y_1894_ = v_val_1918_;
goto v___jp_1893_;
}
v___jp_1893_:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1877_, v_a_1878_, v_a_1879_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1908_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1908_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1908_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1900_ = lean_array_push(v___y_1894_, v_a_1896_);
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 8, v___x_1901_);
v___x_1903_ = v___x_1891_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_config_1881_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_extensions_1882_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_extra_1883_);
lean_ctor_set(v_reuseFailAlloc_1907_, 3, v_extraInj_1884_);
lean_ctor_set(v_reuseFailAlloc_1907_, 4, v_extraFacts_1885_);
lean_ctor_set(v_reuseFailAlloc_1907_, 5, v_symPrios_1886_);
lean_ctor_set(v_reuseFailAlloc_1907_, 6, v_norm_1887_);
lean_ctor_set(v_reuseFailAlloc_1907_, 7, v_normProcs_1888_);
lean_ctor_set(v_reuseFailAlloc_1907_, 8, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1905_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1903_);
v___x_1905_ = v___x_1898_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec_ref(v___y_1894_);
lean_del_object(v___x_1891_);
lean_dec_ref(v_normProcs_1888_);
lean_dec_ref(v_norm_1887_);
lean_dec_ref(v_symPrios_1886_);
lean_dec_ref(v_extraFacts_1885_);
lean_dec_ref(v_extraInj_1884_);
lean_dec_ref(v_extra_1883_);
lean_dec_ref(v_extensions_1882_);
lean_dec_ref(v_config_1881_);
v_a_1909_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1895_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1895_);
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
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_1876_ = stack[0].m_obj;
lean_object* v_val_1877_ = stack[1].m_obj;
lean_object* v_a_1878_ = stack[2].m_obj;
lean_object* v_a_1879_ = stack[3].m_obj;
lean_object* v_res_1920_;
v_res_1920_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_1876_, v_val_1877_, v_a_1878_, v_a_1879_);
stack->m_obj
 = v_res_1920_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_1921_, lean_object* v_val_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_1921_, v_val_1922_, v_a_1923_, v_a_1924_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_val_1922_);
return v_res_1926_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_1929_ = l_Lean_stringToMessageData(v___x_1928_);
return v___x_1929_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_config_1934_; uint8_t v_revert_1935_; 
v_config_1934_ = lean_ctor_get(v_params_1930_, 0);
v_revert_1935_ = lean_ctor_get_uint8(v_config_1934_, sizeof(void*)*14 + 30);
if (v_revert_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_1939_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1938_, v_a_1931_, v_a_1932_);
return v___x_1939_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_1930_ = stack[0].m_obj;
lean_object* v_a_1931_ = stack[1].m_obj;
lean_object* v_a_1932_ = stack[2].m_obj;
lean_object* v_res_1940_;
v_res_1940_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_1930_, v_a_1931_, v_a_1932_);
stack->m_obj
 = v_res_1940_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_params_1941_);
return v_res_1945_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_1946_, lean_object* v___y_1947_){
_start:
{
uint8_t v___x_1949_; 
v___x_1949_ = l_Lean_Expr_hasMVar(v_e_1946_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v_e_1946_);
return v___x_1950_;
}
else
{
lean_object* v___x_1951_; lean_object* v_mctx_1952_; lean_object* v___x_1953_; lean_object* v_fst_1954_; lean_object* v_snd_1955_; lean_object* v___x_1956_; lean_object* v_cache_1957_; lean_object* v_zetaDeltaFVarIds_1958_; lean_object* v_postponed_1959_; lean_object* v_diag_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1969_; 
v___x_1951_ = lean_st_ref_get(v___y_1947_);
v_mctx_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc_ref(v_mctx_1952_);
lean_dec(v___x_1951_);
v___x_1953_ = l_Lean_instantiateMVarsCore(v_mctx_1952_, v_e_1946_);
v_fst_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_fst_1954_);
v_snd_1955_ = lean_ctor_get(v___x_1953_, 1);
lean_inc(v_snd_1955_);
lean_dec_ref(v___x_1953_);
v___x_1956_ = lean_st_ref_take(v___y_1947_);
v_cache_1957_ = lean_ctor_get(v___x_1956_, 1);
v_zetaDeltaFVarIds_1958_ = lean_ctor_get(v___x_1956_, 2);
v_postponed_1959_ = lean_ctor_get(v___x_1956_, 3);
v_diag_1960_ = lean_ctor_get(v___x_1956_, 4);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v___x_1956_, 0);
lean_dec(v_unused_1970_);
v___x_1962_ = v___x_1956_;
v_isShared_1963_ = v_isSharedCheck_1969_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_diag_1960_);
lean_inc(v_postponed_1959_);
lean_inc(v_zetaDeltaFVarIds_1958_);
lean_inc(v_cache_1957_);
lean_dec(v___x_1956_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1969_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v_snd_1955_);
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_snd_1955_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_cache_1957_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v_zetaDeltaFVarIds_1958_);
lean_ctor_set(v_reuseFailAlloc_1968_, 3, v_postponed_1959_);
lean_ctor_set(v_reuseFailAlloc_1968_, 4, v_diag_1960_);
v___x_1965_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = lean_st_ref_put(v___y_1947_, v___x_1965_);
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_fst_1954_);
return v___x_1967_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1946_ = stack[0].m_obj;
lean_object* v___y_1947_ = stack[1].m_obj;
lean_object* v_res_1971_;
v_res_1971_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1946_, v___y_1947_);
stack->m_obj
 = v_res_1971_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1972_, v___y_1973_);
lean_dec(v___y_1973_);
return v_res_1975_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1976_, v___y_1980_);
return v___x_1984_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1976_ = stack[0].m_obj;
lean_object* v___y_1977_ = stack[1].m_obj;
lean_object* v___y_1978_ = stack[2].m_obj;
lean_object* v___y_1979_ = stack[3].m_obj;
lean_object* v___y_1980_ = stack[4].m_obj;
lean_object* v___y_1981_ = stack[5].m_obj;
lean_object* v___y_1982_ = stack[6].m_obj;
lean_object* v_res_1985_;
v_res_1985_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
stack->m_obj
 = v_res_1985_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1994_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(uint8_t v___x_1995_, uint8_t v___x_1996_, uint8_t v_____do__lift_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
if (v_____do__lift_1997_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = lean_box(v___x_1995_);
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
return v___x_2006_;
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_box(v___x_1996_);
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
return v___x_2008_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1995_ = stack[0].m_num;
uint8_t v___x_1996_ = stack[1].m_num;
uint8_t v_____do__lift_1997_ = stack[2].m_num;
lean_object* v___y_1998_ = stack[3].m_obj;
lean_object* v___y_1999_ = stack[4].m_obj;
lean_object* v___y_2000_ = stack[5].m_obj;
lean_object* v___y_2001_ = stack[6].m_obj;
lean_object* v___y_2002_ = stack[7].m_obj;
lean_object* v___y_2003_ = stack[8].m_obj;
lean_object* v_res_2009_;
v_res_2009_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_1995_, v___x_1996_, v_____do__lift_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
stack->m_obj
 = v_res_2009_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v___x_2010_, lean_object* v___x_2011_, lean_object* v_____do__lift_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
uint8_t v___x_14755__boxed_2020_; uint8_t v___x_14756__boxed_2021_; uint8_t v_____do__lift_14757__boxed_2022_; lean_object* v_res_2023_; 
v___x_14755__boxed_2020_ = lean_unbox(v___x_2010_);
v___x_14756__boxed_2021_ = lean_unbox(v___x_2011_);
v_____do__lift_14757__boxed_2022_ = lean_unbox(v_____do__lift_2012_);
v_res_2023_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_14755__boxed_2020_, v___x_14756__boxed_2021_, v_____do__lift_14757__boxed_2022_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2023_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(uint8_t v___x_2024_, uint8_t v___x_2025_, lean_object* v_as_2026_, size_t v_i_2027_, size_t v_stop_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
uint8_t v___x_2034_; 
v___x_2034_ = lean_usize_dec_eq(v_i_2027_, v_stop_2028_);
if (v___x_2034_ == 0)
{
uint8_t v___x_2035_; uint8_t v_a_2037_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2035_ = 1;
v___x_2043_ = lean_array_uget_borrowed(v_as_2026_, v_i_2027_);
lean_inc(v___x_2043_);
v___x_2044_ = l_Lean_Meta_isProof(v___x_2043_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; uint8_t v___x_2046_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
v___x_2046_ = lean_unbox(v_a_2045_);
lean_dec(v_a_2045_);
if (v___x_2046_ == 0)
{
v_a_2037_ = v___x_2024_;
goto v___jp_2036_;
}
else
{
v_a_2037_ = v___x_2025_;
goto v___jp_2036_;
}
}
else
{
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2047_; uint8_t v___x_2048_; 
v_a_2047_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2044_, 1);
v___x_2048_ = lean_unbox(v_a_2047_);
lean_dec(v_a_2047_);
v_a_2037_ = v___x_2048_;
goto v___jp_2036_;
}
else
{
return v___x_2044_;
}
}
v___jp_2036_:
{
if (v_a_2037_ == 0)
{
size_t v___x_2038_; size_t v___x_2039_; 
v___x_2038_ = ((size_t)1ULL);
v___x_2039_ = lean_usize_add(v_i_2027_, v___x_2038_);
v_i_2027_ = v___x_2039_;
goto _start;
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_box(v___x_2035_);
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
return v___x_2042_;
}
}
}
else
{
uint8_t v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = 0;
v___x_2050_ = lean_box(v___x_2049_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2024_ = stack[0].m_num;
uint8_t v___x_2025_ = stack[1].m_num;
lean_object* v_as_2026_ = stack[2].m_obj;
size_t v_i_2027_ = stack[3].m_num;
size_t v_stop_2028_ = stack[4].m_num;
lean_object* v___y_2029_ = stack[5].m_obj;
lean_object* v___y_2030_ = stack[6].m_obj;
lean_object* v___y_2031_ = stack[7].m_obj;
lean_object* v___y_2032_ = stack[8].m_obj;
lean_object* v_res_2052_;
v_res_2052_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2024_, v___x_2025_, v_as_2026_, v_i_2027_, v_stop_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
stack->m_obj
 = v_res_2052_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v___x_2053_, lean_object* v___x_2054_, lean_object* v_as_2055_, lean_object* v_i_2056_, lean_object* v_stop_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
uint8_t v___x_14817__boxed_2063_; uint8_t v___x_14818__boxed_2064_; size_t v_i_boxed_2065_; size_t v_stop_boxed_2066_; lean_object* v_res_2067_; 
v___x_14817__boxed_2063_ = lean_unbox(v___x_2053_);
v___x_14818__boxed_2064_ = lean_unbox(v___x_2054_);
v_i_boxed_2065_ = lean_unbox_usize(v_i_2056_);
lean_dec(v_i_2056_);
v_stop_boxed_2066_ = lean_unbox_usize(v_stop_2057_);
lean_dec(v_stop_2057_);
v_res_2067_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_14817__boxed_2063_, v___x_14818__boxed_2064_, v_as_2055_, v_i_boxed_2065_, v_stop_boxed_2066_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec_ref(v_as_2055_);
return v_res_2067_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_p_2070_, lean_object* v_term_2071_, lean_object* v___x_2072_, uint8_t v___x_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_toCold_2081_; lean_object* v_currRecDepth_2082_; lean_object* v_ref_2083_; uint16_t v_optionFlags_2084_; uint8_t v_suppressElabErrors_2085_; uint8_t v_isRecordingDeps_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2183_; 
v_toCold_2081_ = lean_ctor_get(v___y_2078_, 0);
v_currRecDepth_2082_ = lean_ctor_get(v___y_2078_, 1);
v_ref_2083_ = lean_ctor_get(v___y_2078_, 2);
v_optionFlags_2084_ = lean_ctor_get_uint16(v___y_2078_, sizeof(void*)*3);
v_suppressElabErrors_2085_ = lean_ctor_get_uint8(v___y_2078_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2086_ = lean_ctor_get_uint8(v___y_2078_, sizeof(void*)*3 + 3);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___y_2078_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2088_ = v___y_2078_;
v_isShared_2089_ = v_isSharedCheck_2183_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_ref_2083_);
lean_inc(v_currRecDepth_2082_);
lean_inc(v_toCold_2081_);
lean_dec(v___y_2078_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2183_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_ref_2090_; lean_object* v___x_2092_; 
v_ref_2090_ = l_Lean_replaceRef(v_p_2070_, v_ref_2083_);
lean_dec(v_ref_2083_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 2, v_ref_2090_);
v___x_2092_ = v___x_2088_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_toCold_2081_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_currRecDepth_2082_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v_ref_2090_);
lean_ctor_set_uint16(v_reuseFailAlloc_2182_, sizeof(void*)*3, v_optionFlags_2084_);
lean_ctor_set_uint8(v_reuseFailAlloc_2182_, sizeof(void*)*3 + 2, v_suppressElabErrors_2085_);
lean_ctor_set_uint8(v_reuseFailAlloc_2182_, sizeof(void*)*3 + 3, v_isRecordingDeps_2086_);
v___x_2092_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_Elab_Term_elabTerm(v_term_2071_, v___x_2072_, v___x_2073_, v___x_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___x_2092_, v___y_2079_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
v___x_2095_ = 1;
v___x_2096_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_2095_, v___x_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___x_2092_, v___y_2079_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v___x_2097_; lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2165_; 
lean_dec_ref_known(v___x_2096_, 1);
v___x_2097_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_2094_, v___y_2077_);
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2165_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2165_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
uint8_t v___x_2102_; 
v___x_2102_ = l_Lean_Expr_hasSyntheticSorry(v_a_2098_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = l_Lean_Expr_eta(v_a_2098_);
v___x_2104_ = l_Lean_Expr_hasMVar(v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2111_; 
lean_dec_ref(v___x_2092_);
v___x_2105_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0));
v___x_2106_ = lean_box(v___x_2104_);
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2103_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2105_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2109_);
v___x_2111_ = v___x_2100_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
else
{
lean_object* v___x_2113_; 
lean_del_object(v___x_2100_);
v___x_2113_ = l_Lean_Meta_abstractMVars(v___x_2103_, v___x_2073_, v___y_2076_, v___y_2077_, v___x_2092_, v___y_2079_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2152_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2152_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2152_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v_paramNames_2118_; lean_object* v_mvars_2119_; lean_object* v_expr_2120_; uint8_t v_a_2122_; lean_object* v___y_2131_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v_paramNames_2118_ = lean_ctor_get(v_a_2114_, 0);
lean_inc_ref(v_paramNames_2118_);
v_mvars_2119_ = lean_ctor_get(v_a_2114_, 1);
lean_inc_ref(v_mvars_2119_);
v_expr_2120_ = lean_ctor_get(v_a_2114_, 2);
lean_inc_ref(v_expr_2120_);
lean_dec(v_a_2114_);
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = lean_array_get_size(v_mvars_2119_);
v___x_2144_ = lean_nat_dec_lt(v___x_2142_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; 
lean_dec_ref(v_mvars_2119_);
v___x_2145_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2104_, v___x_2102_, v___x_2144_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___x_2092_, v___y_2079_);
lean_dec_ref(v___x_2092_);
v___y_2131_ = v___x_2145_;
goto v___jp_2130_;
}
else
{
if (v___x_2144_ == 0)
{
lean_dec_ref(v_mvars_2119_);
lean_dec_ref(v___x_2092_);
v_a_2122_ = v___x_2104_;
goto v___jp_2121_;
}
else
{
size_t v___x_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = ((size_t)0ULL);
v___x_2147_ = lean_usize_of_nat(v___x_2143_);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2104_, v___x_2102_, v_mvars_2119_, v___x_2146_, v___x_2147_, v___y_2076_, v___y_2077_, v___x_2092_, v___y_2079_);
lean_dec_ref(v_mvars_2119_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2148_, 1);
v___x_2150_ = lean_unbox(v_a_2149_);
lean_dec(v_a_2149_);
v___x_2151_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2104_, v___x_2102_, v___x_2150_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___x_2092_, v___y_2079_);
lean_dec_ref(v___x_2092_);
v___y_2131_ = v___x_2151_;
goto v___jp_2130_;
}
else
{
lean_dec_ref(v___x_2092_);
v___y_2131_ = v___x_2148_;
goto v___jp_2130_;
}
}
}
v___jp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2123_ = lean_box(v_a_2122_);
v___x_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2124_, 0, v_expr_2120_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v_paramNames_2118_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2126_);
v___x_2128_ = v___x_2116_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
v___jp_2130_:
{
if (lean_obj_tag(v___y_2131_) == 0)
{
lean_object* v_a_2132_; uint8_t v___x_2133_; 
v_a_2132_ = lean_ctor_get(v___y_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___y_2131_, 1);
v___x_2133_ = lean_unbox(v_a_2132_);
lean_dec(v_a_2132_);
v_a_2122_ = v___x_2133_;
goto v___jp_2121_;
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_expr_2120_);
lean_dec_ref(v_paramNames_2118_);
lean_del_object(v___x_2116_);
v_a_2134_ = lean_ctor_get(v___y_2131_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___y_2131_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___y_2131_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___y_2131_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v___x_2092_);
v_a_2153_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2113_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2113_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
lean_dec(v_a_2098_);
lean_dec_ref(v___x_2092_);
v___x_2161_ = lean_box(0);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2161_);
v___x_2163_ = v___x_2100_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v_a_2094_);
lean_dec_ref(v___x_2092_);
v_a_2166_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2096_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2096_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec_ref(v___x_2092_);
v_a_2174_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2093_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2093_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2070_ = stack[0].m_obj;
lean_object* v_term_2071_ = stack[1].m_obj;
lean_object* v___x_2072_ = stack[2].m_obj;
uint8_t v___x_2073_ = stack[3].m_num;
lean_object* v___y_2074_ = stack[4].m_obj;
lean_object* v___y_2075_ = stack[5].m_obj;
lean_object* v___y_2076_ = stack[6].m_obj;
lean_object* v___y_2077_ = stack[7].m_obj;
lean_object* v___y_2078_ = stack[8].m_obj;
lean_object* v___y_2079_ = stack[9].m_obj;
lean_object* v_res_2184_;
v_res_2184_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_p_2070_, v_term_2071_, v___x_2072_, v___x_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
stack->m_obj
 = v_res_2184_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_p_2185_, lean_object* v_term_2186_, lean_object* v___x_2187_, lean_object* v___x_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
uint8_t v___x_14912__boxed_2196_; lean_object* v_res_2197_; 
v___x_14912__boxed_2196_ = lean_unbox(v___x_2188_);
v_res_2197_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_p_2185_, v_term_2186_, v___x_2187_, v___x_14912__boxed_2196_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v_p_2185_);
return v_res_2197_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__2));
v___x_2203_ = l_Lean_stringToMessageData(v___x_2202_);
return v___x_2203_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(lean_object* v_params_2204_, lean_object* v_p_2205_, lean_object* v_fst_2206_, lean_object* v_fst_2207_, uint8_t v___x_2208_, uint8_t v_minIndexable_2209_, lean_object* v_kind_2210_, lean_object* v_idx_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_symPrios_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2222_; 
v_symPrios_2217_ = lean_ctor_get(v_params_2204_, 5);
lean_inc_ref(v_symPrios_2217_);
lean_dec_ref(v_params_2204_);
v___x_2218_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__1));
v___x_2219_ = lean_name_append_index_after(v___x_2218_, v_idx_2211_);
v___x_2220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v_p_2205_);
v___x_2221_ = 0;
v___x_2222_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2220_, v_fst_2206_, v_fst_2207_, v_kind_2210_, v_symPrios_2217_, v___x_2208_, v___x_2221_, v_minIndexable_2209_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2233_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2233_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2233_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
if (lean_obj_tag(v_a_2223_) == 1)
{
lean_object* v_val_2227_; lean_object* v___x_2229_; 
v_val_2227_ = lean_ctor_get(v_a_2223_, 0);
lean_inc(v_val_2227_);
lean_dec_ref_known(v_a_2223_, 1);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v_val_2227_);
v___x_2229_ = v___x_2225_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_val_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
lean_del_object(v___x_2225_);
lean_dec(v_a_2223_);
v___x_2231_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3);
v___x_2232_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2231_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2232_;
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
v_a_2234_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2222_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2222_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_2204_ = stack[0].m_obj;
lean_object* v_p_2205_ = stack[1].m_obj;
lean_object* v_fst_2206_ = stack[2].m_obj;
lean_object* v_fst_2207_ = stack[3].m_obj;
uint8_t v___x_2208_ = stack[4].m_num;
uint8_t v_minIndexable_2209_ = stack[5].m_num;
lean_object* v_kind_2210_ = stack[6].m_obj;
lean_object* v_idx_2211_ = stack[7].m_obj;
lean_object* v___y_2212_ = stack[8].m_obj;
lean_object* v___y_2213_ = stack[9].m_obj;
lean_object* v___y_2214_ = stack[10].m_obj;
lean_object* v___y_2215_ = stack[11].m_obj;
lean_object* v_res_2242_;
v_res_2242_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(v_params_2204_, v_p_2205_, v_fst_2206_, v_fst_2207_, v___x_2208_, v_minIndexable_2209_, v_kind_2210_, v_idx_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
stack->m_obj
 = v_res_2242_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed(lean_object* v_params_2243_, lean_object* v_p_2244_, lean_object* v_fst_2245_, lean_object* v_fst_2246_, lean_object* v___x_2247_, lean_object* v_minIndexable_2248_, lean_object* v_kind_2249_, lean_object* v_idx_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
uint8_t v___x_15256__boxed_2256_; uint8_t v_minIndexable_boxed_2257_; lean_object* v_res_2258_; 
v___x_15256__boxed_2256_ = lean_unbox(v___x_2247_);
v_minIndexable_boxed_2257_ = lean_unbox(v_minIndexable_2248_);
v_res_2258_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(v_params_2243_, v_p_2244_, v_fst_2245_, v_fst_2246_, v___x_15256__boxed_2256_, v_minIndexable_boxed_2257_, v_kind_2249_, v_idx_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2258_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = lean_box(1);
v___x_2260_ = l_Lean_MessageData_ofFormat(v___x_2259_);
return v___x_2260_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__2));
v___x_2265_ = l_Lean_MessageData_ofFormat(v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(lean_object* v_x_2266_, lean_object* v_x_2267_){
_start:
{
if (lean_obj_tag(v_x_2267_) == 0)
{
return v_x_2266_;
}
else
{
lean_object* v_head_2268_; lean_object* v_tail_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2291_; 
v_head_2268_ = lean_ctor_get(v_x_2267_, 0);
v_tail_2269_ = lean_ctor_get(v_x_2267_, 1);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_x_2267_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2271_ = v_x_2267_;
v_isShared_2272_ = v_isSharedCheck_2291_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_tail_2269_);
lean_inc(v_head_2268_);
lean_dec(v_x_2267_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2291_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v_before_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2289_; 
v_before_2273_ = lean_ctor_get(v_head_2268_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_head_2268_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; 
v_unused_2290_ = lean_ctor_get(v_head_2268_, 1);
lean_dec(v_unused_2290_);
v___x_2275_ = v_head_2268_;
v_isShared_2276_ = v_isSharedCheck_2289_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_before_2273_);
lean_dec(v_head_2268_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2289_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2277_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2276_ == 0)
{
lean_ctor_set_tag(v___x_2275_, 7);
lean_ctor_set(v___x_2275_, 1, v___x_2277_);
lean_ctor_set(v___x_2275_, 0, v_x_2266_);
v___x_2279_ = v___x_2275_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_x_2266_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2280_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3);
if (v_isShared_2272_ == 0)
{
lean_ctor_set_tag(v___x_2271_, 7);
lean_ctor_set(v___x_2271_, 1, v___x_2280_);
lean_ctor_set(v___x_2271_, 0, v___x_2279_);
v___x_2282_ = v___x_2271_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = l_Lean_MessageData_ofSyntax(v_before_2273_);
v___x_2284_ = l_Lean_indentD(v___x_2283_);
v___x_2285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2282_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v_x_2266_ = v___x_2285_;
v_x_2267_ = v_tail_2269_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__1));
v___x_2296_ = l_Lean_MessageData_ofFormat(v___x_2295_);
return v___x_2296_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(lean_object* v_msgData_2297_, lean_object* v_macroStack_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2301_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2299_);
v___x_2302_ = l_Lean_Elab_pp_macroStack;
v___x_2303_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_2301_, v___x_2302_);
lean_dec_ref(v___x_2301_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; 
lean_dec(v_macroStack_2298_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_msgData_2297_);
return v___x_2304_;
}
else
{
if (lean_obj_tag(v_macroStack_2298_) == 0)
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2305_, 0, v_msgData_2297_);
return v___x_2305_;
}
else
{
lean_object* v_head_2306_; lean_object* v_after_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2322_; 
v_head_2306_ = lean_ctor_get(v_macroStack_2298_, 0);
lean_inc(v_head_2306_);
v_after_2307_ = lean_ctor_get(v_head_2306_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_head_2306_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v_head_2306_, 0);
lean_dec(v_unused_2323_);
v___x_2309_ = v_head_2306_;
v_isShared_2310_ = v_isSharedCheck_2322_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_after_2307_);
lean_dec(v_head_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2322_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2310_ == 0)
{
lean_ctor_set_tag(v___x_2309_, 7);
lean_ctor_set(v___x_2309_, 1, v___x_2311_);
lean_ctor_set(v___x_2309_, 0, v_msgData_2297_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_msgData_2297_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v_msgData_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2314_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = l_Lean_MessageData_ofSyntax(v_after_2307_);
v___x_2317_ = l_Lean_indentD(v___x_2316_);
v_msgData_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2318_, 0, v___x_2315_);
lean_ctor_set(v_msgData_2318_, 1, v___x_2317_);
v___x_2319_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(v_msgData_2318_, v_macroStack_2298_);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
return v___x_2320_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2297_ = stack[0].m_obj;
lean_object* v_macroStack_2298_ = stack[1].m_obj;
lean_object* v___y_2299_ = stack[2].m_obj;
lean_object* v_res_2324_;
v_res_2324_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2297_, v_macroStack_2298_, v___y_2299_);
stack->m_obj
 = v_res_2324_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_2325_, lean_object* v_macroStack_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2325_, v_macroStack_2326_, v___y_2327_);
lean_dec_ref(v___y_2327_);
return v_res_2329_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(lean_object* v_msg_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_ref_2338_; lean_object* v_macroStack_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v_a_2342_; lean_object* v___x_2343_; lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2352_; 
v_ref_2338_ = lean_ctor_get(v___y_2335_, 2);
v_macroStack_2339_ = lean_ctor_get(v___y_2331_, 1);
v___x_2340_ = l_Lean_Elab_getBetterRef(v_ref_2338_, v_macroStack_2339_);
v___x_2341_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2330_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref(v___x_2341_);
lean_inc(v_macroStack_2339_);
v___x_2343_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_a_2342_, v_macroStack_2339_, v___y_2335_);
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2352_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2352_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2340_);
lean_ctor_set(v___x_2348_, 1, v_a_2344_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set_tag(v___x_2346_, 1);
lean_ctor_set(v___x_2346_, 0, v___x_2348_);
v___x_2350_ = v___x_2346_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2330_ = stack[0].m_obj;
lean_object* v___y_2331_ = stack[1].m_obj;
lean_object* v___y_2332_ = stack[2].m_obj;
lean_object* v___y_2333_ = stack[3].m_obj;
lean_object* v___y_2334_ = stack[4].m_obj;
lean_object* v___y_2335_ = stack[5].m_obj;
lean_object* v___y_2336_ = stack[6].m_obj;
lean_object* v_res_2353_;
v_res_2353_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
stack->m_obj
 = v_res_2353_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg___boxed(lean_object* v_msg_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2362_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2365_ = l_Lean_stringToMessageData(v___x_2364_);
return v___x_2365_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2368_ = l_Lean_stringToMessageData(v___x_2367_);
return v___x_2368_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2371_ = l_Lean_stringToMessageData(v___x_2370_);
return v___x_2371_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_2374_ = l_Lean_stringToMessageData(v___x_2373_);
return v___x_2374_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2377_, lean_object* v_p_2378_, lean_object* v_mod_x3f_2379_, lean_object* v_term_2380_, uint8_t v_minIndexable_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___y_2390_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; uint8_t v___y_2530_; uint8_t v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v_kind_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v_toCold_2751_; lean_object* v_currRecDepth_2752_; lean_object* v_ref_2753_; uint16_t v_optionFlags_2754_; uint8_t v_suppressElabErrors_2755_; uint8_t v_isRecordingDeps_2756_; lean_object* v_ref_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_toCold_2751_ = lean_ctor_get(v_a_2386_, 0);
v_currRecDepth_2752_ = lean_ctor_get(v_a_2386_, 1);
v_ref_2753_ = lean_ctor_get(v_a_2386_, 2);
v_optionFlags_2754_ = lean_ctor_get_uint16(v_a_2386_, sizeof(void*)*3);
v_suppressElabErrors_2755_ = lean_ctor_get_uint8(v_a_2386_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2756_ = lean_ctor_get_uint8(v_a_2386_, sizeof(void*)*3 + 3);
v_ref_2757_ = l_Lean_replaceRef(v_p_2378_, v_ref_2753_);
lean_inc(v_currRecDepth_2752_);
lean_inc_ref(v_toCold_2751_);
v___x_2758_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2758_, 0, v_toCold_2751_);
lean_ctor_set(v___x_2758_, 1, v_currRecDepth_2752_);
lean_ctor_set(v___x_2758_, 2, v_ref_2757_);
lean_ctor_set_uint16(v___x_2758_, sizeof(void*)*3, v_optionFlags_2754_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*3 + 2, v_suppressElabErrors_2755_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*3 + 3, v_isRecordingDeps_2756_);
v___x_2759_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2377_, v___x_2758_, v_a_2387_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_dec_ref_known(v___x_2759_, 1);
if (lean_obj_tag(v_mod_x3f_2379_) == 1)
{
lean_object* v_val_2760_; lean_object* v___x_2761_; 
v_val_2760_ = lean_ctor_get(v_mod_x3f_2379_, 0);
lean_inc(v_val_2760_);
v___x_2761_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2760_, v___x_2758_, v_a_2387_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
switch(lean_obj_tag(v_a_2762_))
{
case 0:
{
lean_object* v_k_2763_; 
v_k_2763_ = lean_ctor_get(v_a_2762_, 0);
lean_inc(v_k_2763_);
lean_dec_ref_known(v_a_2762_, 1);
if (lean_obj_tag(v_k_2763_) == 9)
{
lean_dec_ref_known(v_mod_x3f_2379_, 1);
lean_dec(v_term_2380_);
lean_dec(v_p_2378_);
lean_dec_ref(v_params_2377_);
v___y_2710_ = v_a_2382_;
v___y_2711_ = v_a_2383_;
v___y_2712_ = v_a_2384_;
v___y_2713_ = v_a_2385_;
v___y_2714_ = v___x_2758_;
v___y_2715_ = v_a_2387_;
goto v___jp_2709_;
}
else
{
v_kind_2641_ = v_k_2763_;
v___y_2642_ = v_a_2382_;
v___y_2643_ = v_a_2383_;
v___y_2644_ = v_a_2384_;
v___y_2645_ = v_a_2385_;
v___y_2646_ = v___x_2758_;
v___y_2647_ = v_a_2387_;
goto v___jp_2640_;
}
}
case 1:
{
lean_dec_ref_known(v_a_2762_, 0);
lean_dec_ref_known(v_mod_x3f_2379_, 1);
lean_dec(v_term_2380_);
lean_dec(v_p_2378_);
lean_dec_ref(v_params_2377_);
v___y_2727_ = v_a_2382_;
v___y_2728_ = v_a_2383_;
v___y_2729_ = v_a_2384_;
v___y_2730_ = v_a_2385_;
v___y_2731_ = v___x_2758_;
v___y_2732_ = v_a_2387_;
goto v___jp_2726_;
}
case 3:
{
v___y_2744_ = v_a_2382_;
v___y_2745_ = v_a_2383_;
v___y_2746_ = v_a_2384_;
v___y_2747_ = v_a_2385_;
v___y_2748_ = v___x_2758_;
v___y_2749_ = v_a_2387_;
goto v___jp_2743_;
}
case 5:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec_ref_known(v_a_2762_, 1);
lean_dec_ref_known(v_mod_x3f_2379_, 1);
lean_dec(v_term_2380_);
lean_dec(v_p_2378_);
lean_dec_ref(v_params_2377_);
v___x_2764_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2765_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2764_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v___x_2758_, v_a_2387_);
lean_dec_ref_known(v___x_2758_, 3);
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
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
case 8:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec_ref_known(v_a_2762_, 0);
lean_dec_ref_known(v_mod_x3f_2379_, 1);
lean_dec(v_term_2380_);
lean_dec(v_p_2378_);
lean_dec_ref(v_params_2377_);
v___x_2774_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2775_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2774_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v___x_2758_, v_a_2387_);
lean_dec_ref_known(v___x_2758_, 3);
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
case 10:
{
lean_dec_ref_known(v_a_2762_, 0);
lean_dec_ref_known(v_mod_x3f_2379_, 1);
lean_dec(v_term_2380_);
lean_dec(v_p_2378_);
lean_dec_ref(v_params_2377_);
v___y_2727_ = v_a_2382_;
v___y_2728_ = v_a_2383_;
v___y_2729_ = v_a_2384_;
v___y_2730_ = v_a_2385_;
v___y_2731_ = v___x_2758_;
v___y_2732_ = v_a_2387_;
goto v___jp_2726_;
}
default: 
{
lean_dec(v_a_2762_);
lean_dec_ref_known(v_mod_x3f_2379_, 1);
lean_dec(v_term_2380_);
lean_dec(v_p_2378_);
lean_dec_ref(v_params_2377_);
v___y_2710_ = v_a_2382_;
v___y_2711_ = v_a_2383_;
v___y_2712_ = v_a_2384_;
v___y_2713_ = v_a_2385_;
v___y_2714_ = v___x_2758_;
v___y_2715_ = v_a_2387_;
goto v___jp_2709_;
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec_ref_known(v_mod_x3f_2379_, 1);
lean_dec_ref_known(v___x_2758_, 3);
lean_dec(v_term_2380_);
lean_dec(v_p_2378_);
lean_dec_ref(v_params_2377_);
v_a_2784_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2761_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2761_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
v___y_2744_ = v_a_2382_;
v___y_2745_ = v_a_2383_;
v___y_2746_ = v_a_2384_;
v___y_2747_ = v_a_2385_;
v___y_2748_ = v___x_2758_;
v___y_2749_ = v_a_2387_;
goto v___jp_2743_;
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec_ref_known(v___x_2758_, 3);
lean_dec(v_term_2380_);
lean_dec(v_mod_x3f_2379_);
lean_dec(v_p_2378_);
lean_dec_ref(v_params_2377_);
v_a_2792_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2759_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2759_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
v___jp_2389_:
{
lean_object* v_config_2391_; lean_object* v_extensions_2392_; lean_object* v_extra_2393_; lean_object* v_extraInj_2394_; lean_object* v_extraFacts_2395_; lean_object* v_symPrios_2396_; lean_object* v_norm_2397_; lean_object* v_normProcs_2398_; lean_object* v_anchorRefs_x3f_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2408_; 
v_config_2391_ = lean_ctor_get(v_params_2377_, 0);
v_extensions_2392_ = lean_ctor_get(v_params_2377_, 1);
v_extra_2393_ = lean_ctor_get(v_params_2377_, 2);
v_extraInj_2394_ = lean_ctor_get(v_params_2377_, 3);
v_extraFacts_2395_ = lean_ctor_get(v_params_2377_, 4);
v_symPrios_2396_ = lean_ctor_get(v_params_2377_, 5);
v_norm_2397_ = lean_ctor_get(v_params_2377_, 6);
v_normProcs_2398_ = lean_ctor_get(v_params_2377_, 7);
v_anchorRefs_x3f_2399_ = lean_ctor_get(v_params_2377_, 8);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_params_2377_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2401_ = v_params_2377_;
v_isShared_2402_ = v_isSharedCheck_2408_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_anchorRefs_x3f_2399_);
lean_inc(v_normProcs_2398_);
lean_inc(v_norm_2397_);
lean_inc(v_symPrios_2396_);
lean_inc(v_extraFacts_2395_);
lean_inc(v_extraInj_2394_);
lean_inc(v_extra_2393_);
lean_inc(v_extensions_2392_);
lean_inc(v_config_2391_);
lean_dec(v_params_2377_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2408_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2395_, v___y_2390_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 4, v___x_2403_);
v___x_2405_ = v___x_2401_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_config_2391_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_extensions_2392_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_extra_2393_);
lean_ctor_set(v_reuseFailAlloc_2407_, 3, v_extraInj_2394_);
lean_ctor_set(v_reuseFailAlloc_2407_, 4, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2407_, 5, v_symPrios_2396_);
lean_ctor_set(v_reuseFailAlloc_2407_, 6, v_norm_2397_);
lean_ctor_set(v_reuseFailAlloc_2407_, 7, v_normProcs_2398_);
lean_ctor_set(v_reuseFailAlloc_2407_, 8, v_anchorRefs_x3f_2399_);
v___x_2405_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
return v___x_2406_;
}
}
}
v___jp_2409_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2419_ = lean_array_get_size(v___y_2412_);
lean_dec_ref(v___y_2412_);
v___x_2420_ = lean_unsigned_to_nat(0u);
v___x_2421_ = lean_nat_dec_eq(v___x_2419_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec_ref(v___y_2410_);
lean_dec_ref(v_params_2377_);
v___x_2422_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2423_ = l_Lean_indentExpr(v___y_2411_);
v___x_2424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2424_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec_ref(v___y_2417_);
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
else
{
lean_dec_ref(v___y_2417_);
lean_dec_ref(v___y_2411_);
v___y_2390_ = v___y_2410_;
goto v___jp_2389_;
}
}
v___jp_2434_:
{
if (lean_obj_tag(v_mod_x3f_2379_) == 0)
{
v___y_2410_ = v___y_2441_;
v___y_2411_ = v___y_2440_;
v___y_2412_ = v___y_2439_;
v___y_2413_ = v___y_2436_;
v___y_2414_ = v___y_2438_;
v___y_2415_ = v___y_2442_;
v___y_2416_ = v___y_2437_;
v___y_2417_ = v___y_2435_;
v___y_2418_ = v___y_2443_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec_ref_known(v_mod_x3f_2379_, 1);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___y_2439_);
lean_dec_ref(v_params_2377_);
v___x_2444_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2445_ = l_Lean_indentExpr(v___y_2440_);
v___x_2446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2444_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2446_, v___y_2436_, v___y_2438_, v___y_2442_, v___y_2437_, v___y_2435_, v___y_2443_);
lean_dec_ref(v___y_2435_);
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
v___jp_2456_:
{
lean_object* v___x_2473_; 
lean_inc(v___y_2472_);
lean_inc(v___y_2470_);
lean_inc_ref(v___y_2469_);
v___x_2473_ = lean_apply_7(v___y_2463_, v___y_2462_, v___y_2464_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, lean_box(0));
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2483_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2476_ = v___x_2473_;
v_isShared_2477_ = v_isSharedCheck_2483_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2473_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2483_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2478_ = l_Lean_PersistentArray_push___redArg(v___y_2458_, v_a_2474_);
v___x_2479_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2479_, 0, v___y_2466_);
lean_ctor_set(v___x_2479_, 1, v___y_2461_);
lean_ctor_set(v___x_2479_, 2, v___x_2478_);
lean_ctor_set(v___x_2479_, 3, v___y_2459_);
lean_ctor_set(v___x_2479_, 4, v___y_2467_);
lean_ctor_set(v___x_2479_, 5, v___y_2457_);
lean_ctor_set(v___x_2479_, 6, v___y_2465_);
lean_ctor_set(v___x_2479_, 7, v___y_2460_);
lean_ctor_set(v___x_2479_, 8, v___y_2468_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 0, v___x_2479_);
v___x_2481_ = v___x_2476_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec_ref(v___y_2457_);
v_a_2484_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2473_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2473_);
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
v___jp_2492_:
{
lean_object* v___x_2509_; 
v___x_2509_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2381_, v___y_2497_, v___y_2501_, v___y_2500_, v___y_2508_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_dec_ref_known(v___x_2509_, 1);
v___y_2457_ = v___y_2502_;
v___y_2458_ = v___y_2493_;
v___y_2459_ = v___y_2494_;
v___y_2460_ = v___y_2503_;
v___y_2461_ = v___y_2495_;
v___y_2462_ = v___y_2496_;
v___y_2463_ = v___y_2504_;
v___y_2464_ = v___y_2505_;
v___y_2465_ = v___y_2507_;
v___y_2466_ = v___y_2506_;
v___y_2467_ = v___y_2498_;
v___y_2468_ = v___y_2499_;
v___y_2469_ = v___y_2497_;
v___y_2470_ = v___y_2501_;
v___y_2471_ = v___y_2500_;
v___y_2472_ = v___y_2508_;
goto v___jp_2456_;
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec_ref(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec_ref(v___y_2493_);
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
v___jp_2518_:
{
if (v___y_2530_ == 0)
{
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
v___y_2435_ = v___y_2520_;
v___y_2436_ = v___y_2519_;
v___y_2437_ = v___y_2521_;
v___y_2438_ = v___y_2522_;
v___y_2439_ = v___y_2527_;
v___y_2440_ = v___y_2526_;
v___y_2441_ = v___y_2525_;
v___y_2442_ = v___y_2528_;
v___y_2443_ = v___y_2529_;
goto v___jp_2434_;
}
else
{
lean_object* v_extra_2531_; 
lean_dec_ref(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v_mod_x3f_2379_);
v_extra_2531_ = lean_ctor_get(v_params_2377_, 2);
lean_inc_ref(v_extra_2531_);
if (lean_obj_tag(v___y_2524_) == 2)
{
lean_object* v_config_2532_; lean_object* v_extensions_2533_; lean_object* v_extraInj_2534_; lean_object* v_extraFacts_2535_; lean_object* v_symPrios_2536_; lean_object* v_norm_2537_; lean_object* v_normProcs_2538_; lean_object* v_anchorRefs_x3f_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2594_; 
v_config_2532_ = lean_ctor_get(v_params_2377_, 0);
v_extensions_2533_ = lean_ctor_get(v_params_2377_, 1);
v_extraInj_2534_ = lean_ctor_get(v_params_2377_, 3);
v_extraFacts_2535_ = lean_ctor_get(v_params_2377_, 4);
v_symPrios_2536_ = lean_ctor_get(v_params_2377_, 5);
v_norm_2537_ = lean_ctor_get(v_params_2377_, 6);
v_normProcs_2538_ = lean_ctor_get(v_params_2377_, 7);
v_anchorRefs_x3f_2539_ = lean_ctor_get(v_params_2377_, 8);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_params_2377_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v_params_2377_, 2);
lean_dec(v_unused_2595_);
v___x_2541_ = v_params_2377_;
v_isShared_2542_ = v_isSharedCheck_2594_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_anchorRefs_x3f_2539_);
lean_inc(v_normProcs_2538_);
lean_inc(v_norm_2537_);
lean_inc(v_symPrios_2536_);
lean_inc(v_extraFacts_2535_);
lean_inc(v_extraInj_2534_);
lean_inc(v_extensions_2533_);
lean_inc(v_config_2532_);
lean_dec(v_params_2377_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2594_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v_size_2543_; uint8_t v_gen_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2593_; 
v_size_2543_ = lean_ctor_get(v_extra_2531_, 2);
v_gen_2544_ = lean_ctor_get_uint8(v___y_2524_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___y_2524_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2546_ = v___y_2524_;
v_isShared_2547_ = v_isSharedCheck_2593_;
goto v_resetjp_2545_;
}
else
{
lean_dec(v___y_2524_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2593_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; 
v___x_2548_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2381_, v___y_2528_, v___y_2521_, v___y_2520_, v___y_2529_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v___x_2550_; 
lean_dec_ref_known(v___x_2548_, 1);
if (v_isShared_2547_ == 0)
{
lean_ctor_set_tag(v___x_2546_, 0);
v___x_2550_ = v___x_2546_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2584_, 0, v_gen_2544_);
v___x_2550_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; 
lean_inc_ref(v___y_2523_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2520_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2528_);
lean_inc(v_size_2543_);
v___x_2551_ = lean_apply_7(v___y_2523_, v___x_2550_, v_size_2543_, v___y_2528_, v___y_2521_, v___y_2520_, v___y_2529_, lean_box(0));
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2551_, 1);
v___x_2553_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2553_, 0, v_gen_2544_);
lean_inc(v___y_2529_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2528_);
lean_inc(v_size_2543_);
v___x_2554_ = lean_apply_7(v___y_2523_, v___x_2553_, v_size_2543_, v___y_2528_, v___y_2521_, v___y_2520_, v___y_2529_, lean_box(0));
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2567_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2567_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2567_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2559_ = l_Lean_PersistentArray_push___redArg(v_extra_2531_, v_a_2552_);
v___x_2560_ = l_Lean_PersistentArray_push___redArg(v___x_2559_, v_a_2555_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 2, v___x_2560_);
v___x_2562_ = v___x_2541_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_config_2532_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_extensions_2533_);
lean_ctor_set(v_reuseFailAlloc_2566_, 2, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2566_, 3, v_extraInj_2534_);
lean_ctor_set(v_reuseFailAlloc_2566_, 4, v_extraFacts_2535_);
lean_ctor_set(v_reuseFailAlloc_2566_, 5, v_symPrios_2536_);
lean_ctor_set(v_reuseFailAlloc_2566_, 6, v_norm_2537_);
lean_ctor_set(v_reuseFailAlloc_2566_, 7, v_normProcs_2538_);
lean_ctor_set(v_reuseFailAlloc_2566_, 8, v_anchorRefs_x3f_2539_);
v___x_2562_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2564_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2562_);
v___x_2564_ = v___x_2557_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
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
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_a_2552_);
lean_del_object(v___x_2541_);
lean_dec(v_anchorRefs_x3f_2539_);
lean_dec_ref(v_normProcs_2538_);
lean_dec_ref(v_norm_2537_);
lean_dec_ref(v_symPrios_2536_);
lean_dec_ref(v_extraFacts_2535_);
lean_dec_ref(v_extraInj_2534_);
lean_dec_ref(v_extensions_2533_);
lean_dec_ref(v_config_2532_);
lean_dec_ref(v_extra_2531_);
v_a_2568_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2554_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2554_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_del_object(v___x_2541_);
lean_dec(v_anchorRefs_x3f_2539_);
lean_dec_ref(v_normProcs_2538_);
lean_dec_ref(v_norm_2537_);
lean_dec_ref(v_symPrios_2536_);
lean_dec_ref(v_extraFacts_2535_);
lean_dec_ref(v_extraInj_2534_);
lean_dec_ref(v_extensions_2533_);
lean_dec_ref(v_config_2532_);
lean_dec_ref(v_extra_2531_);
lean_dec_ref(v___y_2523_);
lean_dec_ref(v___y_2520_);
v_a_2576_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2551_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2551_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_del_object(v___x_2546_);
lean_del_object(v___x_2541_);
lean_dec(v_anchorRefs_x3f_2539_);
lean_dec_ref(v_normProcs_2538_);
lean_dec_ref(v_norm_2537_);
lean_dec_ref(v_symPrios_2536_);
lean_dec_ref(v_extraFacts_2535_);
lean_dec_ref(v_extraInj_2534_);
lean_dec_ref(v_extensions_2533_);
lean_dec_ref(v_config_2532_);
lean_dec_ref(v_extra_2531_);
lean_dec_ref(v___y_2523_);
lean_dec_ref(v___y_2520_);
v_a_2585_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2548_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2548_);
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
}
}
}
else
{
switch(lean_obj_tag(v___y_2524_))
{
case 0:
{
lean_object* v_config_2596_; lean_object* v_extensions_2597_; lean_object* v_extraInj_2598_; lean_object* v_extraFacts_2599_; lean_object* v_symPrios_2600_; lean_object* v_norm_2601_; lean_object* v_normProcs_2602_; lean_object* v_anchorRefs_x3f_2603_; lean_object* v_size_2604_; 
v_config_2596_ = lean_ctor_get(v_params_2377_, 0);
lean_inc_ref(v_config_2596_);
v_extensions_2597_ = lean_ctor_get(v_params_2377_, 1);
lean_inc_ref(v_extensions_2597_);
v_extraInj_2598_ = lean_ctor_get(v_params_2377_, 3);
lean_inc_ref(v_extraInj_2598_);
v_extraFacts_2599_ = lean_ctor_get(v_params_2377_, 4);
lean_inc_ref(v_extraFacts_2599_);
v_symPrios_2600_ = lean_ctor_get(v_params_2377_, 5);
lean_inc_ref(v_symPrios_2600_);
v_norm_2601_ = lean_ctor_get(v_params_2377_, 6);
lean_inc_ref(v_norm_2601_);
v_normProcs_2602_ = lean_ctor_get(v_params_2377_, 7);
lean_inc_ref(v_normProcs_2602_);
v_anchorRefs_x3f_2603_ = lean_ctor_get(v_params_2377_, 8);
lean_inc(v_anchorRefs_x3f_2603_);
lean_dec_ref(v_params_2377_);
v_size_2604_ = lean_ctor_get(v_extra_2531_, 2);
lean_inc(v_size_2604_);
v___y_2493_ = v_extra_2531_;
v___y_2494_ = v_extraInj_2598_;
v___y_2495_ = v_extensions_2597_;
v___y_2496_ = v___y_2524_;
v___y_2497_ = v___y_2528_;
v___y_2498_ = v_extraFacts_2599_;
v___y_2499_ = v_anchorRefs_x3f_2603_;
v___y_2500_ = v___y_2520_;
v___y_2501_ = v___y_2521_;
v___y_2502_ = v_symPrios_2600_;
v___y_2503_ = v_normProcs_2602_;
v___y_2504_ = v___y_2523_;
v___y_2505_ = v_size_2604_;
v___y_2506_ = v_config_2596_;
v___y_2507_ = v_norm_2601_;
v___y_2508_ = v___y_2529_;
goto v___jp_2492_;
}
case 1:
{
lean_object* v_config_2605_; lean_object* v_extensions_2606_; lean_object* v_extraInj_2607_; lean_object* v_extraFacts_2608_; lean_object* v_symPrios_2609_; lean_object* v_norm_2610_; lean_object* v_normProcs_2611_; lean_object* v_anchorRefs_x3f_2612_; lean_object* v_size_2613_; 
v_config_2605_ = lean_ctor_get(v_params_2377_, 0);
lean_inc_ref(v_config_2605_);
v_extensions_2606_ = lean_ctor_get(v_params_2377_, 1);
lean_inc_ref(v_extensions_2606_);
v_extraInj_2607_ = lean_ctor_get(v_params_2377_, 3);
lean_inc_ref(v_extraInj_2607_);
v_extraFacts_2608_ = lean_ctor_get(v_params_2377_, 4);
lean_inc_ref(v_extraFacts_2608_);
v_symPrios_2609_ = lean_ctor_get(v_params_2377_, 5);
lean_inc_ref(v_symPrios_2609_);
v_norm_2610_ = lean_ctor_get(v_params_2377_, 6);
lean_inc_ref(v_norm_2610_);
v_normProcs_2611_ = lean_ctor_get(v_params_2377_, 7);
lean_inc_ref(v_normProcs_2611_);
v_anchorRefs_x3f_2612_ = lean_ctor_get(v_params_2377_, 8);
lean_inc(v_anchorRefs_x3f_2612_);
lean_dec_ref(v_params_2377_);
v_size_2613_ = lean_ctor_get(v_extra_2531_, 2);
lean_inc(v_size_2613_);
v___y_2493_ = v_extra_2531_;
v___y_2494_ = v_extraInj_2607_;
v___y_2495_ = v_extensions_2606_;
v___y_2496_ = v___y_2524_;
v___y_2497_ = v___y_2528_;
v___y_2498_ = v_extraFacts_2608_;
v___y_2499_ = v_anchorRefs_x3f_2612_;
v___y_2500_ = v___y_2520_;
v___y_2501_ = v___y_2521_;
v___y_2502_ = v_symPrios_2609_;
v___y_2503_ = v_normProcs_2611_;
v___y_2504_ = v___y_2523_;
v___y_2505_ = v_size_2613_;
v___y_2506_ = v_config_2605_;
v___y_2507_ = v_norm_2610_;
v___y_2508_ = v___y_2529_;
goto v___jp_2492_;
}
default: 
{
lean_object* v_config_2614_; lean_object* v_extensions_2615_; lean_object* v_extraInj_2616_; lean_object* v_extraFacts_2617_; lean_object* v_symPrios_2618_; lean_object* v_norm_2619_; lean_object* v_normProcs_2620_; lean_object* v_anchorRefs_x3f_2621_; lean_object* v_size_2622_; 
v_config_2614_ = lean_ctor_get(v_params_2377_, 0);
lean_inc_ref(v_config_2614_);
v_extensions_2615_ = lean_ctor_get(v_params_2377_, 1);
lean_inc_ref(v_extensions_2615_);
v_extraInj_2616_ = lean_ctor_get(v_params_2377_, 3);
lean_inc_ref(v_extraInj_2616_);
v_extraFacts_2617_ = lean_ctor_get(v_params_2377_, 4);
lean_inc_ref(v_extraFacts_2617_);
v_symPrios_2618_ = lean_ctor_get(v_params_2377_, 5);
lean_inc_ref(v_symPrios_2618_);
v_norm_2619_ = lean_ctor_get(v_params_2377_, 6);
lean_inc_ref(v_norm_2619_);
v_normProcs_2620_ = lean_ctor_get(v_params_2377_, 7);
lean_inc_ref(v_normProcs_2620_);
v_anchorRefs_x3f_2621_ = lean_ctor_get(v_params_2377_, 8);
lean_inc(v_anchorRefs_x3f_2621_);
lean_dec_ref(v_params_2377_);
v_size_2622_ = lean_ctor_get(v_extra_2531_, 2);
lean_inc(v_size_2622_);
v___y_2457_ = v_symPrios_2618_;
v___y_2458_ = v_extra_2531_;
v___y_2459_ = v_extraInj_2616_;
v___y_2460_ = v_normProcs_2620_;
v___y_2461_ = v_extensions_2615_;
v___y_2462_ = v___y_2524_;
v___y_2463_ = v___y_2523_;
v___y_2464_ = v_size_2622_;
v___y_2465_ = v_norm_2619_;
v___y_2466_ = v_config_2614_;
v___y_2467_ = v_extraFacts_2617_;
v___y_2468_ = v_anchorRefs_x3f_2621_;
v___y_2469_ = v___y_2528_;
v___y_2470_ = v___y_2521_;
v___y_2471_ = v___y_2520_;
v___y_2472_ = v___y_2529_;
goto v___jp_2456_;
}
}
}
}
}
v___jp_2623_:
{
uint8_t v___x_2636_; 
v___x_2636_ = l_Lean_Expr_isForall(v___y_2628_);
if (v___x_2636_ == 0)
{
v___y_2519_ = v___y_2630_;
v___y_2520_ = v___y_2634_;
v___y_2521_ = v___y_2633_;
v___y_2522_ = v___y_2631_;
v___y_2523_ = v___y_2626_;
v___y_2524_ = v___y_2625_;
v___y_2525_ = v___y_2627_;
v___y_2526_ = v___y_2628_;
v___y_2527_ = v___y_2629_;
v___y_2528_ = v___y_2632_;
v___y_2529_ = v___y_2635_;
v___y_2530_ = v___x_2636_;
goto v___jp_2518_;
}
else
{
if (v___y_2624_ == 0)
{
v___y_2519_ = v___y_2630_;
v___y_2520_ = v___y_2634_;
v___y_2521_ = v___y_2633_;
v___y_2522_ = v___y_2631_;
v___y_2523_ = v___y_2626_;
v___y_2524_ = v___y_2625_;
v___y_2525_ = v___y_2627_;
v___y_2526_ = v___y_2628_;
v___y_2527_ = v___y_2629_;
v___y_2528_ = v___y_2632_;
v___y_2529_ = v___y_2635_;
v___y_2530_ = v___x_2636_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2637_ = lean_array_get_size(v___y_2629_);
v___x_2638_ = lean_unsigned_to_nat(0u);
v___x_2639_ = lean_nat_dec_eq(v___x_2637_, v___x_2638_);
if (v___x_2639_ == 0)
{
v___y_2519_ = v___y_2630_;
v___y_2520_ = v___y_2634_;
v___y_2521_ = v___y_2633_;
v___y_2522_ = v___y_2631_;
v___y_2523_ = v___y_2626_;
v___y_2524_ = v___y_2625_;
v___y_2525_ = v___y_2627_;
v___y_2526_ = v___y_2628_;
v___y_2527_ = v___y_2629_;
v___y_2528_ = v___y_2632_;
v___y_2529_ = v___y_2635_;
v___y_2530_ = v___x_2636_;
goto v___jp_2518_;
}
else
{
if (lean_obj_tag(v_mod_x3f_2379_) == 0)
{
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
v___y_2435_ = v___y_2634_;
v___y_2436_ = v___y_2630_;
v___y_2437_ = v___y_2633_;
v___y_2438_ = v___y_2631_;
v___y_2439_ = v___y_2629_;
v___y_2440_ = v___y_2628_;
v___y_2441_ = v___y_2627_;
v___y_2442_ = v___y_2632_;
v___y_2443_ = v___y_2635_;
goto v___jp_2434_;
}
else
{
v___y_2519_ = v___y_2630_;
v___y_2520_ = v___y_2634_;
v___y_2521_ = v___y_2633_;
v___y_2522_ = v___y_2631_;
v___y_2523_ = v___y_2626_;
v___y_2524_ = v___y_2625_;
v___y_2525_ = v___y_2627_;
v___y_2526_ = v___y_2628_;
v___y_2527_ = v___y_2629_;
v___y_2528_ = v___y_2632_;
v___y_2529_ = v___y_2635_;
v___y_2530_ = v___x_2636_;
goto v___jp_2518_;
}
}
}
}
}
v___jp_2640_:
{
lean_object* v___x_2648_; uint8_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___f_2651_; lean_object* v___x_2652_; 
v___x_2648_ = lean_box(0);
v___x_2649_ = 1;
v___x_2650_ = lean_box(v___x_2649_);
lean_inc(v_p_2378_);
v___f_2651_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2651_, 0, v_p_2378_);
lean_closure_set(v___f_2651_, 1, v_term_2380_);
lean_closure_set(v___f_2651_, 2, v___x_2648_);
lean_closure_set(v___f_2651_, 3, v___x_2650_);
v___x_2652_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2651_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2700_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2700_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2700_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
if (lean_obj_tag(v_a_2653_) == 1)
{
lean_object* v_val_2657_; lean_object* v_snd_2658_; lean_object* v_fst_2659_; lean_object* v_fst_2660_; lean_object* v_snd_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___f_2664_; lean_object* v___x_2665_; 
lean_del_object(v___x_2655_);
v_val_2657_ = lean_ctor_get(v_a_2653_, 0);
lean_inc(v_val_2657_);
lean_dec_ref_known(v_a_2653_, 1);
v_snd_2658_ = lean_ctor_get(v_val_2657_, 1);
lean_inc(v_snd_2658_);
v_fst_2659_ = lean_ctor_get(v_val_2657_, 0);
lean_inc_n(v_fst_2659_, 2);
lean_dec(v_val_2657_);
v_fst_2660_ = lean_ctor_get(v_snd_2658_, 0);
lean_inc_n(v_fst_2660_, 3);
v_snd_2661_ = lean_ctor_get(v_snd_2658_, 1);
lean_inc(v_snd_2661_);
lean_dec(v_snd_2658_);
v___x_2662_ = lean_box(v___x_2649_);
v___x_2663_ = lean_box(v_minIndexable_2381_);
lean_inc_ref(v_params_2377_);
v___f_2664_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed), 13, 6);
lean_closure_set(v___f_2664_, 0, v_params_2377_);
lean_closure_set(v___f_2664_, 1, v_p_2378_);
lean_closure_set(v___f_2664_, 2, v_fst_2659_);
lean_closure_set(v___f_2664_, 3, v_fst_2660_);
lean_closure_set(v___f_2664_, 4, v___x_2662_);
lean_closure_set(v___f_2664_, 5, v___x_2663_);
lean_inc(v___y_2647_);
lean_inc_ref(v___y_2646_);
lean_inc(v___y_2645_);
lean_inc_ref(v___y_2644_);
v___x_2665_ = lean_infer_type(v_fst_2660_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2667_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc_n(v_a_2666_, 2);
lean_dec_ref_known(v___x_2665_, 1);
v___x_2667_ = l_Lean_Meta_isProp(v_a_2666_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; uint8_t v___x_2669_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2667_, 1);
v___x_2669_ = lean_unbox(v_a_2668_);
lean_dec(v_a_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec(v_a_2666_);
lean_dec_ref(v___f_2664_);
lean_dec(v_snd_2661_);
lean_dec(v_fst_2660_);
lean_dec(v_fst_2659_);
lean_dec(v_kind_2641_);
lean_dec(v_mod_x3f_2379_);
lean_dec_ref(v_params_2377_);
v___x_2670_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2671_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2670_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec_ref(v___y_2646_);
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
else
{
uint8_t v___x_2680_; 
v___x_2680_ = lean_unbox(v_snd_2661_);
lean_dec(v_snd_2661_);
v___y_2624_ = v___x_2680_;
v___y_2625_ = v_kind_2641_;
v___y_2626_ = v___f_2664_;
v___y_2627_ = v_fst_2660_;
v___y_2628_ = v_a_2666_;
v___y_2629_ = v_fst_2659_;
v___y_2630_ = v___y_2642_;
v___y_2631_ = v___y_2643_;
v___y_2632_ = v___y_2644_;
v___y_2633_ = v___y_2645_;
v___y_2634_ = v___y_2646_;
v___y_2635_ = v___y_2647_;
goto v___jp_2623_;
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec(v_a_2666_);
lean_dec_ref(v___f_2664_);
lean_dec(v_snd_2661_);
lean_dec(v_fst_2660_);
lean_dec(v_fst_2659_);
lean_dec_ref(v___y_2646_);
lean_dec(v_kind_2641_);
lean_dec(v_mod_x3f_2379_);
lean_dec_ref(v_params_2377_);
v_a_2681_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2667_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2667_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec_ref(v___f_2664_);
lean_dec(v_snd_2661_);
lean_dec(v_fst_2660_);
lean_dec(v_fst_2659_);
lean_dec_ref(v___y_2646_);
lean_dec(v_kind_2641_);
lean_dec(v_mod_x3f_2379_);
lean_dec_ref(v_params_2377_);
v_a_2689_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2665_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2665_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
lean_object* v___x_2698_; 
lean_dec(v_a_2653_);
lean_dec_ref(v___y_2646_);
lean_dec(v_kind_2641_);
lean_dec(v_mod_x3f_2379_);
lean_dec(v_p_2378_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v_params_2377_);
v___x_2698_ = v___x_2655_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_params_2377_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec_ref(v___y_2646_);
lean_dec(v_kind_2641_);
lean_dec(v_mod_x3f_2379_);
lean_dec(v_p_2378_);
lean_dec_ref(v_params_2377_);
v_a_2701_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2652_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2652_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
v___jp_2709_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
v___x_2716_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2717_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2716_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec_ref(v___y_2714_);
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
v___jp_2726_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
v___x_2733_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2734_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2733_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec_ref(v___y_2731_);
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
v___jp_2743_:
{
lean_object* v___x_2750_; 
v___x_2750_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_kind_2641_ = v___x_2750_;
v___y_2642_ = v___y_2744_;
v___y_2643_ = v___y_2745_;
v___y_2644_ = v___y_2746_;
v___y_2645_ = v___y_2747_;
v___y_2646_ = v___y_2748_;
v___y_2647_ = v___y_2749_;
goto v___jp_2640_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_2377_ = stack[0].m_obj;
lean_object* v_p_2378_ = stack[1].m_obj;
lean_object* v_mod_x3f_2379_ = stack[2].m_obj;
lean_object* v_term_2380_ = stack[3].m_obj;
uint8_t v_minIndexable_2381_ = stack[4].m_num;
lean_object* v_a_2382_ = stack[5].m_obj;
lean_object* v_a_2383_ = stack[6].m_obj;
lean_object* v_a_2384_ = stack[7].m_obj;
lean_object* v_a_2385_ = stack[8].m_obj;
lean_object* v_a_2386_ = stack[9].m_obj;
lean_object* v_a_2387_ = stack[10].m_obj;
lean_object* v_res_2800_;
v_res_2800_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2377_, v_p_2378_, v_mod_x3f_2379_, v_term_2380_, v_minIndexable_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
stack->m_obj
 = v_res_2800_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2801_, lean_object* v_p_2802_, lean_object* v_mod_x3f_2803_, lean_object* v_term_2804_, lean_object* v_minIndexable_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
uint8_t v_minIndexable_boxed_2813_; lean_object* v_res_2814_; 
v_minIndexable_boxed_2813_ = lean_unbox(v_minIndexable_2805_);
v_res_2814_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2801_, v_p_2802_, v_mod_x3f_2803_, v_term_2804_, v_minIndexable_boxed_2813_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
return v_res_2814_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(uint8_t v___x_2815_, uint8_t v___x_2816_, lean_object* v_as_2817_, size_t v_i_2818_, size_t v_stop_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2815_, v___x_2816_, v_as_2817_, v_i_2818_, v_stop_2819_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2815_ = stack[0].m_num;
uint8_t v___x_2816_ = stack[1].m_num;
lean_object* v_as_2817_ = stack[2].m_obj;
size_t v_i_2818_ = stack[3].m_num;
size_t v_stop_2819_ = stack[4].m_num;
lean_object* v___y_2820_ = stack[5].m_obj;
lean_object* v___y_2821_ = stack[6].m_obj;
lean_object* v___y_2822_ = stack[7].m_obj;
lean_object* v___y_2823_ = stack[8].m_obj;
lean_object* v___y_2824_ = stack[9].m_obj;
lean_object* v___y_2825_ = stack[10].m_obj;
lean_object* v_res_2828_;
v_res_2828_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v___x_2815_, v___x_2816_, v_as_2817_, v_i_2818_, v_stop_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
stack->m_obj
 = v_res_2828_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v___x_2829_, lean_object* v___x_2830_, lean_object* v_as_2831_, lean_object* v_i_2832_, lean_object* v_stop_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
uint8_t v___x_16811__boxed_2841_; uint8_t v___x_16812__boxed_2842_; size_t v_i_boxed_2843_; size_t v_stop_boxed_2844_; lean_object* v_res_2845_; 
v___x_16811__boxed_2841_ = lean_unbox(v___x_2829_);
v___x_16812__boxed_2842_ = lean_unbox(v___x_2830_);
v_i_boxed_2843_ = lean_unbox_usize(v_i_2832_);
lean_dec(v_i_2832_);
v_stop_boxed_2844_ = lean_unbox_usize(v_stop_2833_);
lean_dec(v_stop_2833_);
v_res_2845_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v___x_16811__boxed_2841_, v___x_16812__boxed_2842_, v_as_2831_, v_i_boxed_2843_, v_stop_boxed_2844_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec_ref(v_as_2831_);
return v_res_2845_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(lean_object* v_00_u03b1_2846_, lean_object* v_msg_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
return v___x_2855_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2847_ = stack[1].m_obj;
lean_object* v___y_2848_ = stack[2].m_obj;
lean_object* v___y_2849_ = stack[3].m_obj;
lean_object* v___y_2850_ = stack[4].m_obj;
lean_object* v___y_2851_ = stack[5].m_obj;
lean_object* v___y_2852_ = stack[6].m_obj;
lean_object* v___y_2853_ = stack[7].m_obj;
lean_object* v_res_2856_;
v_res_2856_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(lean_box(0), v_msg_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
stack->m_obj
 = v_res_2856_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___boxed(lean_object* v_00_u03b1_2857_, lean_object* v_msg_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(v_00_u03b1_2857_, v_msg_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2866_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(lean_object* v_msgData_2867_, lean_object* v_macroStack_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2867_, v_macroStack_2868_, v___y_2873_);
return v___x_2876_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2867_ = stack[0].m_obj;
lean_object* v_macroStack_2868_ = stack[1].m_obj;
lean_object* v___y_2869_ = stack[2].m_obj;
lean_object* v___y_2870_ = stack[3].m_obj;
lean_object* v___y_2871_ = stack[4].m_obj;
lean_object* v___y_2872_ = stack[5].m_obj;
lean_object* v___y_2873_ = stack[6].m_obj;
lean_object* v___y_2874_ = stack[7].m_obj;
lean_object* v_res_2877_;
v_res_2877_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(v_msgData_2867_, v_macroStack_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
stack->m_obj
 = v_res_2877_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___boxed(lean_object* v_msgData_2878_, lean_object* v_macroStack_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(v_msgData_2878_, v_macroStack_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
return v_res_2887_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2888_, lean_object* v_val_2889_, lean_object* v___x_2890_, uint8_t v___y_2891_, lean_object* v_____r_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v___x_2900_; lean_object* v_ext_2901_; lean_object* v_toEnvExtension_2902_; lean_object* v_env_2903_; lean_object* v_config_2904_; lean_object* v_extensions_2905_; lean_object* v_extra_2906_; lean_object* v_extraInj_2907_; lean_object* v_extraFacts_2908_; lean_object* v_symPrios_2909_; lean_object* v_norm_2910_; lean_object* v_normProcs_2911_; lean_object* v_anchorRefs_x3f_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2924_; 
v___x_2900_ = lean_st_ref_get(v___y_2898_);
v_ext_2901_ = lean_ctor_get(v_val_2889_, 1);
v_toEnvExtension_2902_ = lean_ctor_get(v_ext_2901_, 0);
v_env_2903_ = lean_ctor_get(v___x_2900_, 0);
lean_inc_ref(v_env_2903_);
lean_dec(v___x_2900_);
v_config_2904_ = lean_ctor_get(v_params_2888_, 0);
v_extensions_2905_ = lean_ctor_get(v_params_2888_, 1);
v_extra_2906_ = lean_ctor_get(v_params_2888_, 2);
v_extraInj_2907_ = lean_ctor_get(v_params_2888_, 3);
v_extraFacts_2908_ = lean_ctor_get(v_params_2888_, 4);
v_symPrios_2909_ = lean_ctor_get(v_params_2888_, 5);
v_norm_2910_ = lean_ctor_get(v_params_2888_, 6);
v_normProcs_2911_ = lean_ctor_get(v_params_2888_, 7);
v_anchorRefs_x3f_2912_ = lean_ctor_get(v_params_2888_, 8);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_params_2888_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2914_ = v_params_2888_;
v_isShared_2915_ = v_isSharedCheck_2924_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_anchorRefs_x3f_2912_);
lean_inc(v_normProcs_2911_);
lean_inc(v_norm_2910_);
lean_inc(v_symPrios_2909_);
lean_inc(v_extraFacts_2908_);
lean_inc(v_extraInj_2907_);
lean_inc(v_extra_2906_);
lean_inc(v_extensions_2905_);
lean_inc(v_config_2904_);
lean_dec(v_params_2888_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2924_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v_asyncMode_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2920_; 
v_asyncMode_2916_ = lean_ctor_get(v_toEnvExtension_2902_, 2);
v___x_2917_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2890_, v_val_2889_, v_env_2903_, v_asyncMode_2916_, v___y_2891_);
v___x_2918_ = lean_array_push(v_extensions_2905_, v___x_2917_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 1, v___x_2918_);
v___x_2920_ = v___x_2914_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_config_2904_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_2923_, 2, v_extra_2906_);
lean_ctor_set(v_reuseFailAlloc_2923_, 3, v_extraInj_2907_);
lean_ctor_set(v_reuseFailAlloc_2923_, 4, v_extraFacts_2908_);
lean_ctor_set(v_reuseFailAlloc_2923_, 5, v_symPrios_2909_);
lean_ctor_set(v_reuseFailAlloc_2923_, 6, v_norm_2910_);
lean_ctor_set(v_reuseFailAlloc_2923_, 7, v_normProcs_2911_);
lean_ctor_set(v_reuseFailAlloc_2923_, 8, v_anchorRefs_x3f_2912_);
v___x_2920_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
return v___x_2922_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_2888_ = stack[0].m_obj;
lean_object* v_val_2889_ = stack[1].m_obj;
lean_object* v___x_2890_ = stack[2].m_obj;
uint8_t v___y_2891_ = stack[3].m_num;
lean_object* v_____r_2892_ = stack[4].m_obj;
lean_object* v___y_2893_ = stack[5].m_obj;
lean_object* v___y_2894_ = stack[6].m_obj;
lean_object* v___y_2895_ = stack[7].m_obj;
lean_object* v___y_2896_ = stack[8].m_obj;
lean_object* v___y_2897_ = stack[9].m_obj;
lean_object* v___y_2898_ = stack[10].m_obj;
lean_object* v_res_2925_;
v_res_2925_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2888_, v_val_2889_, v___x_2890_, v___y_2891_, v_____r_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
stack->m_obj
 = v_res_2925_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2926_, lean_object* v_val_2927_, lean_object* v___x_2928_, lean_object* v___y_2929_, lean_object* v_____r_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
uint8_t v___y_30061__boxed_2938_; lean_object* v_res_2939_; 
v___y_30061__boxed_2938_ = lean_unbox(v___y_2929_);
v_res_2939_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2926_, v_val_2927_, v___x_2928_, v___y_30061__boxed_2938_, v_____r_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v_val_2927_);
return v_res_2939_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2940_, lean_object* v_id_2941_, uint8_t v_minIndexable_2942_, lean_object* v_as_x27_2943_, lean_object* v_b_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
if (lean_obj_tag(v_as_x27_2943_) == 0)
{
lean_object* v___x_2950_; 
lean_dec(v_id_2941_);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_b_2944_);
return v___x_2950_;
}
else
{
lean_object* v_head_2951_; lean_object* v_tail_2952_; lean_object* v_toCold_2953_; lean_object* v_currRecDepth_2954_; lean_object* v_ref_2955_; uint16_t v_optionFlags_2956_; uint8_t v_suppressElabErrors_2957_; uint8_t v_isRecordingDeps_2958_; uint8_t v___x_2959_; lean_object* v___x_2960_; lean_object* v_ref_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v_head_2951_ = lean_ctor_get(v_as_x27_2943_, 0);
v_tail_2952_ = lean_ctor_get(v_as_x27_2943_, 1);
v_toCold_2953_ = lean_ctor_get(v___y_2947_, 0);
v_currRecDepth_2954_ = lean_ctor_get(v___y_2947_, 1);
v_ref_2955_ = lean_ctor_get(v___y_2947_, 2);
v_optionFlags_2956_ = lean_ctor_get_uint16(v___y_2947_, sizeof(void*)*3);
v_suppressElabErrors_2957_ = lean_ctor_get_uint8(v___y_2947_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2958_ = lean_ctor_get_uint8(v___y_2947_, sizeof(void*)*3 + 3);
v___x_2959_ = 0;
v___x_2960_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_ref_2961_ = l_Lean_replaceRef(v_p_2940_, v_ref_2955_);
lean_inc(v_currRecDepth_2954_);
lean_inc_ref(v_toCold_2953_);
v___x_2962_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2962_, 0, v_toCold_2953_);
lean_ctor_set(v___x_2962_, 1, v_currRecDepth_2954_);
lean_ctor_set(v___x_2962_, 2, v_ref_2961_);
lean_ctor_set_uint16(v___x_2962_, sizeof(void*)*3, v_optionFlags_2956_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*3 + 2, v_suppressElabErrors_2957_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*3 + 3, v_isRecordingDeps_2958_);
lean_inc(v_head_2951_);
lean_inc(v_id_2941_);
v___x_2963_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2944_, v_id_2941_, v_head_2951_, v___x_2960_, v_minIndexable_2942_, v___x_2959_, v___x_2959_, v___y_2945_, v___y_2946_, v___x_2962_, v___y_2948_);
lean_dec_ref_known(v___x_2962_, 3);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v_as_x27_2943_ = v_tail_2952_;
v_b_2944_ = v_a_2964_;
goto _start;
}
else
{
lean_dec(v_id_2941_);
return v___x_2963_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2940_ = stack[0].m_obj;
lean_object* v_id_2941_ = stack[1].m_obj;
uint8_t v_minIndexable_2942_ = stack[2].m_num;
lean_object* v_as_x27_2943_ = stack[3].m_obj;
lean_object* v_b_2944_ = stack[4].m_obj;
lean_object* v___y_2945_ = stack[5].m_obj;
lean_object* v___y_2946_ = stack[6].m_obj;
lean_object* v___y_2947_ = stack[7].m_obj;
lean_object* v___y_2948_ = stack[8].m_obj;
lean_object* v_res_2966_;
v_res_2966_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_2940_, v_id_2941_, v_minIndexable_2942_, v_as_x27_2943_, v_b_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
stack->m_obj
 = v_res_2966_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_2967_, lean_object* v_id_2968_, lean_object* v_minIndexable_2969_, lean_object* v_as_x27_2970_, lean_object* v_b_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
uint8_t v_minIndexable_boxed_2977_; lean_object* v_res_2978_; 
v_minIndexable_boxed_2977_ = lean_unbox(v_minIndexable_2969_);
v_res_2978_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_2967_, v_id_2968_, v_minIndexable_boxed_2977_, v_as_x27_2970_, v_b_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v_as_x27_2970_);
lean_dec(v_p_2967_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_){
_start:
{
if (lean_obj_tag(v_a_2980_) == 0)
{
lean_object* v___x_2982_; 
v___x_2982_ = l_List_reverse___redArg(v_a_2981_);
return v___x_2982_;
}
else
{
lean_object* v_head_2983_; lean_object* v_tail_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2995_; 
v_head_2983_ = lean_ctor_get(v_a_2980_, 0);
v_tail_2984_ = lean_ctor_get(v_a_2980_, 1);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_a_2980_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2986_ = v_a_2980_;
v_isShared_2987_ = v_isSharedCheck_2995_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_tail_2984_);
lean_inc(v_head_2983_);
lean_dec(v_a_2980_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2995_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v_kind_2988_; uint8_t v___x_2989_; 
v_kind_2988_ = lean_ctor_get(v_head_2983_, 6);
v___x_2989_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_2988_, v_k_2979_);
if (v___x_2989_ == 0)
{
lean_del_object(v___x_2986_);
lean_dec(v_head_2983_);
v_a_2980_ = v_tail_2984_;
goto _start;
}
else
{
lean_object* v___x_2992_; 
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 1, v_a_2981_);
v___x_2992_ = v___x_2986_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_head_2983_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_a_2981_);
v___x_2992_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
v_a_2980_ = v_tail_2984_;
v_a_2981_ = v___x_2992_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_2996_, v_a_2997_, v_a_2998_);
lean_dec(v_k_2996_);
return v_res_2999_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_3000_, lean_object* v_msg_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v_toCold_3009_; lean_object* v_currRecDepth_3010_; lean_object* v_ref_3011_; uint16_t v_optionFlags_3012_; uint8_t v_suppressElabErrors_3013_; uint8_t v_isRecordingDeps_3014_; lean_object* v_ref_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_toCold_3009_ = lean_ctor_get(v___y_3006_, 0);
v_currRecDepth_3010_ = lean_ctor_get(v___y_3006_, 1);
v_ref_3011_ = lean_ctor_get(v___y_3006_, 2);
v_optionFlags_3012_ = lean_ctor_get_uint16(v___y_3006_, sizeof(void*)*3);
v_suppressElabErrors_3013_ = lean_ctor_get_uint8(v___y_3006_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3014_ = lean_ctor_get_uint8(v___y_3006_, sizeof(void*)*3 + 3);
v_ref_3015_ = l_Lean_replaceRef(v_ref_3000_, v_ref_3011_);
lean_inc(v_currRecDepth_3010_);
lean_inc_ref(v_toCold_3009_);
v___x_3016_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3016_, 0, v_toCold_3009_);
lean_ctor_set(v___x_3016_, 1, v_currRecDepth_3010_);
lean_ctor_set(v___x_3016_, 2, v_ref_3015_);
lean_ctor_set_uint16(v___x_3016_, sizeof(void*)*3, v_optionFlags_3012_);
lean_ctor_set_uint8(v___x_3016_, sizeof(void*)*3 + 2, v_suppressElabErrors_3013_);
lean_ctor_set_uint8(v___x_3016_, sizeof(void*)*3 + 3, v_isRecordingDeps_3014_);
v___x_3017_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___x_3016_, v___y_3007_);
lean_dec_ref_known(v___x_3016_, 3);
return v___x_3017_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3000_ = stack[0].m_obj;
lean_object* v_msg_3001_ = stack[1].m_obj;
lean_object* v___y_3002_ = stack[2].m_obj;
lean_object* v___y_3003_ = stack[3].m_obj;
lean_object* v___y_3004_ = stack[4].m_obj;
lean_object* v___y_3005_ = stack[5].m_obj;
lean_object* v___y_3006_ = stack[6].m_obj;
lean_object* v___y_3007_ = stack[7].m_obj;
lean_object* v_res_3018_;
v_res_3018_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_3000_, v_msg_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
stack->m_obj
 = v_res_3018_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_3019_, lean_object* v_msg_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_3019_, v_msg_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v_ref_3019_);
return v_res_3028_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_3029_, lean_object* v_id_3030_, uint8_t v_minIndexable_3031_, lean_object* v_as_x27_3032_, lean_object* v_b_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
if (lean_obj_tag(v_as_x27_3032_) == 0)
{
lean_object* v___x_3039_; 
lean_dec(v_id_3030_);
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_b_3033_);
return v___x_3039_;
}
else
{
lean_object* v_head_3040_; lean_object* v_tail_3041_; lean_object* v_toCold_3042_; lean_object* v_currRecDepth_3043_; lean_object* v_ref_3044_; uint16_t v_optionFlags_3045_; uint8_t v_suppressElabErrors_3046_; uint8_t v_isRecordingDeps_3047_; uint8_t v___x_3048_; uint8_t v___x_3049_; lean_object* v___x_3050_; lean_object* v_ref_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_head_3040_ = lean_ctor_get(v_as_x27_3032_, 0);
v_tail_3041_ = lean_ctor_get(v_as_x27_3032_, 1);
v_toCold_3042_ = lean_ctor_get(v___y_3036_, 0);
v_currRecDepth_3043_ = lean_ctor_get(v___y_3036_, 1);
v_ref_3044_ = lean_ctor_get(v___y_3036_, 2);
v_optionFlags_3045_ = lean_ctor_get_uint16(v___y_3036_, sizeof(void*)*3);
v_suppressElabErrors_3046_ = lean_ctor_get_uint8(v___y_3036_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3047_ = lean_ctor_get_uint8(v___y_3036_, sizeof(void*)*3 + 3);
v___x_3048_ = 0;
v___x_3049_ = 1;
v___x_3050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_ref_3051_ = l_Lean_replaceRef(v_p_3029_, v_ref_3044_);
lean_inc(v_currRecDepth_3043_);
lean_inc_ref(v_toCold_3042_);
v___x_3052_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3052_, 0, v_toCold_3042_);
lean_ctor_set(v___x_3052_, 1, v_currRecDepth_3043_);
lean_ctor_set(v___x_3052_, 2, v_ref_3051_);
lean_ctor_set_uint16(v___x_3052_, sizeof(void*)*3, v_optionFlags_3045_);
lean_ctor_set_uint8(v___x_3052_, sizeof(void*)*3 + 2, v_suppressElabErrors_3046_);
lean_ctor_set_uint8(v___x_3052_, sizeof(void*)*3 + 3, v_isRecordingDeps_3047_);
lean_inc(v_head_3040_);
lean_inc(v_id_3030_);
v___x_3053_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_3033_, v_id_3030_, v_head_3040_, v___x_3050_, v_minIndexable_3031_, v___x_3048_, v___x_3049_, v___y_3034_, v___y_3035_, v___x_3052_, v___y_3037_);
lean_dec_ref_known(v___x_3052_, 3);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3053_, 1);
v_as_x27_3032_ = v_tail_3041_;
v_b_3033_ = v_a_3054_;
goto _start;
}
else
{
lean_dec(v_id_3030_);
return v___x_3053_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3029_ = stack[0].m_obj;
lean_object* v_id_3030_ = stack[1].m_obj;
uint8_t v_minIndexable_3031_ = stack[2].m_num;
lean_object* v_as_x27_3032_ = stack[3].m_obj;
lean_object* v_b_3033_ = stack[4].m_obj;
lean_object* v___y_3034_ = stack[5].m_obj;
lean_object* v___y_3035_ = stack[6].m_obj;
lean_object* v___y_3036_ = stack[7].m_obj;
lean_object* v___y_3037_ = stack[8].m_obj;
lean_object* v_res_3056_;
v_res_3056_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3029_, v_id_3030_, v_minIndexable_3031_, v_as_x27_3032_, v_b_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
stack->m_obj
 = v_res_3056_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_3057_, lean_object* v_id_3058_, lean_object* v_minIndexable_3059_, lean_object* v_as_x27_3060_, lean_object* v_b_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
uint8_t v_minIndexable_boxed_3067_; lean_object* v_res_3068_; 
v_minIndexable_boxed_3067_ = lean_unbox(v_minIndexable_3059_);
v_res_3068_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3057_, v_id_3058_, v_minIndexable_boxed_3067_, v_as_x27_3060_, v_b_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v_as_x27_3060_);
lean_dec(v_p_3057_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_3069_){
_start:
{
if (lean_obj_tag(v_x_3069_) == 0)
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_box(0);
return v___x_3070_;
}
else
{
lean_object* v_head_3071_; lean_object* v_tail_3072_; lean_object* v_fst_3073_; uint8_t v___x_3074_; 
v_head_3071_ = lean_ctor_get(v_x_3069_, 0);
v_tail_3072_ = lean_ctor_get(v_x_3069_, 1);
v_fst_3073_ = lean_ctor_get(v_head_3071_, 0);
v___x_3074_ = l_Lean_isPrivateName(v_fst_3073_);
if (v___x_3074_ == 0)
{
v_x_3069_ = v_tail_3072_;
goto _start;
}
else
{
lean_object* v___x_3076_; 
lean_inc(v_head_3071_);
v___x_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_head_3071_);
return v___x_3076_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_3077_);
lean_dec(v_x_3077_);
return v_res_3078_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_3079_, lean_object* v_msgData_3080_, uint8_t v_severity_3081_, uint8_t v_isSilent_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; uint8_t v___y_3094_; uint8_t v___y_3095_; lean_object* v_toCold_3096_; lean_object* v___y_3097_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; uint8_t v___y_3129_; lean_object* v___y_3130_; uint8_t v___y_3131_; uint8_t v___y_3132_; lean_object* v___y_3133_; uint8_t v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; uint8_t v___y_3157_; uint8_t v___y_3158_; lean_object* v___y_3159_; uint8_t v___y_3163_; uint8_t v___y_3164_; uint8_t v___y_3165_; uint8_t v___x_3176_; uint8_t v___y_3178_; uint8_t v___y_3179_; uint8_t v___y_3180_; uint8_t v___y_3182_; uint8_t v___x_3190_; 
v___x_3176_ = 2;
v___x_3190_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3081_, v___x_3176_);
if (v___x_3190_ == 0)
{
v___y_3182_ = v___x_3190_;
goto v___jp_3181_;
}
else
{
uint8_t v___x_3191_; 
lean_inc_ref(v_msgData_3080_);
v___x_3191_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3080_);
v___y_3182_ = v___x_3191_;
goto v___jp_3181_;
}
v___jp_3088_:
{
lean_object* v_currNamespace_3098_; lean_object* v_openDecls_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v_env_3104_; lean_object* v_nextMacroScope_3105_; lean_object* v_ngen_3106_; lean_object* v_auxDeclNGen_3107_; lean_object* v_traceState_3108_; lean_object* v_cache_3109_; lean_object* v_recordedDeps_3110_; lean_object* v_messages_3111_; lean_object* v_infoState_3112_; lean_object* v_snapshotTasks_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3124_; 
v_currNamespace_3098_ = lean_ctor_get(v_toCold_3096_, 4);
v_openDecls_3099_ = lean_ctor_get(v_toCold_3096_, 5);
lean_inc(v_openDecls_3099_);
lean_inc(v_currNamespace_3098_);
v___x_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3100_, 0, v_currNamespace_3098_);
lean_ctor_set(v___x_3100_, 1, v_openDecls_3099_);
v___x_3101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
lean_ctor_set(v___x_3101_, 1, v___y_3092_);
lean_inc_ref(v___y_3093_);
lean_inc_ref(v___y_3090_);
v___x_3102_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3102_, 0, v___y_3090_);
lean_ctor_set(v___x_3102_, 1, v___y_3091_);
lean_ctor_set(v___x_3102_, 2, v___y_3089_);
lean_ctor_set(v___x_3102_, 3, v___y_3093_);
lean_ctor_set(v___x_3102_, 4, v___x_3101_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*5, v___y_3095_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*5 + 1, v___y_3094_);
lean_ctor_set_uint8(v___x_3102_, sizeof(void*)*5 + 2, v_isSilent_3082_);
v___x_3103_ = lean_st_ref_take(v___y_3097_);
v_env_3104_ = lean_ctor_get(v___x_3103_, 0);
v_nextMacroScope_3105_ = lean_ctor_get(v___x_3103_, 1);
v_ngen_3106_ = lean_ctor_get(v___x_3103_, 2);
v_auxDeclNGen_3107_ = lean_ctor_get(v___x_3103_, 3);
v_traceState_3108_ = lean_ctor_get(v___x_3103_, 4);
v_cache_3109_ = lean_ctor_get(v___x_3103_, 5);
v_recordedDeps_3110_ = lean_ctor_get(v___x_3103_, 6);
v_messages_3111_ = lean_ctor_get(v___x_3103_, 7);
v_infoState_3112_ = lean_ctor_get(v___x_3103_, 8);
v_snapshotTasks_3113_ = lean_ctor_get(v___x_3103_, 9);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3115_ = v___x_3103_;
v_isShared_3116_ = v_isSharedCheck_3124_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_snapshotTasks_3113_);
lean_inc(v_infoState_3112_);
lean_inc(v_messages_3111_);
lean_inc(v_recordedDeps_3110_);
lean_inc(v_cache_3109_);
lean_inc(v_traceState_3108_);
lean_inc(v_auxDeclNGen_3107_);
lean_inc(v_ngen_3106_);
lean_inc(v_nextMacroScope_3105_);
lean_inc(v_env_3104_);
lean_dec(v___x_3103_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3124_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3117_ = lean_box(0);
v___x_3118_ = l_Lean_MessageLog_add(v___x_3102_, v_messages_3111_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 7, v___x_3118_);
v___x_3120_ = v___x_3115_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_env_3104_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_nextMacroScope_3105_);
lean_ctor_set(v_reuseFailAlloc_3123_, 2, v_ngen_3106_);
lean_ctor_set(v_reuseFailAlloc_3123_, 3, v_auxDeclNGen_3107_);
lean_ctor_set(v_reuseFailAlloc_3123_, 4, v_traceState_3108_);
lean_ctor_set(v_reuseFailAlloc_3123_, 5, v_cache_3109_);
lean_ctor_set(v_reuseFailAlloc_3123_, 6, v_recordedDeps_3110_);
lean_ctor_set(v_reuseFailAlloc_3123_, 7, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3123_, 8, v_infoState_3112_);
lean_ctor_set(v_reuseFailAlloc_3123_, 9, v_snapshotTasks_3113_);
v___x_3120_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = lean_st_ref_put(v___y_3097_, v___x_3120_);
v___x_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3117_);
return v___x_3122_;
}
}
}
v___jp_3125_:
{
lean_object* v_fileName_3134_; lean_object* v_fileMap_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3151_; 
v_fileName_3134_ = lean_ctor_get(v___y_3130_, 0);
v_fileMap_3135_ = lean_ctor_get(v___y_3130_, 1);
v___x_3136_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3080_);
v___x_3137_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_3136_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3151_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3151_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
lean_inc_ref_n(v_fileMap_3135_, 2);
v___x_3142_ = l_Lean_FileMap_toPosition(v_fileMap_3135_, v___y_3128_);
lean_dec(v___y_3128_);
v___x_3143_ = l_Lean_FileMap_toPosition(v_fileMap_3135_, v___y_3133_);
lean_dec(v___y_3133_);
v___x_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
v___x_3145_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_3129_ == 0)
{
lean_del_object(v___x_3140_);
lean_dec_ref(v___y_3127_);
v___y_3089_ = v___x_3144_;
v___y_3090_ = v_fileName_3134_;
v___y_3091_ = v___x_3142_;
v___y_3092_ = v_a_3138_;
v___y_3093_ = v___x_3145_;
v___y_3094_ = v___y_3132_;
v___y_3095_ = v___y_3131_;
v_toCold_3096_ = v___y_3126_;
v___y_3097_ = v___y_3086_;
goto v___jp_3088_;
}
else
{
uint8_t v___x_3146_; 
lean_inc(v_a_3138_);
v___x_3146_ = l_Lean_MessageData_hasTag(v___y_3127_, v_a_3138_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; lean_object* v___x_3149_; 
lean_dec_ref_known(v___x_3144_, 1);
lean_dec_ref(v___x_3142_);
lean_dec(v_a_3138_);
v___x_3147_ = lean_box(0);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v___x_3147_);
v___x_3149_ = v___x_3140_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
else
{
lean_del_object(v___x_3140_);
v___y_3089_ = v___x_3144_;
v___y_3090_ = v_fileName_3134_;
v___y_3091_ = v___x_3142_;
v___y_3092_ = v_a_3138_;
v___y_3093_ = v___x_3145_;
v___y_3094_ = v___y_3132_;
v___y_3095_ = v___y_3131_;
v_toCold_3096_ = v___y_3126_;
v___y_3097_ = v___y_3086_;
goto v___jp_3088_;
}
}
}
}
v___jp_3152_:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_Lean_Syntax_getTailPos_x3f(v___y_3156_, v___y_3158_);
lean_dec(v___y_3156_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_inc(v___y_3159_);
v___y_3126_ = v___y_3154_;
v___y_3127_ = v___y_3155_;
v___y_3128_ = v___y_3159_;
v___y_3129_ = v___y_3153_;
v___y_3130_ = v___y_3154_;
v___y_3131_ = v___y_3158_;
v___y_3132_ = v___y_3157_;
v___y_3133_ = v___y_3159_;
goto v___jp_3125_;
}
else
{
lean_object* v_val_3161_; 
v_val_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_val_3161_);
lean_dec_ref_known(v___x_3160_, 1);
v___y_3126_ = v___y_3154_;
v___y_3127_ = v___y_3155_;
v___y_3128_ = v___y_3159_;
v___y_3129_ = v___y_3153_;
v___y_3130_ = v___y_3154_;
v___y_3131_ = v___y_3158_;
v___y_3132_ = v___y_3157_;
v___y_3133_ = v_val_3161_;
goto v___jp_3125_;
}
}
v___jp_3162_:
{
lean_object* v_toCold_3166_; lean_object* v_ref_3167_; uint8_t v_suppressElabErrors_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___f_3171_; lean_object* v_ref_3172_; lean_object* v___x_3173_; 
v_toCold_3166_ = lean_ctor_get(v___y_3085_, 0);
v_ref_3167_ = lean_ctor_get(v___y_3085_, 2);
v_suppressElabErrors_3168_ = lean_ctor_get_uint8(v___y_3085_, sizeof(void*)*3 + 2);
v___x_3169_ = lean_box(v_suppressElabErrors_3168_);
v___x_3170_ = lean_box(v___y_3163_);
v___f_3171_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3171_, 0, v___x_3169_);
lean_closure_set(v___f_3171_, 1, v___x_3170_);
v_ref_3172_ = l_Lean_replaceRef(v_ref_3079_, v_ref_3167_);
v___x_3173_ = l_Lean_Syntax_getPos_x3f(v_ref_3172_, v___y_3164_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v___x_3174_; 
v___x_3174_ = lean_unsigned_to_nat(0u);
v___y_3153_ = v_suppressElabErrors_3168_;
v___y_3154_ = v_toCold_3166_;
v___y_3155_ = v___f_3171_;
v___y_3156_ = v_ref_3172_;
v___y_3157_ = v___y_3165_;
v___y_3158_ = v___y_3164_;
v___y_3159_ = v___x_3174_;
goto v___jp_3152_;
}
else
{
lean_object* v_val_3175_; 
v_val_3175_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_val_3175_);
lean_dec_ref_known(v___x_3173_, 1);
v___y_3153_ = v_suppressElabErrors_3168_;
v___y_3154_ = v_toCold_3166_;
v___y_3155_ = v___f_3171_;
v___y_3156_ = v_ref_3172_;
v___y_3157_ = v___y_3165_;
v___y_3158_ = v___y_3164_;
v___y_3159_ = v_val_3175_;
goto v___jp_3152_;
}
}
v___jp_3177_:
{
if (v___y_3180_ == 0)
{
v___y_3163_ = v___y_3178_;
v___y_3164_ = v___y_3179_;
v___y_3165_ = v_severity_3081_;
goto v___jp_3162_;
}
else
{
v___y_3163_ = v___y_3178_;
v___y_3164_ = v___y_3179_;
v___y_3165_ = v___x_3176_;
goto v___jp_3162_;
}
}
v___jp_3181_:
{
if (v___y_3182_ == 0)
{
uint8_t v___x_3183_; uint8_t v___x_3184_; 
v___x_3183_ = 1;
v___x_3184_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3081_, v___x_3183_);
if (v___x_3184_ == 0)
{
v___y_3178_ = v___y_3182_;
v___y_3179_ = v___y_3182_;
v___y_3180_ = v___x_3184_;
goto v___jp_3177_;
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3186_; uint8_t v___x_3187_; 
v___x_3185_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3085_);
v___x_3186_ = l_Lean_warningAsError;
v___x_3187_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3185_, v___x_3186_);
lean_dec_ref(v___x_3185_);
v___y_3178_ = v___y_3182_;
v___y_3179_ = v___y_3182_;
v___y_3180_ = v___x_3187_;
goto v___jp_3177_;
}
}
else
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
lean_dec_ref(v_msgData_3080_);
v___x_3188_ = lean_box(0);
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
return v___x_3189_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3079_ = stack[0].m_obj;
lean_object* v_msgData_3080_ = stack[1].m_obj;
uint8_t v_severity_3081_ = stack[2].m_num;
uint8_t v_isSilent_3082_ = stack[3].m_num;
lean_object* v___y_3083_ = stack[4].m_obj;
lean_object* v___y_3084_ = stack[5].m_obj;
lean_object* v___y_3085_ = stack[6].m_obj;
lean_object* v___y_3086_ = stack[7].m_obj;
lean_object* v_res_3192_;
v_res_3192_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3079_, v_msgData_3080_, v_severity_3081_, v_isSilent_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
stack->m_obj
 = v_res_3192_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_3193_, lean_object* v_msgData_3194_, lean_object* v_severity_3195_, lean_object* v_isSilent_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
uint8_t v_severity_boxed_3202_; uint8_t v_isSilent_boxed_3203_; lean_object* v_res_3204_; 
v_severity_boxed_3202_ = lean_unbox(v_severity_3195_);
v_isSilent_boxed_3203_ = lean_unbox(v_isSilent_3196_);
v_res_3204_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3193_, v_msgData_3194_, v_severity_boxed_3202_, v_isSilent_boxed_3203_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v_ref_3193_);
return v_res_3204_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_3205_, uint8_t v_severity_3206_, uint8_t v_isSilent_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_ref_3215_; lean_object* v___x_3216_; 
v_ref_3215_ = lean_ctor_get(v___y_3212_, 2);
v___x_3216_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3215_, v_msgData_3205_, v_severity_3206_, v_isSilent_3207_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
return v___x_3216_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3205_ = stack[0].m_obj;
uint8_t v_severity_3206_ = stack[1].m_num;
uint8_t v_isSilent_3207_ = stack[2].m_num;
lean_object* v___y_3208_ = stack[3].m_obj;
lean_object* v___y_3209_ = stack[4].m_obj;
lean_object* v___y_3210_ = stack[5].m_obj;
lean_object* v___y_3211_ = stack[6].m_obj;
lean_object* v___y_3212_ = stack[7].m_obj;
lean_object* v___y_3213_ = stack[8].m_obj;
lean_object* v_res_3217_;
v_res_3217_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3205_, v_severity_3206_, v_isSilent_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
stack->m_obj
 = v_res_3217_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_3218_, lean_object* v_severity_3219_, lean_object* v_isSilent_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
uint8_t v_severity_boxed_3228_; uint8_t v_isSilent_boxed_3229_; lean_object* v_res_3230_; 
v_severity_boxed_3228_ = lean_unbox(v_severity_3219_);
v_isSilent_boxed_3229_ = lean_unbox(v_isSilent_3220_);
v_res_3230_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3218_, v_severity_boxed_3228_, v_isSilent_boxed_3229_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
return v_res_3230_;
}
}
lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v___x_3239_; uint8_t v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = 1;
v___x_3240_ = 0;
v___x_3241_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3231_, v___x_3239_, v___x_3240_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3241_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3231_ = stack[0].m_obj;
lean_object* v___y_3232_ = stack[1].m_obj;
lean_object* v___y_3233_ = stack[2].m_obj;
lean_object* v___y_3234_ = stack[3].m_obj;
lean_object* v___y_3235_ = stack[4].m_obj;
lean_object* v___y_3236_ = stack[5].m_obj;
lean_object* v___y_3237_ = stack[6].m_obj;
lean_object* v_res_3242_;
v_res_3242_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
stack->m_obj
 = v_res_3242_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
return v_res_3251_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v___x_3255_; uint8_t v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3255_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3253_);
v___x_3256_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3255_, v_opt_3252_);
lean_dec_ref(v___x_3255_);
v___x_3257_ = lean_box(v___x_3256_);
v___x_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_3252_ = stack[0].m_obj;
lean_object* v___y_3253_ = stack[1].m_obj;
lean_object* v_res_3259_;
v_res_3259_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3252_, v___y_3253_);
stack->m_obj
 = v_res_3259_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3260_, v___y_3261_);
lean_dec_ref(v___y_3261_);
lean_dec_ref(v_opt_3260_);
return v_res_3263_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3266_ = l_Lean_stringToMessageData(v___x_3265_);
return v___x_3266_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3268_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3269_ = l_Lean_stringToMessageData(v___x_3268_);
return v___x_3269_;
}
}
lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v___x_3278_; lean_object* v_env_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3301_; 
v___x_3278_ = lean_st_ref_get(v___y_3276_);
v_env_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc_ref(v_env_3279_);
lean_dec(v___x_3278_);
v___x_3280_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3281_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3280_, v___y_3275_);
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3284_ = v___x_3281_;
v_isShared_3285_ = v_isSharedCheck_3301_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3281_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3301_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
uint8_t v_isExporting_3291_; 
v_isExporting_3291_ = lean_ctor_get_uint8(v_env_3279_, sizeof(void*)*13);
lean_dec_ref(v_env_3279_);
if (v_isExporting_3291_ == 0)
{
lean_dec(v_a_3282_);
lean_dec(v_id_3270_);
goto v___jp_3286_;
}
else
{
uint8_t v___x_3292_; 
v___x_3292_ = l_Lean_isPrivateName(v_id_3270_);
if (v___x_3292_ == 0)
{
lean_dec(v_a_3282_);
lean_dec(v_id_3270_);
goto v___jp_3286_;
}
else
{
uint8_t v___x_3293_; 
v___x_3293_ = lean_unbox(v_a_3282_);
lean_dec(v_a_3282_);
if (v___x_3293_ == 0)
{
lean_dec(v_id_3270_);
goto v___jp_3286_;
}
else
{
lean_object* v___x_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_del_object(v___x_3284_);
v___x_3294_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3295_ = 0;
v___x_3296_ = l_Lean_MessageData_ofConstName(v_id_3270_, v___x_3295_);
v___x_3297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3294_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3299_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
return v___x_3300_;
}
}
}
v___jp_3286_:
{
lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3287_ = lean_box(0);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v___x_3287_);
v___x_3289_ = v___x_3284_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_3270_ = stack[0].m_obj;
lean_object* v___y_3271_ = stack[1].m_obj;
lean_object* v___y_3272_ = stack[2].m_obj;
lean_object* v___y_3273_ = stack[3].m_obj;
lean_object* v___y_3274_ = stack[4].m_obj;
lean_object* v___y_3275_ = stack[5].m_obj;
lean_object* v___y_3276_ = stack[6].m_obj;
lean_object* v_res_3302_;
v_res_3302_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
stack->m_obj
 = v_res_3302_;
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
return v_res_3311_;
}
}
lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3312_, uint8_t v_enableLog_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v___x_3321_; lean_object* v_toCold_3322_; lean_object* v_env_3323_; lean_object* v_currNamespace_3324_; lean_object* v_openDecls_3325_; lean_object* v___x_3326_; lean_object* v_res_3327_; lean_object* v___x_3328_; 
v___x_3321_ = lean_st_ref_get(v___y_3319_);
v_toCold_3322_ = lean_ctor_get(v___y_3318_, 0);
v_env_3323_ = lean_ctor_get(v___x_3321_, 0);
lean_inc_ref(v_env_3323_);
lean_dec(v___x_3321_);
v_currNamespace_3324_ = lean_ctor_get(v_toCold_3322_, 4);
v_openDecls_3325_ = lean_ctor_get(v_toCold_3322_, 5);
v___x_3326_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3318_);
lean_inc(v_openDecls_3325_);
lean_inc(v_currNamespace_3324_);
v_res_3327_ = l_Lean_ResolveName_resolveGlobalName(v_env_3323_, v___x_3326_, v_currNamespace_3324_, v_openDecls_3325_, v_id_3312_);
lean_dec_ref(v___x_3326_);
v___x_3328_ = lean_st_ref_get(v___y_3319_);
if (v_enableLog_3313_ == 0)
{
lean_object* v___x_3329_; 
lean_dec(v___x_3328_);
v___x_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3329_, 0, v_res_3327_);
return v___x_3329_;
}
else
{
lean_object* v_env_3330_; uint8_t v_isExporting_3331_; 
v_env_3330_ = lean_ctor_get(v___x_3328_, 0);
lean_inc_ref(v_env_3330_);
lean_dec(v___x_3328_);
v_isExporting_3331_ = lean_ctor_get_uint8(v_env_3330_, sizeof(void*)*13);
lean_dec_ref(v_env_3330_);
if (v_isExporting_3331_ == 0)
{
lean_object* v___x_3332_; 
v___x_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3332_, 0, v_res_3327_);
return v___x_3332_;
}
else
{
lean_object* v___x_3333_; 
v___x_3333_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3327_);
if (lean_obj_tag(v___x_3333_) == 1)
{
lean_object* v_val_3334_; lean_object* v_fst_3335_; lean_object* v___x_3336_; 
v_val_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_val_3334_);
lean_dec_ref_known(v___x_3333_, 1);
v_fst_3335_ = lean_ctor_get(v_val_3334_, 0);
lean_inc(v_fst_3335_);
lean_dec(v_val_3334_);
v___x_3336_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3335_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3343_ == 0)
{
lean_object* v_unused_3344_; 
v_unused_3344_ = lean_ctor_get(v___x_3336_, 0);
lean_dec(v_unused_3344_);
v___x_3338_ = v___x_3336_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_dec(v___x_3336_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v_res_3327_);
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_res_3327_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_res_3327_);
v_a_3345_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3336_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3336_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
else
{
lean_object* v___x_3353_; 
lean_dec(v___x_3333_);
v___x_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3353_, 0, v_res_3327_);
return v___x_3353_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_3312_ = stack[0].m_obj;
uint8_t v_enableLog_3313_ = stack[1].m_num;
lean_object* v___y_3314_ = stack[2].m_obj;
lean_object* v___y_3315_ = stack[3].m_obj;
lean_object* v___y_3316_ = stack[4].m_obj;
lean_object* v___y_3317_ = stack[5].m_obj;
lean_object* v___y_3318_ = stack[6].m_obj;
lean_object* v___y_3319_ = stack[7].m_obj;
lean_object* v_res_3354_;
v_res_3354_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3312_, v_enableLog_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
stack->m_obj
 = v_res_3354_;
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3355_, lean_object* v_enableLog_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
uint8_t v_enableLog_boxed_3364_; lean_object* v_res_3365_; 
v_enableLog_boxed_3364_ = lean_unbox(v_enableLog_3356_);
v_res_3365_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3355_, v_enableLog_boxed_3364_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3366_, lean_object* v_a_3367_){
_start:
{
if (lean_obj_tag(v_a_3366_) == 0)
{
lean_object* v___x_3368_; 
v___x_3368_ = l_List_reverse___redArg(v_a_3367_);
return v___x_3368_;
}
else
{
lean_object* v_head_3369_; lean_object* v_tail_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3381_; 
v_head_3369_ = lean_ctor_get(v_a_3366_, 0);
v_tail_3370_ = lean_ctor_get(v_a_3366_, 1);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_a_3366_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3372_ = v_a_3366_;
v_isShared_3373_ = v_isSharedCheck_3381_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_tail_3370_);
lean_inc(v_head_3369_);
lean_dec(v_a_3366_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3381_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v_snd_3374_; uint8_t v___x_3375_; 
v_snd_3374_ = lean_ctor_get(v_head_3369_, 1);
v___x_3375_ = l_List_isEmpty___redArg(v_snd_3374_);
if (v___x_3375_ == 0)
{
lean_del_object(v___x_3372_);
lean_dec(v_head_3369_);
v_a_3366_ = v_tail_3370_;
goto _start;
}
else
{
lean_object* v___x_3378_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 1, v_a_3367_);
v___x_3378_ = v___x_3372_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_head_3369_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_a_3367_);
v___x_3378_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
v_a_3366_ = v_tail_3370_;
v_a_3367_ = v___x_3378_;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3382_, lean_object* v_findLocalDecl_x3f_3383_, lean_object* v_n_3384_, lean_object* v_projs_3385_, uint8_t v_globalDeclFound_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v___y_3395_; lean_object* v___y_3396_; uint8_t v_globalDeclFoundNext_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v_imported_3406_; lean_object* v_ctx_3407_; lean_object* v_scopes_3408_; lean_object* v_givenNameView_3409_; uint8_t v___y_3411_; 
v_imported_3406_ = lean_ctor_get(v_view_3382_, 1);
v_ctx_3407_ = lean_ctor_get(v_view_3382_, 2);
v_scopes_3408_ = lean_ctor_get(v_view_3382_, 3);
lean_inc(v_scopes_3408_);
lean_inc(v_ctx_3407_);
lean_inc(v_imported_3406_);
lean_inc(v_n_3384_);
v_givenNameView_3409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3409_, 0, v_n_3384_);
lean_ctor_set(v_givenNameView_3409_, 1, v_imported_3406_);
lean_ctor_set(v_givenNameView_3409_, 2, v_ctx_3407_);
lean_ctor_set(v_givenNameView_3409_, 3, v_scopes_3408_);
if (v_globalDeclFound_3386_ == 0)
{
v___y_3411_ = v_globalDeclFound_3386_;
goto v___jp_3410_;
}
else
{
uint8_t v___x_3446_; 
v___x_3446_ = l_List_isEmpty___redArg(v_projs_3385_);
if (v___x_3446_ == 0)
{
v___y_3411_ = v_globalDeclFound_3386_;
goto v___jp_3410_;
}
else
{
uint8_t v___x_3447_; 
v___x_3447_ = 0;
v___y_3411_ = v___x_3447_;
goto v___jp_3410_;
}
}
v___jp_3394_:
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___y_3395_);
lean_ctor_set(v___x_3404_, 1, v_projs_3385_);
v_n_3384_ = v___y_3396_;
v_projs_3385_ = v___x_3404_;
v_globalDeclFound_3386_ = v_globalDeclFoundNext_3397_;
v___y_3387_ = v___y_3398_;
v___y_3388_ = v___y_3399_;
v___y_3389_ = v___y_3400_;
v___y_3390_ = v___y_3401_;
v___y_3391_ = v___y_3402_;
v___y_3392_ = v___y_3403_;
goto _start;
}
v___jp_3410_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = lean_box(v___y_3411_);
lean_inc_ref(v_findLocalDecl_x3f_3383_);
lean_inc_ref(v_givenNameView_3409_);
v___x_3413_ = lean_apply_2(v_findLocalDecl_x3f_3383_, v_givenNameView_3409_, v___x_3412_);
if (lean_obj_tag(v___x_3413_) == 0)
{
if (lean_obj_tag(v_n_3384_) == 1)
{
if (v_globalDeclFound_3386_ == 0)
{
lean_object* v_pre_3414_; lean_object* v_str_3415_; uint8_t v_globalDeclFoundNext_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v_pre_3414_ = lean_ctor_get(v_n_3384_, 0);
lean_inc(v_pre_3414_);
v_str_3415_ = lean_ctor_get(v_n_3384_, 1);
lean_inc_ref(v_str_3415_);
lean_dec_ref_known(v_n_3384_, 2);
v_globalDeclFoundNext_3416_ = 1;
v___x_3417_ = l_Lean_MacroScopesView_review(v_givenNameView_3409_);
v___x_3418_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3417_, v_globalDeclFound_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3420_; lean_object* v_r_3421_; uint8_t v___x_3422_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3418_, 1);
v___x_3420_ = lean_box(0);
v_r_3421_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3419_, v___x_3420_);
v___x_3422_ = l_List_isEmpty___redArg(v_r_3421_);
lean_dec(v_r_3421_);
if (v___x_3422_ == 0)
{
v___y_3395_ = v_str_3415_;
v___y_3396_ = v_pre_3414_;
v_globalDeclFoundNext_3397_ = v_globalDeclFoundNext_3416_;
v___y_3398_ = v___y_3387_;
v___y_3399_ = v___y_3388_;
v___y_3400_ = v___y_3389_;
v___y_3401_ = v___y_3390_;
v___y_3402_ = v___y_3391_;
v___y_3403_ = v___y_3392_;
goto v___jp_3394_;
}
else
{
v___y_3395_ = v_str_3415_;
v___y_3396_ = v_pre_3414_;
v_globalDeclFoundNext_3397_ = v_globalDeclFound_3386_;
v___y_3398_ = v___y_3387_;
v___y_3399_ = v___y_3388_;
v___y_3400_ = v___y_3389_;
v___y_3401_ = v___y_3390_;
v___y_3402_ = v___y_3391_;
v___y_3403_ = v___y_3392_;
goto v___jp_3394_;
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v_str_3415_);
lean_dec(v_pre_3414_);
lean_dec(v_projs_3385_);
lean_dec_ref(v_findLocalDecl_x3f_3383_);
v_a_3423_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3418_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3418_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_object* v_pre_3431_; lean_object* v_str_3432_; 
lean_dec_ref_known(v_givenNameView_3409_, 4);
v_pre_3431_ = lean_ctor_get(v_n_3384_, 0);
lean_inc(v_pre_3431_);
v_str_3432_ = lean_ctor_get(v_n_3384_, 1);
lean_inc_ref(v_str_3432_);
lean_dec_ref_known(v_n_3384_, 2);
v___y_3395_ = v_str_3432_;
v___y_3396_ = v_pre_3431_;
v_globalDeclFoundNext_3397_ = v_globalDeclFound_3386_;
v___y_3398_ = v___y_3387_;
v___y_3399_ = v___y_3388_;
v___y_3400_ = v___y_3389_;
v___y_3401_ = v___y_3390_;
v___y_3402_ = v___y_3391_;
v___y_3403_ = v___y_3392_;
goto v___jp_3394_;
}
}
else
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_dec_ref_known(v_givenNameView_3409_, 4);
lean_dec(v_projs_3385_);
lean_dec(v_n_3384_);
lean_dec_ref(v_findLocalDecl_x3f_3383_);
v___x_3433_ = lean_box(0);
v___x_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
return v___x_3434_;
}
}
else
{
lean_object* v_val_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref_known(v_givenNameView_3409_, 4);
lean_dec(v_n_3384_);
lean_dec_ref(v_findLocalDecl_x3f_3383_);
v_val_3435_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3437_ = v___x_3413_;
v_isShared_3438_ = v_isSharedCheck_3445_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_val_3435_);
lean_dec(v___x_3413_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3445_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3439_ = l_Lean_LocalDecl_toExpr(v_val_3435_);
v___x_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
lean_ctor_set(v___x_3440_, 1, v_projs_3385_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3440_);
v___x_3442_ = v___x_3437_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
return v___x_3443_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_view_3382_ = stack[0].m_obj;
lean_object* v_findLocalDecl_x3f_3383_ = stack[1].m_obj;
lean_object* v_n_3384_ = stack[2].m_obj;
lean_object* v_projs_3385_ = stack[3].m_obj;
uint8_t v_globalDeclFound_3386_ = stack[4].m_num;
lean_object* v___y_3387_ = stack[5].m_obj;
lean_object* v___y_3388_ = stack[6].m_obj;
lean_object* v___y_3389_ = stack[7].m_obj;
lean_object* v___y_3390_ = stack[8].m_obj;
lean_object* v___y_3391_ = stack[9].m_obj;
lean_object* v___y_3392_ = stack[10].m_obj;
lean_object* v_res_3448_;
v_res_3448_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3382_, v_findLocalDecl_x3f_3383_, v_n_3384_, v_projs_3385_, v_globalDeclFound_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
stack->m_obj
 = v_res_3448_;
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3449_, lean_object* v_findLocalDecl_x3f_3450_, lean_object* v_n_3451_, lean_object* v_projs_3452_, lean_object* v_globalDeclFound_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
uint8_t v_globalDeclFound_boxed_3461_; lean_object* v_res_3462_; 
v_globalDeclFound_boxed_3461_ = lean_unbox(v_globalDeclFound_3453_);
v_res_3462_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3449_, v_findLocalDecl_x3f_3450_, v_n_3451_, v_projs_3452_, v_globalDeclFound_boxed_3461_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec_ref(v_view_3449_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3463_, lean_object* v_givenName_3464_, lean_object* v_as_3465_, lean_object* v_i_3466_){
_start:
{
lean_object* v_zero_3467_; uint8_t v_isZero_3468_; 
v_zero_3467_ = lean_unsigned_to_nat(0u);
v_isZero_3468_ = lean_nat_dec_eq(v_i_3466_, v_zero_3467_);
if (v_isZero_3468_ == 1)
{
lean_object* v___x_3469_; 
lean_dec(v_i_3466_);
v___x_3469_ = lean_box(0);
return v___x_3469_;
}
else
{
lean_object* v_one_3470_; lean_object* v_n_3471_; lean_object* v___y_3473_; lean_object* v___x_3475_; 
v_one_3470_ = lean_unsigned_to_nat(1u);
v_n_3471_ = lean_nat_sub(v_i_3466_, v_one_3470_);
lean_dec(v_i_3466_);
v___x_3475_ = lean_array_fget_borrowed(v_as_3465_, v_n_3471_);
if (lean_obj_tag(v___x_3475_) == 0)
{
v___y_3473_ = v___x_3475_;
goto v___jp_3472_;
}
else
{
lean_object* v_val_3476_; uint8_t v___x_3477_; 
v_val_3476_ = lean_ctor_get(v___x_3475_, 0);
v___x_3477_ = l_Lean_LocalDecl_isAuxDecl(v_val_3476_);
if (v___x_3477_ == 0)
{
v___y_3473_ = v_localDecl_x3f_3463_;
goto v___jp_3472_;
}
else
{
lean_object* v___x_3478_; uint8_t v___x_3479_; 
v___x_3478_ = l_Lean_LocalDecl_userName(v_val_3476_);
v___x_3479_ = lean_name_eq(v___x_3478_, v_givenName_3464_);
lean_dec(v___x_3478_);
if (v___x_3479_ == 0)
{
v_i_3466_ = v_n_3471_;
goto _start;
}
else
{
v___y_3473_ = v___x_3475_;
goto v___jp_3472_;
}
}
}
v___jp_3472_:
{
if (lean_obj_tag(v___y_3473_) == 0)
{
v_i_3466_ = v_n_3471_;
goto _start;
}
else
{
lean_dec(v_n_3471_);
lean_inc_ref(v___y_3473_);
return v___y_3473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3481_, lean_object* v_givenName_3482_, lean_object* v_as_3483_, lean_object* v_i_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3481_, v_givenName_3482_, v_as_3483_, v_i_3484_);
lean_dec_ref(v_as_3483_);
lean_dec(v_givenName_3482_);
lean_dec(v_localDecl_x3f_3481_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3486_, lean_object* v_givenName_3487_, lean_object* v_as_3488_, lean_object* v_i_3489_){
_start:
{
lean_object* v_zero_3490_; uint8_t v_isZero_3491_; 
v_zero_3490_ = lean_unsigned_to_nat(0u);
v_isZero_3491_ = lean_nat_dec_eq(v_i_3489_, v_zero_3490_);
if (v_isZero_3491_ == 1)
{
lean_object* v___x_3492_; 
lean_dec(v_i_3489_);
v___x_3492_ = lean_box(0);
return v___x_3492_;
}
else
{
lean_object* v_one_3493_; lean_object* v_n_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v_one_3493_ = lean_unsigned_to_nat(1u);
v_n_3494_ = lean_nat_sub(v_i_3489_, v_one_3493_);
lean_dec(v_i_3489_);
v___x_3495_ = lean_array_fget_borrowed(v_as_3488_, v_n_3494_);
v___x_3496_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3486_, v_givenName_3487_, v___x_3495_);
if (lean_obj_tag(v___x_3496_) == 0)
{
v_i_3489_ = v_n_3494_;
goto _start;
}
else
{
lean_dec(v_n_3494_);
return v___x_3496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3498_, lean_object* v_givenName_3499_, lean_object* v_x_3500_){
_start:
{
if (lean_obj_tag(v_x_3500_) == 0)
{
lean_object* v_cs_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_cs_3501_ = lean_ctor_get(v_x_3500_, 0);
v___x_3502_ = lean_array_get_size(v_cs_3501_);
v___x_3503_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3498_, v_givenName_3499_, v_cs_3501_, v___x_3502_);
return v___x_3503_;
}
else
{
lean_object* v_vs_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_vs_3504_ = lean_ctor_get(v_x_3500_, 0);
v___x_3505_ = lean_array_get_size(v_vs_3504_);
v___x_3506_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3498_, v_givenName_3499_, v_vs_3504_, v___x_3505_);
return v___x_3506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3507_, lean_object* v_givenName_3508_, lean_object* v_x_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3507_, v_givenName_3508_, v_x_3509_);
lean_dec_ref(v_x_3509_);
lean_dec(v_givenName_3508_);
lean_dec(v_localDecl_x3f_3507_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3511_, lean_object* v_givenName_3512_, lean_object* v_as_3513_, lean_object* v_i_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3511_, v_givenName_3512_, v_as_3513_, v_i_3514_);
lean_dec_ref(v_as_3513_);
lean_dec(v_givenName_3512_);
lean_dec(v_localDecl_x3f_3511_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3516_, lean_object* v_givenName_3517_, lean_object* v_t_3518_){
_start:
{
lean_object* v_root_3519_; lean_object* v_tail_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v_root_3519_ = lean_ctor_get(v_t_3518_, 0);
v_tail_3520_ = lean_ctor_get(v_t_3518_, 1);
v___x_3521_ = lean_array_get_size(v_tail_3520_);
v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3516_, v_givenName_3517_, v_tail_3520_, v___x_3521_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3516_, v_givenName_3517_, v_root_3519_);
return v___x_3523_;
}
else
{
return v___x_3522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3524_, lean_object* v_givenName_3525_, lean_object* v_t_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3524_, v_givenName_3525_, v_t_3526_);
lean_dec_ref(v_t_3526_);
lean_dec(v_givenName_3525_);
lean_dec(v_localDecl_x3f_3524_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3528_, lean_object* v_k_3529_){
_start:
{
if (lean_obj_tag(v_t_3528_) == 0)
{
lean_object* v_k_3530_; lean_object* v_v_3531_; lean_object* v_l_3532_; lean_object* v_r_3533_; uint8_t v___x_3534_; 
v_k_3530_ = lean_ctor_get(v_t_3528_, 1);
v_v_3531_ = lean_ctor_get(v_t_3528_, 2);
v_l_3532_ = lean_ctor_get(v_t_3528_, 3);
v_r_3533_ = lean_ctor_get(v_t_3528_, 4);
v___x_3534_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3529_, v_k_3530_);
switch(v___x_3534_)
{
case 0:
{
v_t_3528_ = v_l_3532_;
goto _start;
}
case 1:
{
lean_object* v___x_3536_; 
lean_inc(v_v_3531_);
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v_v_3531_);
return v___x_3536_;
}
default: 
{
v_t_3528_ = v_r_3533_;
goto _start;
}
}
}
else
{
lean_object* v___x_3538_; 
v___x_3538_ = lean_box(0);
return v___x_3538_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3539_, lean_object* v_k_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3539_, v_k_3540_);
lean_dec(v_k_3540_);
lean_dec(v_t_3539_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3542_, lean_object* v_givenName_3543_){
_start:
{
lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3544_ = l_Lean_LocalDecl_userName(v_localDecl_3542_);
v___x_3545_ = lean_name_eq(v___x_3544_, v_givenName_3543_);
lean_dec(v___x_3544_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; 
lean_dec_ref(v_localDecl_3542_);
v___x_3546_ = lean_box(0);
return v___x_3546_;
}
else
{
lean_object* v___x_3547_; 
v___x_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3547_, 0, v_localDecl_3542_);
return v___x_3547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3548_, lean_object* v_givenName_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3548_, v_givenName_3549_);
lean_dec(v_givenName_3549_);
return v_res_3550_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3551_, uint8_t v_skipAuxDecl_3552_, lean_object* v_auxDeclToFullName_3553_, lean_object* v___x_3554_, lean_object* v_givenNameView_3555_, lean_object* v_as_3556_, lean_object* v_i_3557_){
_start:
{
lean_object* v_zero_3558_; uint8_t v_isZero_3559_; 
v_zero_3558_ = lean_unsigned_to_nat(0u);
v_isZero_3559_ = lean_nat_dec_eq(v_i_3557_, v_zero_3558_);
if (v_isZero_3559_ == 1)
{
lean_object* v___x_3560_; 
lean_dec(v_i_3557_);
lean_dec_ref(v_givenNameView_3555_);
lean_dec(v___x_3554_);
v___x_3560_ = lean_box(0);
return v___x_3560_;
}
else
{
lean_object* v_one_3561_; lean_object* v_n_3562_; lean_object* v___y_3564_; lean_object* v___x_3566_; 
v_one_3561_ = lean_unsigned_to_nat(1u);
v_n_3562_ = lean_nat_sub(v_i_3557_, v_one_3561_);
lean_dec(v_i_3557_);
v___x_3566_ = lean_array_fget_borrowed(v_as_3556_, v_n_3562_);
if (lean_obj_tag(v___x_3566_) == 0)
{
v___y_3564_ = v___x_3566_;
goto v___jp_3563_;
}
else
{
lean_object* v_val_3567_; uint8_t v___x_3568_; 
v_val_3567_ = lean_ctor_get(v___x_3566_, 0);
v___x_3568_ = l_Lean_LocalDecl_isAuxDecl(v_val_3567_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3569_; 
lean_inc(v_val_3567_);
v___x_3569_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3567_, v_givenName_3551_);
v___y_3564_ = v___x_3569_;
goto v___jp_3563_;
}
else
{
if (v_skipAuxDecl_3552_ == 0)
{
if (v___x_3568_ == 0)
{
v_i_3557_ = v_n_3562_;
goto _start;
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = l_Lean_LocalDecl_fvarId(v_val_3567_);
v___x_3572_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3553_, v___x_3571_);
lean_dec(v___x_3571_);
if (lean_obj_tag(v___x_3572_) == 1)
{
lean_object* v_val_3573_; lean_object* v_fullDeclView_3574_; lean_object* v___y_3576_; lean_object* v_name_3597_; lean_object* v___x_3598_; 
v_val_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_val_3573_);
lean_dec_ref_known(v___x_3572_, 1);
v_fullDeclView_3574_ = l_Lean_extractMacroScopes(v_val_3573_);
v_name_3597_ = lean_ctor_get(v_fullDeclView_3574_, 0);
lean_inc(v_name_3597_);
v___x_3598_ = l_Lean_privateToUserName_x3f(v_name_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_inc(v_name_3597_);
v___y_3576_ = v_name_3597_;
goto v___jp_3575_;
}
else
{
lean_object* v_val_3599_; 
v_val_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_val_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v___y_3576_ = v_val_3599_;
goto v___jp_3575_;
}
v___jp_3575_:
{
lean_object* v_imported_3577_; lean_object* v_ctx_3578_; lean_object* v_scopes_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3595_; 
v_imported_3577_ = lean_ctor_get(v_fullDeclView_3574_, 1);
v_ctx_3578_ = lean_ctor_get(v_fullDeclView_3574_, 2);
v_scopes_3579_ = lean_ctor_get(v_fullDeclView_3574_, 3);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_fullDeclView_3574_);
if (v_isSharedCheck_3595_ == 0)
{
lean_object* v_unused_3596_; 
v_unused_3596_ = lean_ctor_get(v_fullDeclView_3574_, 0);
lean_dec(v_unused_3596_);
v___x_3581_ = v_fullDeclView_3574_;
v_isShared_3582_ = v_isSharedCheck_3595_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_scopes_3579_);
lean_inc(v_ctx_3578_);
lean_inc(v_imported_3577_);
lean_dec(v_fullDeclView_3574_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3595_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v_fullDeclView_3584_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v___y_3576_);
v_fullDeclView_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___y_3576_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_imported_3577_);
lean_ctor_set(v_reuseFailAlloc_3594_, 2, v_ctx_3578_);
lean_ctor_set(v_reuseFailAlloc_3594_, 3, v_scopes_3579_);
v_fullDeclView_3584_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v_fullDeclName_3585_; uint8_t v___x_3586_; 
lean_inc_ref(v_fullDeclView_3584_);
v_fullDeclName_3585_ = l_Lean_MacroScopesView_review(v_fullDeclView_3584_);
v___x_3586_ = l_Lean_Name_isPrefixOf(v___x_3554_, v_fullDeclName_3585_);
if (v___x_3586_ == 0)
{
lean_object* v___x_3587_; 
lean_dec_ref(v_fullDeclView_3584_);
lean_inc(v___x_3554_);
lean_inc_ref(v_givenNameView_3555_);
lean_inc(v_val_3567_);
v___x_3587_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3567_, v_givenNameView_3555_, v_fullDeclName_3585_, v___x_3554_);
lean_dec(v_fullDeclName_3585_);
v___y_3564_ = v___x_3587_;
goto v___jp_3563_;
}
else
{
lean_object* v___x_3588_; lean_object* v_localDeclNameView_3589_; uint8_t v___x_3590_; 
lean_dec(v_fullDeclName_3585_);
v___x_3588_ = l_Lean_LocalDecl_userName(v_val_3567_);
v_localDeclNameView_3589_ = l_Lean_extractMacroScopes(v___x_3588_);
v___x_3590_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3589_, v_givenNameView_3555_);
lean_dec_ref(v_localDeclNameView_3589_);
if (v___x_3590_ == 0)
{
lean_dec_ref(v_fullDeclView_3584_);
v_i_3557_ = v_n_3562_;
goto _start;
}
else
{
uint8_t v___x_3592_; 
v___x_3592_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3555_, v_fullDeclView_3584_);
lean_dec_ref(v_fullDeclView_3584_);
if (v___x_3592_ == 0)
{
v_i_3557_ = v_n_3562_;
goto _start;
}
else
{
lean_inc_ref(v___x_3566_);
v___y_3564_ = v___x_3566_;
goto v___jp_3563_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3600_; 
lean_dec(v___x_3572_);
lean_inc(v_val_3567_);
v___x_3600_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3567_, v_givenName_3551_);
v___y_3564_ = v___x_3600_;
goto v___jp_3563_;
}
}
}
else
{
v_i_3557_ = v_n_3562_;
goto _start;
}
}
}
v___jp_3563_:
{
if (lean_obj_tag(v___y_3564_) == 0)
{
v_i_3557_ = v_n_3562_;
goto _start;
}
else
{
lean_dec(v_n_3562_);
lean_dec_ref(v_givenNameView_3555_);
lean_dec(v___x_3554_);
return v___y_3564_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_givenName_3551_ = stack[0].m_obj;
uint8_t v_skipAuxDecl_3552_ = stack[1].m_num;
lean_object* v_auxDeclToFullName_3553_ = stack[2].m_obj;
lean_object* v___x_3554_ = stack[3].m_obj;
lean_object* v_givenNameView_3555_ = stack[4].m_obj;
lean_object* v_as_3556_ = stack[5].m_obj;
lean_object* v_i_3557_ = stack[6].m_obj;
lean_object* v_res_3602_;
v_res_3602_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3551_, v_skipAuxDecl_3552_, v_auxDeclToFullName_3553_, v___x_3554_, v_givenNameView_3555_, v_as_3556_, v_i_3557_);
stack->m_obj
 = v_res_3602_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3603_, lean_object* v_skipAuxDecl_3604_, lean_object* v_auxDeclToFullName_3605_, lean_object* v___x_3606_, lean_object* v_givenNameView_3607_, lean_object* v_as_3608_, lean_object* v_i_3609_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3610_; lean_object* v_res_3611_; 
v_skipAuxDecl_boxed_3610_ = lean_unbox(v_skipAuxDecl_3604_);
v_res_3611_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3603_, v_skipAuxDecl_boxed_3610_, v_auxDeclToFullName_3605_, v___x_3606_, v_givenNameView_3607_, v_as_3608_, v_i_3609_);
lean_dec_ref(v_as_3608_);
lean_dec(v_auxDeclToFullName_3605_);
lean_dec(v_givenName_3603_);
return v_res_3611_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3612_, uint8_t v_skipAuxDecl_3613_, lean_object* v_auxDeclToFullName_3614_, lean_object* v___x_3615_, lean_object* v_givenNameView_3616_, lean_object* v_as_3617_, lean_object* v_i_3618_){
_start:
{
lean_object* v_zero_3619_; uint8_t v_isZero_3620_; 
v_zero_3619_ = lean_unsigned_to_nat(0u);
v_isZero_3620_ = lean_nat_dec_eq(v_i_3618_, v_zero_3619_);
if (v_isZero_3620_ == 1)
{
lean_object* v___x_3621_; 
lean_dec(v_i_3618_);
lean_dec_ref(v_givenNameView_3616_);
lean_dec(v___x_3615_);
v___x_3621_ = lean_box(0);
return v___x_3621_;
}
else
{
lean_object* v_one_3622_; lean_object* v_n_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v_one_3622_ = lean_unsigned_to_nat(1u);
v_n_3623_ = lean_nat_sub(v_i_3618_, v_one_3622_);
lean_dec(v_i_3618_);
v___x_3624_ = lean_array_fget_borrowed(v_as_3617_, v_n_3623_);
lean_inc_ref(v_givenNameView_3616_);
lean_inc(v___x_3615_);
v___x_3625_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3612_, v_skipAuxDecl_3613_, v_auxDeclToFullName_3614_, v___x_3615_, v_givenNameView_3616_, v___x_3624_);
if (lean_obj_tag(v___x_3625_) == 0)
{
v_i_3618_ = v_n_3623_;
goto _start;
}
else
{
lean_dec(v_n_3623_);
lean_dec_ref(v_givenNameView_3616_);
lean_dec(v___x_3615_);
return v___x_3625_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_givenName_3612_ = stack[0].m_obj;
uint8_t v_skipAuxDecl_3613_ = stack[1].m_num;
lean_object* v_auxDeclToFullName_3614_ = stack[2].m_obj;
lean_object* v___x_3615_ = stack[3].m_obj;
lean_object* v_givenNameView_3616_ = stack[4].m_obj;
lean_object* v_as_3617_ = stack[5].m_obj;
lean_object* v_i_3618_ = stack[6].m_obj;
lean_object* v_res_3627_;
v_res_3627_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3612_, v_skipAuxDecl_3613_, v_auxDeclToFullName_3614_, v___x_3615_, v_givenNameView_3616_, v_as_3617_, v_i_3618_);
stack->m_obj
 = v_res_3627_;
}
lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3628_, uint8_t v_skipAuxDecl_3629_, lean_object* v_auxDeclToFullName_3630_, lean_object* v___x_3631_, lean_object* v_givenNameView_3632_, lean_object* v_x_3633_){
_start:
{
if (lean_obj_tag(v_x_3633_) == 0)
{
lean_object* v_cs_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v_cs_3634_ = lean_ctor_get(v_x_3633_, 0);
v___x_3635_ = lean_array_get_size(v_cs_3634_);
v___x_3636_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3628_, v_skipAuxDecl_3629_, v_auxDeclToFullName_3630_, v___x_3631_, v_givenNameView_3632_, v_cs_3634_, v___x_3635_);
return v___x_3636_;
}
else
{
lean_object* v_vs_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v_vs_3637_ = lean_ctor_get(v_x_3633_, 0);
v___x_3638_ = lean_array_get_size(v_vs_3637_);
v___x_3639_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3628_, v_skipAuxDecl_3629_, v_auxDeclToFullName_3630_, v___x_3631_, v_givenNameView_3632_, v_vs_3637_, v___x_3638_);
return v___x_3639_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_givenName_3628_ = stack[0].m_obj;
uint8_t v_skipAuxDecl_3629_ = stack[1].m_num;
lean_object* v_auxDeclToFullName_3630_ = stack[2].m_obj;
lean_object* v___x_3631_ = stack[3].m_obj;
lean_object* v_givenNameView_3632_ = stack[4].m_obj;
lean_object* v_x_3633_ = stack[5].m_obj;
lean_object* v_res_3640_;
v_res_3640_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3628_, v_skipAuxDecl_3629_, v_auxDeclToFullName_3630_, v___x_3631_, v_givenNameView_3632_, v_x_3633_);
stack->m_obj
 = v_res_3640_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3641_, lean_object* v_skipAuxDecl_3642_, lean_object* v_auxDeclToFullName_3643_, lean_object* v___x_3644_, lean_object* v_givenNameView_3645_, lean_object* v_x_3646_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3647_; lean_object* v_res_3648_; 
v_skipAuxDecl_boxed_3647_ = lean_unbox(v_skipAuxDecl_3642_);
v_res_3648_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3641_, v_skipAuxDecl_boxed_3647_, v_auxDeclToFullName_3643_, v___x_3644_, v_givenNameView_3645_, v_x_3646_);
lean_dec_ref(v_x_3646_);
lean_dec(v_auxDeclToFullName_3643_);
lean_dec(v_givenName_3641_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3649_, lean_object* v_skipAuxDecl_3650_, lean_object* v_auxDeclToFullName_3651_, lean_object* v___x_3652_, lean_object* v_givenNameView_3653_, lean_object* v_as_3654_, lean_object* v_i_3655_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3656_; lean_object* v_res_3657_; 
v_skipAuxDecl_boxed_3656_ = lean_unbox(v_skipAuxDecl_3650_);
v_res_3657_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3649_, v_skipAuxDecl_boxed_3656_, v_auxDeclToFullName_3651_, v___x_3652_, v_givenNameView_3653_, v_as_3654_, v_i_3655_);
lean_dec_ref(v_as_3654_);
lean_dec(v_auxDeclToFullName_3651_);
lean_dec(v_givenName_3649_);
return v_res_3657_;
}
}
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3658_, uint8_t v_skipAuxDecl_3659_, lean_object* v_auxDeclToFullName_3660_, lean_object* v___x_3661_, lean_object* v_givenNameView_3662_, lean_object* v_t_3663_){
_start:
{
lean_object* v_root_3664_; lean_object* v_tail_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v_root_3664_ = lean_ctor_get(v_t_3663_, 0);
v_tail_3665_ = lean_ctor_get(v_t_3663_, 1);
v___x_3666_ = lean_array_get_size(v_tail_3665_);
lean_inc_ref(v_givenNameView_3662_);
lean_inc(v___x_3661_);
v___x_3667_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3658_, v_skipAuxDecl_3659_, v_auxDeclToFullName_3660_, v___x_3661_, v_givenNameView_3662_, v_tail_3665_, v___x_3666_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3658_, v_skipAuxDecl_3659_, v_auxDeclToFullName_3660_, v___x_3661_, v_givenNameView_3662_, v_root_3664_);
return v___x_3668_;
}
else
{
lean_dec_ref(v_givenNameView_3662_);
lean_dec(v___x_3661_);
return v___x_3667_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_givenName_3658_ = stack[0].m_obj;
uint8_t v_skipAuxDecl_3659_ = stack[1].m_num;
lean_object* v_auxDeclToFullName_3660_ = stack[2].m_obj;
lean_object* v___x_3661_ = stack[3].m_obj;
lean_object* v_givenNameView_3662_ = stack[4].m_obj;
lean_object* v_t_3663_ = stack[5].m_obj;
lean_object* v_res_3669_;
v_res_3669_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3658_, v_skipAuxDecl_3659_, v_auxDeclToFullName_3660_, v___x_3661_, v_givenNameView_3662_, v_t_3663_);
stack->m_obj
 = v_res_3669_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3670_, lean_object* v_skipAuxDecl_3671_, lean_object* v_auxDeclToFullName_3672_, lean_object* v___x_3673_, lean_object* v_givenNameView_3674_, lean_object* v_t_3675_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3676_; lean_object* v_res_3677_; 
v_skipAuxDecl_boxed_3676_ = lean_unbox(v_skipAuxDecl_3671_);
v_res_3677_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3670_, v_skipAuxDecl_boxed_3676_, v_auxDeclToFullName_3672_, v___x_3673_, v_givenNameView_3674_, v_t_3675_);
lean_dec_ref(v_t_3675_);
lean_dec(v_auxDeclToFullName_3672_);
lean_dec(v_givenName_3670_);
return v_res_3677_;
}
}
lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3678_, lean_object* v_currNamespace_3679_, lean_object* v_decls_3680_, lean_object* v_givenNameView_3681_, uint8_t v_skipAuxDecl_3682_){
_start:
{
lean_object* v_givenName_3683_; lean_object* v_localDecl_x3f_3684_; 
lean_inc_ref(v_givenNameView_3681_);
v_givenName_3683_ = l_Lean_MacroScopesView_review(v_givenNameView_3681_);
v_localDecl_x3f_3684_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3683_, v_skipAuxDecl_3682_, v_auxDeclToFullName_3678_, v_currNamespace_3679_, v_givenNameView_3681_, v_decls_3680_);
if (lean_obj_tag(v_localDecl_x3f_3684_) == 0)
{
if (v_skipAuxDecl_3682_ == 0)
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3684_, v_givenName_3683_, v_decls_3680_);
lean_dec(v_givenName_3683_);
return v___x_3685_;
}
else
{
lean_dec(v_givenName_3683_);
return v_localDecl_x3f_3684_;
}
}
else
{
lean_dec(v_givenName_3683_);
return v_localDecl_x3f_3684_;
}
}
}
LEAN_EXPORT void l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_auxDeclToFullName_3678_ = stack[0].m_obj;
lean_object* v_currNamespace_3679_ = stack[1].m_obj;
lean_object* v_decls_3680_ = stack[2].m_obj;
lean_object* v_givenNameView_3681_ = stack[3].m_obj;
uint8_t v_skipAuxDecl_3682_ = stack[4].m_num;
lean_object* v_res_3686_;
v_res_3686_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3678_, v_currNamespace_3679_, v_decls_3680_, v_givenNameView_3681_, v_skipAuxDecl_3682_);
stack->m_obj
 = v_res_3686_;
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3687_, lean_object* v_currNamespace_3688_, lean_object* v_decls_3689_, lean_object* v_givenNameView_3690_, lean_object* v_skipAuxDecl_3691_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3692_; lean_object* v_res_3693_; 
v_skipAuxDecl_boxed_3692_ = lean_unbox(v_skipAuxDecl_3691_);
v_res_3693_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3687_, v_currNamespace_3688_, v_decls_3689_, v_givenNameView_3690_, v_skipAuxDecl_boxed_3692_);
lean_dec_ref(v_decls_3689_);
lean_dec(v_auxDeclToFullName_3687_);
return v_res_3693_;
}
}
lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_lctx_3702_; lean_object* v_toCold_3703_; lean_object* v_decls_3704_; lean_object* v_auxDeclToFullName_3705_; lean_object* v_currNamespace_3706_; lean_object* v_view_3707_; lean_object* v_name_3708_; lean_object* v_findLocalDecl_x3f_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; lean_object* v___x_3712_; 
v_lctx_3702_ = lean_ctor_get(v___y_3697_, 2);
v_toCold_3703_ = lean_ctor_get(v___y_3699_, 0);
v_decls_3704_ = lean_ctor_get(v_lctx_3702_, 1);
v_auxDeclToFullName_3705_ = lean_ctor_get(v_lctx_3702_, 2);
v_currNamespace_3706_ = lean_ctor_get(v_toCold_3703_, 4);
v_view_3707_ = l_Lean_extractMacroScopes(v_n_3694_);
v_name_3708_ = lean_ctor_get(v_view_3707_, 0);
lean_inc(v_name_3708_);
lean_inc_ref(v_decls_3704_);
lean_inc(v_currNamespace_3706_);
lean_inc(v_auxDeclToFullName_3705_);
v_findLocalDecl_x3f_3709_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3709_, 0, v_auxDeclToFullName_3705_);
lean_closure_set(v_findLocalDecl_x3f_3709_, 1, v_currNamespace_3706_);
lean_closure_set(v_findLocalDecl_x3f_3709_, 2, v_decls_3704_);
v___x_3710_ = lean_box(0);
v___x_3711_ = 0;
v___x_3712_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3707_, v_findLocalDecl_x3f_3709_, v_name_3708_, v___x_3710_, v___x_3711_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
lean_dec_ref(v_view_3707_);
return v___x_3712_;
}
}
LEAN_EXPORT void l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3694_ = stack[0].m_obj;
lean_object* v___y_3695_ = stack[1].m_obj;
lean_object* v___y_3696_ = stack[2].m_obj;
lean_object* v___y_3697_ = stack[3].m_obj;
lean_object* v___y_3698_ = stack[4].m_obj;
lean_object* v___y_3699_ = stack[5].m_obj;
lean_object* v___y_3700_ = stack[6].m_obj;
lean_object* v_res_3713_;
v_res_3713_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
stack->m_obj
 = v_res_3713_;
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
return v_res_3722_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3723_, lean_object* v_b_3724_){
_start:
{
if (lean_obj_tag(v_as_x27_3723_) == 0)
{
lean_object* v___x_3726_; 
v___x_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3726_, 0, v_b_3724_);
return v___x_3726_;
}
else
{
lean_object* v_head_3727_; lean_object* v_tail_3728_; lean_object* v_config_3729_; lean_object* v_extensions_3730_; lean_object* v_extra_3731_; lean_object* v_extraInj_3732_; lean_object* v_extraFacts_3733_; lean_object* v_symPrios_3734_; lean_object* v_norm_3735_; lean_object* v_normProcs_3736_; lean_object* v_anchorRefs_x3f_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3746_; 
v_head_3727_ = lean_ctor_get(v_as_x27_3723_, 0);
v_tail_3728_ = lean_ctor_get(v_as_x27_3723_, 1);
v_config_3729_ = lean_ctor_get(v_b_3724_, 0);
v_extensions_3730_ = lean_ctor_get(v_b_3724_, 1);
v_extra_3731_ = lean_ctor_get(v_b_3724_, 2);
v_extraInj_3732_ = lean_ctor_get(v_b_3724_, 3);
v_extraFacts_3733_ = lean_ctor_get(v_b_3724_, 4);
v_symPrios_3734_ = lean_ctor_get(v_b_3724_, 5);
v_norm_3735_ = lean_ctor_get(v_b_3724_, 6);
v_normProcs_3736_ = lean_ctor_get(v_b_3724_, 7);
v_anchorRefs_x3f_3737_ = lean_ctor_get(v_b_3724_, 8);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_b_3724_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3739_ = v_b_3724_;
v_isShared_3740_ = v_isSharedCheck_3746_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_anchorRefs_x3f_3737_);
lean_inc(v_normProcs_3736_);
lean_inc(v_norm_3735_);
lean_inc(v_symPrios_3734_);
lean_inc(v_extraFacts_3733_);
lean_inc(v_extraInj_3732_);
lean_inc(v_extra_3731_);
lean_inc(v_extensions_3730_);
lean_inc(v_config_3729_);
lean_dec(v_b_3724_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3746_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3741_; lean_object* v___x_3743_; 
lean_inc(v_head_3727_);
v___x_3741_ = l_Lean_PersistentArray_push___redArg(v_extra_3731_, v_head_3727_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 2, v___x_3741_);
v___x_3743_ = v___x_3739_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_config_3729_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_extensions_3730_);
lean_ctor_set(v_reuseFailAlloc_3745_, 2, v___x_3741_);
lean_ctor_set(v_reuseFailAlloc_3745_, 3, v_extraInj_3732_);
lean_ctor_set(v_reuseFailAlloc_3745_, 4, v_extraFacts_3733_);
lean_ctor_set(v_reuseFailAlloc_3745_, 5, v_symPrios_3734_);
lean_ctor_set(v_reuseFailAlloc_3745_, 6, v_norm_3735_);
lean_ctor_set(v_reuseFailAlloc_3745_, 7, v_normProcs_3736_);
lean_ctor_set(v_reuseFailAlloc_3745_, 8, v_anchorRefs_x3f_3737_);
v___x_3743_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
v_as_x27_3723_ = v_tail_3728_;
v_b_3724_ = v___x_3743_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_3723_ = stack[0].m_obj;
lean_object* v_b_3724_ = stack[1].m_obj;
lean_object* v_res_3747_;
v_res_3747_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3723_, v_b_3724_);
stack->m_obj
 = v_res_3747_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3748_, lean_object* v_b_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3748_, v_b_3749_);
lean_dec(v_as_x27_3748_);
return v_res_3751_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3754_ = l_Lean_stringToMessageData(v___x_3753_);
return v___x_3754_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3757_ = l_Lean_stringToMessageData(v___x_3756_);
return v___x_3757_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3760_ = l_Lean_stringToMessageData(v___x_3759_);
return v___x_3760_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3763_ = l_Lean_stringToMessageData(v___x_3762_);
return v___x_3763_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3765_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3766_ = l_Lean_stringToMessageData(v___x_3765_);
return v___x_3766_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3768_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3769_ = l_Lean_stringToMessageData(v___x_3768_);
return v___x_3769_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3772_ = l_Lean_stringToMessageData(v___x_3771_);
return v___x_3772_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3774_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3775_ = l_Lean_stringToMessageData(v___x_3774_);
return v___x_3775_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3778_ = l_Lean_stringToMessageData(v___x_3777_);
return v___x_3778_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3781_ = l_Lean_stringToMessageData(v___x_3780_);
return v___x_3781_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3783_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3784_ = l_Lean_stringToMessageData(v___x_3783_);
return v___x_3784_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23(void){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3786_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22));
v___x_3787_ = l_Lean_stringToMessageData(v___x_3786_);
return v___x_3787_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25(void){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24));
v___x_3790_ = l_Lean_stringToMessageData(v___x_3789_);
return v___x_3790_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3791_, lean_object* v_p_3792_, lean_object* v_mod_x3f_3793_, lean_object* v_id_3794_, uint8_t v_minIndexable_3795_, uint8_t v_only_3796_, uint8_t v_incremental_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_){
_start:
{
uint8_t v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; uint8_t v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v_a_3960_; lean_object* v___y_4185_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4196_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4197_ = lean_box(0);
lean_inc(v_id_3794_);
v___x_4198_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3794_, v___x_4197_, v_a_3802_, v_a_3803_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4198_, 1);
v_a_3960_ = v_a_4199_;
goto v___jp_3959_;
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4274_; 
v_a_4200_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4202_ = v___x_4198_;
v_isShared_4203_ = v_isSharedCheck_4274_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4198_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4274_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
uint8_t v___y_4205_; uint8_t v___x_4272_; 
v___x_4272_ = l_Lean_Exception_isInterrupt(v_a_4200_);
if (v___x_4272_ == 0)
{
uint8_t v___x_4273_; 
lean_inc(v_a_4200_);
v___x_4273_ = l_Lean_Exception_isRuntime(v_a_4200_);
v___y_4205_ = v___x_4273_;
goto v___jp_4204_;
}
else
{
v___y_4205_ = v___x_4272_;
goto v___jp_4204_;
}
v___jp_4204_:
{
if (v___y_4205_ == 0)
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
lean_del_object(v___x_4202_);
v___x_4206_ = l_Lean_TSyntax_getId(v_id_3794_);
lean_inc(v___x_4206_);
v___x_4207_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4206_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4208_);
lean_dec_ref_known(v___x_4207_, 1);
if (lean_obj_tag(v_a_4208_) == 0)
{
lean_object* v___x_4209_; 
v___x_4209_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_4206_, v_a_3802_, v_a_3803_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4238_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4212_ = v___x_4209_;
v_isShared_4213_ = v_isSharedCheck_4238_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4209_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4238_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
if (lean_obj_tag(v_a_4210_) == 1)
{
lean_del_object(v___x_4212_);
lean_dec(v_a_4200_);
if (lean_obj_tag(v_mod_x3f_3793_) == 1)
{
lean_object* v_val_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_dec_ref_known(v_a_4210_, 1);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v_val_4214_ = lean_ctor_get(v_mod_x3f_3793_, 0);
lean_inc(v_val_4214_);
lean_dec_ref_known(v_mod_x3f_3793_, 1);
v___x_4215_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4216_ = l_Lean_MessageData_ofName(v___x_4206_);
v___x_4217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4215_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
v___x_4218_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4217_);
lean_ctor_set(v___x_4219_, 1, v___x_4218_);
v___x_4220_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4214_, v___x_4219_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
lean_dec(v_val_4214_);
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4220_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4220_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
else
{
lean_object* v_val_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_dec(v___x_4206_);
v_val_4229_ = lean_ctor_get(v_a_4210_, 0);
lean_inc(v_val_4229_);
lean_dec_ref_known(v_a_4210_, 1);
v___x_4230_ = lean_box(0);
lean_inc_ref(v_params_3791_);
v___x_4231_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3791_, v_val_4229_, v___x_4196_, v___y_4205_, v___x_4230_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
lean_dec(v_val_4229_);
v___y_4185_ = v___x_4231_;
goto v___jp_4184_;
}
}
else
{
lean_object* v___x_4232_; uint8_t v___x_4233_; 
lean_dec(v_a_4210_);
v___x_4232_ = l_Lean_Name_getPrefix(v___x_4206_);
lean_dec(v___x_4206_);
v___x_4233_ = l_Lean_Name_isAnonymous(v___x_4232_);
lean_dec(v___x_4232_);
if (v___x_4233_ == 0)
{
lean_object* v___x_4234_; 
lean_del_object(v___x_4212_);
lean_dec(v_a_4200_);
v___x_4234_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3791_, v_p_3792_, v_mod_x3f_3793_, v_id_3794_, v_minIndexable_3795_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
return v___x_4234_;
}
else
{
lean_object* v___x_4236_; 
lean_dec(v_id_3794_);
lean_dec(v_mod_x3f_3793_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
if (v_isShared_4213_ == 0)
{
lean_ctor_set_tag(v___x_4212_, 1);
lean_ctor_set(v___x_4212_, 0, v_a_4200_);
v___x_4236_ = v___x_4212_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4200_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
lean_dec(v___x_4206_);
lean_dec(v_a_4200_);
lean_dec(v_id_3794_);
lean_dec(v_mod_x3f_3793_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v_a_4239_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4209_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4209_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
else
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec_ref_known(v_a_4208_, 1);
lean_dec(v___x_4206_);
lean_dec(v_a_4200_);
lean_dec(v_mod_x3f_3793_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v___x_4247_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23);
lean_inc(v_id_3794_);
v___x_4248_ = l_Lean_MessageData_ofSyntax(v_id_3794_);
v___x_4249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4247_);
lean_ctor_set(v___x_4249_, 1, v___x_4248_);
v___x_4250_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25);
v___x_4251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4249_);
lean_ctor_set(v___x_4251_, 1, v___x_4250_);
v___x_4252_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3794_, v___x_4251_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
lean_dec(v_id_3794_);
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4252_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4252_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_dec(v___x_4206_);
lean_dec(v_a_4200_);
lean_dec(v_id_3794_);
lean_dec(v_mod_x3f_3793_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v_a_4261_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4207_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4207_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
else
{
lean_object* v___x_4270_; 
lean_dec(v_id_3794_);
lean_dec(v_mod_x3f_3793_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
if (v_isShared_4203_ == 0)
{
v___x_4270_ = v___x_4202_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4200_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
}
v___jp_3805_:
{
uint8_t v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = 0;
lean_inc(v___y_3807_);
v___x_3815_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3807_, v___x_3814_, v___y_3812_, v___y_3813_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3815_, 1);
if (lean_obj_tag(v_a_3816_) == 1)
{
lean_object* v_val_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_dec(v___y_3807_);
v_val_3817_ = lean_ctor_get(v_a_3816_, 0);
lean_inc_n(v_val_3817_, 2);
lean_dec_ref_known(v_a_3816_, 1);
v___x_3818_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3791_, v_val_3817_, v___x_3814_);
v___x_3819_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3817_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3830_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3822_ = v___x_3819_;
v_isShared_3823_ = v_isSharedCheck_3830_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3819_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3830_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
if (lean_obj_tag(v_a_3820_) == 1)
{
lean_object* v_val_3824_; lean_object* v_ctors_3825_; lean_object* v___x_3826_; 
lean_del_object(v___x_3822_);
v_val_3824_ = lean_ctor_get(v_a_3820_, 0);
lean_inc(v_val_3824_);
lean_dec_ref_known(v_a_3820_, 1);
v_ctors_3825_ = lean_ctor_get(v_val_3824_, 4);
lean_inc(v_ctors_3825_);
lean_dec(v_val_3824_);
v___x_3826_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3792_, v_id_3794_, v_minIndexable_3795_, v_ctors_3825_, v___x_3818_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
lean_dec(v_ctors_3825_);
lean_dec(v_p_3792_);
return v___x_3826_;
}
else
{
lean_object* v___x_3828_; 
lean_dec(v_a_3820_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 0, v___x_3818_);
v___x_3828_ = v___x_3822_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3818_);
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
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec_ref(v___x_3818_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
v_a_3831_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3819_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3819_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
else
{
lean_object* v_toCold_3839_; lean_object* v_currRecDepth_3840_; lean_object* v_ref_3841_; uint16_t v_optionFlags_3842_; uint8_t v_suppressElabErrors_3843_; uint8_t v_isRecordingDeps_3844_; lean_object* v___x_3845_; lean_object* v_ref_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
lean_dec(v_a_3816_);
v_toCold_3839_ = lean_ctor_get(v___y_3812_, 0);
v_currRecDepth_3840_ = lean_ctor_get(v___y_3812_, 1);
v_ref_3841_ = lean_ctor_get(v___y_3812_, 2);
v_optionFlags_3842_ = lean_ctor_get_uint16(v___y_3812_, sizeof(void*)*3);
v_suppressElabErrors_3843_ = lean_ctor_get_uint8(v___y_3812_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3844_ = lean_ctor_get_uint8(v___y_3812_, sizeof(void*)*3 + 3);
v___x_3845_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_ref_3846_ = l_Lean_replaceRef(v_p_3792_, v_ref_3841_);
lean_dec(v_p_3792_);
lean_inc(v_currRecDepth_3840_);
lean_inc_ref(v_toCold_3839_);
v___x_3847_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3847_, 0, v_toCold_3839_);
lean_ctor_set(v___x_3847_, 1, v_currRecDepth_3840_);
lean_ctor_set(v___x_3847_, 2, v_ref_3846_);
lean_ctor_set_uint16(v___x_3847_, sizeof(void*)*3, v_optionFlags_3842_);
lean_ctor_set_uint8(v___x_3847_, sizeof(void*)*3 + 2, v_suppressElabErrors_3843_);
lean_ctor_set_uint8(v___x_3847_, sizeof(void*)*3 + 3, v_isRecordingDeps_3844_);
v___x_3848_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3791_, v_id_3794_, v___y_3807_, v___x_3845_, v_minIndexable_3795_, v___y_3806_, v___y_3806_, v___y_3810_, v___y_3811_, v___x_3847_, v___y_3813_);
lean_dec_ref_known(v___x_3847_, 3);
return v___x_3848_;
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec(v___y_3807_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v_a_3849_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3815_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3815_);
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
v___jp_3857_:
{
lean_object* v___x_3866_; 
v___x_3866_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3795_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
lean_dec_ref_known(v___x_3866_, 1);
v___x_3867_ = l_Lean_Meta_Grind_grindExt;
v___x_3868_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3867_, v___y_3865_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v___x_3868_, 1);
lean_inc(v___y_3858_);
v___x_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3870_, 0, v___y_3858_);
v___x_3871_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3869_, v___x_3870_);
lean_dec_ref_known(v___x_3870_, 1);
lean_dec(v_a_3869_);
v___x_3872_ = lean_box(0);
v___x_3873_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3859_, v___x_3871_, v___x_3872_);
lean_dec(v___y_3859_);
v___x_3874_ = l_List_isEmpty___redArg(v___x_3873_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; 
lean_dec(v___y_3858_);
lean_dec(v_p_3792_);
v___x_3875_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3873_, v_params_3791_);
lean_dec(v___x_3873_);
return v___x_3875_;
}
else
{
lean_object* v___x_3876_; uint8_t v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_dec(v___x_3873_);
lean_dec_ref(v_params_3791_);
v___x_3876_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3877_ = 0;
v___x_3878_ = l_Lean_MessageData_ofConstName(v___y_3858_, v___x_3877_);
v___x_3879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3876_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
v___x_3880_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3879_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___x_3882_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3792_, v___x_3881_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
lean_dec(v_p_3792_);
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
lean_dec(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v_a_3891_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3868_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3868_);
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
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_dec(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v_a_3899_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3866_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3866_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
v___jp_3907_:
{
lean_object* v___x_3914_; 
v___x_3914_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3795_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_toCold_3915_; lean_object* v_currRecDepth_3916_; lean_object* v_ref_3917_; uint16_t v_optionFlags_3918_; uint8_t v_suppressElabErrors_3919_; uint8_t v_isRecordingDeps_3920_; lean_object* v_ref_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
lean_dec_ref_known(v___x_3914_, 1);
v_toCold_3915_ = lean_ctor_get(v___y_3912_, 0);
v_currRecDepth_3916_ = lean_ctor_get(v___y_3912_, 1);
v_ref_3917_ = lean_ctor_get(v___y_3912_, 2);
v_optionFlags_3918_ = lean_ctor_get_uint16(v___y_3912_, sizeof(void*)*3);
v_suppressElabErrors_3919_ = lean_ctor_get_uint8(v___y_3912_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3920_ = lean_ctor_get_uint8(v___y_3912_, sizeof(void*)*3 + 3);
v_ref_3921_ = l_Lean_replaceRef(v_p_3792_, v_ref_3917_);
lean_dec(v_p_3792_);
lean_inc(v_currRecDepth_3916_);
lean_inc_ref(v_toCold_3915_);
v___x_3922_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3922_, 0, v_toCold_3915_);
lean_ctor_set(v___x_3922_, 1, v_currRecDepth_3916_);
lean_ctor_set(v___x_3922_, 2, v_ref_3921_);
lean_ctor_set_uint16(v___x_3922_, sizeof(void*)*3, v_optionFlags_3918_);
lean_ctor_set_uint8(v___x_3922_, sizeof(void*)*3 + 2, v_suppressElabErrors_3919_);
lean_ctor_set_uint8(v___x_3922_, sizeof(void*)*3 + 3, v_isRecordingDeps_3920_);
lean_inc(v___y_3909_);
v___x_3923_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3909_, v___y_3908_, v___x_3922_, v___y_3913_);
lean_dec_ref_known(v___x_3922_, 3);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3931_; 
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; 
v_unused_3932_ = lean_ctor_get(v___x_3923_, 0);
lean_dec(v_unused_3932_);
v___x_3925_ = v___x_3923_;
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
else
{
lean_dec(v___x_3923_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3927_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3791_, v___y_3909_, v___y_3908_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3927_);
v___x_3929_ = v___x_3925_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3927_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec(v___y_3909_);
lean_dec_ref(v_params_3791_);
v_a_3933_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3923_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3923_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
lean_dec(v___y_3909_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v_a_3941_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3914_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3914_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
v___jp_3949_:
{
lean_object* v_ctors_3957_; lean_object* v___x_3958_; 
v_ctors_3957_ = lean_ctor_get(v___y_3950_, 4);
lean_inc(v_ctors_3957_);
lean_dec_ref(v___y_3950_);
v___x_3958_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3792_, v_id_3794_, v_minIndexable_3795_, v_ctors_3957_, v_params_3791_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v_ctors_3957_);
lean_dec(v_p_3792_);
return v___x_3958_;
}
v___jp_3959_:
{
uint8_t v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = 1;
lean_inc(v_a_3960_);
v___x_3962_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_3960_, v___x_3961_, v_a_3798_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_dec_ref_known(v___x_3962_, 1);
if (lean_obj_tag(v_mod_x3f_3793_) == 1)
{
lean_object* v_val_3963_; lean_object* v___x_3964_; 
v_val_3963_ = lean_ctor_get(v_mod_x3f_3793_, 0);
lean_inc(v_val_3963_);
lean_dec_ref_known(v_mod_x3f_3793_, 1);
v___x_3964_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_3963_, v_a_3802_, v_a_3803_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_4167_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_3967_ = v___x_3964_;
v_isShared_3968_ = v_isSharedCheck_4167_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3964_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_4167_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
switch(lean_obj_tag(v_a_3965_))
{
case 0:
{
lean_object* v_k_3969_; 
lean_del_object(v___x_3967_);
v_k_3969_ = lean_ctor_get(v_a_3965_, 0);
lean_inc(v_k_3969_);
lean_dec_ref_known(v_a_3965_, 1);
if (lean_obj_tag(v_k_3969_) == 9)
{
lean_dec(v_id_3794_);
if (v_only_3796_ == 0)
{
lean_object* v_toCold_3970_; lean_object* v_currRecDepth_3971_; lean_object* v_ref_3972_; uint16_t v_optionFlags_3973_; uint8_t v_suppressElabErrors_3974_; uint8_t v_isRecordingDeps_3975_; lean_object* v_ref_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v_toCold_3970_ = lean_ctor_get(v_a_3802_, 0);
v_currRecDepth_3971_ = lean_ctor_get(v_a_3802_, 1);
v_ref_3972_ = lean_ctor_get(v_a_3802_, 2);
v_optionFlags_3973_ = lean_ctor_get_uint16(v_a_3802_, sizeof(void*)*3);
v_suppressElabErrors_3974_ = lean_ctor_get_uint8(v_a_3802_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3975_ = lean_ctor_get_uint8(v_a_3802_, sizeof(void*)*3 + 3);
v_ref_3976_ = l_Lean_replaceRef(v_p_3792_, v_ref_3972_);
lean_inc(v_currRecDepth_3971_);
lean_inc_ref(v_toCold_3970_);
v___x_3977_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3977_, 0, v_toCold_3970_);
lean_ctor_set(v___x_3977_, 1, v_currRecDepth_3971_);
lean_ctor_set(v___x_3977_, 2, v_ref_3976_);
lean_ctor_set_uint16(v___x_3977_, sizeof(void*)*3, v_optionFlags_3973_);
lean_ctor_set_uint8(v___x_3977_, sizeof(void*)*3 + 2, v_suppressElabErrors_3974_);
lean_ctor_set_uint8(v___x_3977_, sizeof(void*)*3 + 3, v_isRecordingDeps_3975_);
v___x_3978_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_3977_, v_a_3803_);
lean_dec_ref_known(v___x_3977_, 3);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_dec_ref_known(v___x_3978_, 1);
v___y_3858_ = v_a_3960_;
v___y_3859_ = v_k_3969_;
v___y_3860_ = v_a_3798_;
v___y_3861_ = v_a_3799_;
v___y_3862_ = v_a_3800_;
v___y_3863_ = v_a_3801_;
v___y_3864_ = v_a_3802_;
v___y_3865_ = v_a_3803_;
goto v___jp_3857_;
}
else
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3986_; 
lean_dec(v_a_3960_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3981_ = v___x_3978_;
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3978_);
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
else
{
v___y_3858_ = v_a_3960_;
v___y_3859_ = v_k_3969_;
v___y_3860_ = v_a_3798_;
v___y_3861_ = v_a_3799_;
v___y_3862_ = v_a_3800_;
v___y_3863_ = v_a_3801_;
v___y_3864_ = v_a_3802_;
v___y_3865_ = v_a_3803_;
goto v___jp_3857_;
}
}
else
{
lean_object* v_toCold_3987_; lean_object* v_currRecDepth_3988_; lean_object* v_ref_3989_; uint16_t v_optionFlags_3990_; uint8_t v_suppressElabErrors_3991_; uint8_t v_isRecordingDeps_3992_; uint8_t v___x_3993_; lean_object* v_ref_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v_toCold_3987_ = lean_ctor_get(v_a_3802_, 0);
v_currRecDepth_3988_ = lean_ctor_get(v_a_3802_, 1);
v_ref_3989_ = lean_ctor_get(v_a_3802_, 2);
v_optionFlags_3990_ = lean_ctor_get_uint16(v_a_3802_, sizeof(void*)*3);
v_suppressElabErrors_3991_ = lean_ctor_get_uint8(v_a_3802_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3992_ = lean_ctor_get_uint8(v_a_3802_, sizeof(void*)*3 + 3);
v___x_3993_ = 0;
v_ref_3994_ = l_Lean_replaceRef(v_p_3792_, v_ref_3989_);
lean_dec(v_p_3792_);
lean_inc(v_currRecDepth_3988_);
lean_inc_ref(v_toCold_3987_);
v___x_3995_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3995_, 0, v_toCold_3987_);
lean_ctor_set(v___x_3995_, 1, v_currRecDepth_3988_);
lean_ctor_set(v___x_3995_, 2, v_ref_3994_);
lean_ctor_set_uint16(v___x_3995_, sizeof(void*)*3, v_optionFlags_3990_);
lean_ctor_set_uint8(v___x_3995_, sizeof(void*)*3 + 2, v_suppressElabErrors_3991_);
lean_ctor_set_uint8(v___x_3995_, sizeof(void*)*3 + 3, v_isRecordingDeps_3992_);
v___x_3996_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3791_, v_id_3794_, v_a_3960_, v_k_3969_, v_minIndexable_3795_, v___x_3993_, v___x_3961_, v_a_3800_, v_a_3801_, v___x_3995_, v_a_3803_);
lean_dec_ref_known(v___x_3995_, 3);
return v___x_3996_;
}
}
case 1:
{
lean_del_object(v___x_3967_);
lean_dec(v_id_3794_);
if (v_incremental_3797_ == 0)
{
uint8_t v_eager_3997_; 
v_eager_3997_ = lean_ctor_get_uint8(v_a_3965_, 0);
lean_dec_ref_known(v_a_3965_, 0);
v___y_3908_ = v_eager_3997_;
v___y_3909_ = v_a_3960_;
v___y_3910_ = v_a_3800_;
v___y_3911_ = v_a_3801_;
v___y_3912_ = v_a_3802_;
v___y_3913_ = v_a_3803_;
goto v___jp_3907_;
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec_ref_known(v_a_3965_, 0);
lean_dec(v_a_3960_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v___x_3998_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3999_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_3998_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3999_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3999_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
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
case 2:
{
uint8_t v___x_4008_; lean_object* v___x_4009_; 
lean_del_object(v___x_3967_);
v___x_4008_ = 0;
lean_inc(v_a_3960_);
v___x_4009_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3960_, v___x_4008_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___x_4009_, 1);
if (lean_obj_tag(v_a_4010_) == 1)
{
lean_dec(v_a_3960_);
if (v_incremental_3797_ == 0)
{
lean_object* v_val_4011_; 
v_val_4011_ = lean_ctor_get(v_a_4010_, 0);
lean_inc(v_val_4011_);
lean_dec_ref_known(v_a_4010_, 1);
v___y_3950_ = v_val_4011_;
v___y_3951_ = v_a_3798_;
v___y_3952_ = v_a_3799_;
v___y_3953_ = v_a_3800_;
v___y_3954_ = v_a_3801_;
v___y_3955_ = v_a_3802_;
v___y_3956_ = v_a_3803_;
goto v___jp_3949_;
}
else
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec_ref_known(v_a_4010_, 1);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v___x_4012_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_4013_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4012_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_4013_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_4013_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
else
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec(v_a_4010_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v___x_4022_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_4023_ = l_Lean_MessageData_ofConstName(v_a_3960_, v___x_4008_);
v___x_4024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4022_);
lean_ctor_set(v___x_4024_, 1, v___x_4023_);
v___x_4025_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_4026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4024_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
v___x_4027_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4026_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
lean_dec(v_a_3960_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v_a_4036_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4009_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4009_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
case 3:
{
lean_del_object(v___x_3967_);
v___y_3806_ = v___x_3961_;
v___y_3807_ = v_a_3960_;
v___y_3808_ = v_a_3798_;
v___y_3809_ = v_a_3799_;
v___y_3810_ = v_a_3800_;
v___y_3811_ = v_a_3801_;
v___y_3812_ = v_a_3802_;
v___y_3813_ = v_a_3803_;
goto v___jp_3805_;
}
case 4:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_del_object(v___x_3967_);
lean_dec(v_a_3960_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v___x_4044_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_4045_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4044_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4045_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4045_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
case 5:
{
lean_object* v_prio_4054_; lean_object* v___x_4055_; 
lean_del_object(v___x_3967_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
v_prio_4054_ = lean_ctor_get(v_a_3965_, 0);
lean_inc(v_prio_4054_);
lean_dec_ref_known(v_a_3965_, 1);
v___x_4055_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3795_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4079_; 
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4079_ == 0)
{
lean_object* v_unused_4080_; 
v_unused_4080_ = lean_ctor_get(v___x_4055_, 0);
lean_dec(v_unused_4080_);
v___x_4057_ = v___x_4055_;
v_isShared_4058_ = v_isSharedCheck_4079_;
goto v_resetjp_4056_;
}
else
{
lean_dec(v___x_4055_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4079_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v_config_4059_; lean_object* v_extensions_4060_; lean_object* v_extra_4061_; lean_object* v_extraInj_4062_; lean_object* v_extraFacts_4063_; lean_object* v_symPrios_4064_; lean_object* v_norm_4065_; lean_object* v_normProcs_4066_; lean_object* v_anchorRefs_x3f_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4078_; 
v_config_4059_ = lean_ctor_get(v_params_3791_, 0);
v_extensions_4060_ = lean_ctor_get(v_params_3791_, 1);
v_extra_4061_ = lean_ctor_get(v_params_3791_, 2);
v_extraInj_4062_ = lean_ctor_get(v_params_3791_, 3);
v_extraFacts_4063_ = lean_ctor_get(v_params_3791_, 4);
v_symPrios_4064_ = lean_ctor_get(v_params_3791_, 5);
v_norm_4065_ = lean_ctor_get(v_params_3791_, 6);
v_normProcs_4066_ = lean_ctor_get(v_params_3791_, 7);
v_anchorRefs_x3f_4067_ = lean_ctor_get(v_params_3791_, 8);
v_isSharedCheck_4078_ = !lean_is_exclusive(v_params_3791_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4069_ = v_params_3791_;
v_isShared_4070_ = v_isSharedCheck_4078_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_anchorRefs_x3f_4067_);
lean_inc(v_normProcs_4066_);
lean_inc(v_norm_4065_);
lean_inc(v_symPrios_4064_);
lean_inc(v_extraFacts_4063_);
lean_inc(v_extraInj_4062_);
lean_inc(v_extra_4061_);
lean_inc(v_extensions_4060_);
lean_inc(v_config_4059_);
lean_dec(v_params_3791_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4078_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4071_; lean_object* v___x_4073_; 
v___x_4071_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_4064_, v_a_3960_, v_prio_4054_);
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 5, v___x_4071_);
v___x_4073_ = v___x_4069_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_config_4059_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v_extensions_4060_);
lean_ctor_set(v_reuseFailAlloc_4077_, 2, v_extra_4061_);
lean_ctor_set(v_reuseFailAlloc_4077_, 3, v_extraInj_4062_);
lean_ctor_set(v_reuseFailAlloc_4077_, 4, v_extraFacts_4063_);
lean_ctor_set(v_reuseFailAlloc_4077_, 5, v___x_4071_);
lean_ctor_set(v_reuseFailAlloc_4077_, 6, v_norm_4065_);
lean_ctor_set(v_reuseFailAlloc_4077_, 7, v_normProcs_4066_);
lean_ctor_set(v_reuseFailAlloc_4077_, 8, v_anchorRefs_x3f_4067_);
v___x_4073_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_object* v___x_4075_; 
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 0, v___x_4073_);
v___x_4075_ = v___x_4057_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v_prio_4054_);
lean_dec(v_a_3960_);
lean_dec_ref(v_params_3791_);
v_a_4081_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4055_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4055_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
case 6:
{
lean_object* v___x_4089_; 
lean_del_object(v___x_3967_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
v___x_4089_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3960_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4114_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4092_ = v___x_4089_;
v_isShared_4093_ = v_isSharedCheck_4114_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4089_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4114_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v_config_4094_; lean_object* v_extensions_4095_; lean_object* v_extra_4096_; lean_object* v_extraInj_4097_; lean_object* v_extraFacts_4098_; lean_object* v_symPrios_4099_; lean_object* v_norm_4100_; lean_object* v_normProcs_4101_; lean_object* v_anchorRefs_x3f_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4113_; 
v_config_4094_ = lean_ctor_get(v_params_3791_, 0);
v_extensions_4095_ = lean_ctor_get(v_params_3791_, 1);
v_extra_4096_ = lean_ctor_get(v_params_3791_, 2);
v_extraInj_4097_ = lean_ctor_get(v_params_3791_, 3);
v_extraFacts_4098_ = lean_ctor_get(v_params_3791_, 4);
v_symPrios_4099_ = lean_ctor_get(v_params_3791_, 5);
v_norm_4100_ = lean_ctor_get(v_params_3791_, 6);
v_normProcs_4101_ = lean_ctor_get(v_params_3791_, 7);
v_anchorRefs_x3f_4102_ = lean_ctor_get(v_params_3791_, 8);
v_isSharedCheck_4113_ = !lean_is_exclusive(v_params_3791_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4104_ = v_params_3791_;
v_isShared_4105_ = v_isSharedCheck_4113_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_anchorRefs_x3f_4102_);
lean_inc(v_normProcs_4101_);
lean_inc(v_norm_4100_);
lean_inc(v_symPrios_4099_);
lean_inc(v_extraFacts_4098_);
lean_inc(v_extraInj_4097_);
lean_inc(v_extra_4096_);
lean_inc(v_extensions_4095_);
lean_inc(v_config_4094_);
lean_dec(v_params_3791_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4113_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4106_; lean_object* v___x_4108_; 
v___x_4106_ = l_Lean_PersistentArray_push___redArg(v_extraInj_4097_, v_a_4090_);
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 3, v___x_4106_);
v___x_4108_ = v___x_4104_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_config_4094_);
lean_ctor_set(v_reuseFailAlloc_4112_, 1, v_extensions_4095_);
lean_ctor_set(v_reuseFailAlloc_4112_, 2, v_extra_4096_);
lean_ctor_set(v_reuseFailAlloc_4112_, 3, v___x_4106_);
lean_ctor_set(v_reuseFailAlloc_4112_, 4, v_extraFacts_4098_);
lean_ctor_set(v_reuseFailAlloc_4112_, 5, v_symPrios_4099_);
lean_ctor_set(v_reuseFailAlloc_4112_, 6, v_norm_4100_);
lean_ctor_set(v_reuseFailAlloc_4112_, 7, v_normProcs_4101_);
lean_ctor_set(v_reuseFailAlloc_4112_, 8, v_anchorRefs_x3f_4102_);
v___x_4108_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
lean_object* v___x_4110_; 
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 0, v___x_4108_);
v___x_4110_ = v___x_4092_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4108_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
lean_dec_ref(v_params_3791_);
v_a_4115_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4089_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4089_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
case 7:
{
lean_object* v___x_4123_; lean_object* v___x_4125_; 
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
v___x_4123_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3791_, v_a_3960_);
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 0, v___x_4123_);
v___x_4125_ = v___x_3967_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
case 8:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
lean_dec_ref_known(v_a_3965_, 0);
lean_del_object(v___x_3967_);
lean_dec(v_a_3960_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v___x_4127_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_4128_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4127_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4128_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4128_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
case 9:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
lean_del_object(v___x_3967_);
lean_dec(v_a_3960_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v___x_4137_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_4138_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4137_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4138_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4138_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
case 10:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
lean_dec_ref_known(v_a_3965_, 0);
lean_del_object(v___x_3967_);
lean_dec(v_a_3960_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v___x_4147_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_4148_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4147_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4148_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4148_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
default: 
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_del_object(v___x_3967_);
lean_dec(v_a_3960_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v___x_4157_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
v___x_4158_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4157_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4158_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4158_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v_a_3960_);
lean_dec(v_id_3794_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v_a_4168_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_3964_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_3964_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_3793_);
v___y_3806_ = v___x_3961_;
v___y_3807_ = v_a_3960_;
v___y_3808_ = v_a_3798_;
v___y_3809_ = v_a_3799_;
v___y_3810_ = v_a_3800_;
v___y_3811_ = v_a_3801_;
v___y_3812_ = v_a_3802_;
v___y_3813_ = v_a_3803_;
goto v___jp_3805_;
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_dec(v_a_3960_);
lean_dec(v_id_3794_);
lean_dec(v_mod_x3f_3793_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v_a_4176_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_3962_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_3962_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
v___jp_4184_:
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4195_; 
v_a_4186_ = lean_ctor_get(v___y_4185_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___y_4185_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4188_ = v___y_4185_;
v_isShared_4189_ = v_isSharedCheck_4195_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___y_4185_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4195_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
if (lean_obj_tag(v_a_4186_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4192_; 
lean_dec(v_id_3794_);
lean_dec(v_mod_x3f_3793_);
lean_dec(v_p_3792_);
lean_dec_ref(v_params_3791_);
v_a_4190_ = lean_ctor_get(v_a_4186_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v_a_4186_, 1);
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 0, v_a_4190_);
v___x_4192_ = v___x_4188_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4190_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
else
{
lean_object* v_a_4194_; 
lean_del_object(v___x_4188_);
v_a_4194_ = lean_ctor_get(v_a_4186_, 0);
lean_inc(v_a_4194_);
lean_dec_ref_known(v_a_4186_, 1);
v_a_3960_ = v_a_4194_;
goto v___jp_3959_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_3791_ = stack[0].m_obj;
lean_object* v_p_3792_ = stack[1].m_obj;
lean_object* v_mod_x3f_3793_ = stack[2].m_obj;
lean_object* v_id_3794_ = stack[3].m_obj;
uint8_t v_minIndexable_3795_ = stack[4].m_num;
uint8_t v_only_3796_ = stack[5].m_num;
uint8_t v_incremental_3797_ = stack[6].m_num;
lean_object* v_a_3798_ = stack[7].m_obj;
lean_object* v_a_3799_ = stack[8].m_obj;
lean_object* v_a_3800_ = stack[9].m_obj;
lean_object* v_a_3801_ = stack[10].m_obj;
lean_object* v_a_3802_ = stack[11].m_obj;
lean_object* v_a_3803_ = stack[12].m_obj;
lean_object* v_res_4275_;
v_res_4275_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_3791_, v_p_3792_, v_mod_x3f_3793_, v_id_3794_, v_minIndexable_3795_, v_only_3796_, v_incremental_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
stack->m_obj
 = v_res_4275_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4276_, lean_object* v_p_4277_, lean_object* v_mod_x3f_4278_, lean_object* v_id_4279_, lean_object* v_minIndexable_4280_, lean_object* v_only_4281_, lean_object* v_incremental_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_){
_start:
{
uint8_t v_minIndexable_boxed_4290_; uint8_t v_only_boxed_4291_; uint8_t v_incremental_boxed_4292_; lean_object* v_res_4293_; 
v_minIndexable_boxed_4290_ = lean_unbox(v_minIndexable_4280_);
v_only_boxed_4291_ = lean_unbox(v_only_4281_);
v_incremental_boxed_4292_ = lean_unbox(v_incremental_4282_);
v_res_4293_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4276_, v_p_4277_, v_mod_x3f_4278_, v_id_4279_, v_minIndexable_boxed_4290_, v_only_boxed_4291_, v_incremental_boxed_4292_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
lean_dec(v_a_4288_);
lean_dec_ref(v_a_4287_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
lean_dec(v_a_4284_);
lean_dec_ref(v_a_4283_);
return v_res_4293_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4294_, lean_object* v_id_4295_, uint8_t v_minIndexable_4296_, lean_object* v_as_4297_, lean_object* v_as_x27_4298_, lean_object* v_b_4299_, lean_object* v_a_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4294_, v_id_4295_, v_minIndexable_4296_, v_as_x27_4298_, v_b_4299_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
return v___x_4308_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4294_ = stack[0].m_obj;
lean_object* v_id_4295_ = stack[1].m_obj;
uint8_t v_minIndexable_4296_ = stack[2].m_num;
lean_object* v_as_4297_ = stack[3].m_obj;
lean_object* v_as_x27_4298_ = stack[4].m_obj;
lean_object* v_b_4299_ = stack[5].m_obj;
lean_object* v___y_4301_ = stack[7].m_obj;
lean_object* v___y_4302_ = stack[8].m_obj;
lean_object* v___y_4303_ = stack[9].m_obj;
lean_object* v___y_4304_ = stack[10].m_obj;
lean_object* v___y_4305_ = stack[11].m_obj;
lean_object* v___y_4306_ = stack[12].m_obj;
lean_object* v_res_4309_;
v_res_4309_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4294_, v_id_4295_, v_minIndexable_4296_, v_as_4297_, v_as_x27_4298_, v_b_4299_, lean_box(0), v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
stack->m_obj
 = v_res_4309_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4310_, lean_object* v_id_4311_, lean_object* v_minIndexable_4312_, lean_object* v_as_4313_, lean_object* v_as_x27_4314_, lean_object* v_b_4315_, lean_object* v_a_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
uint8_t v_minIndexable_boxed_4324_; lean_object* v_res_4325_; 
v_minIndexable_boxed_4324_ = lean_unbox(v_minIndexable_4312_);
v_res_4325_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4310_, v_id_4311_, v_minIndexable_boxed_4324_, v_as_4313_, v_as_x27_4314_, v_b_4315_, v_a_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v_as_x27_4314_);
lean_dec(v_as_4313_);
lean_dec(v_p_4310_);
return v_res_4325_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4326_, lean_object* v_as_x27_4327_, lean_object* v_b_4328_, lean_object* v_a_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; 
v___x_4337_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4327_, v_b_4328_);
return v___x_4337_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4326_ = stack[0].m_obj;
lean_object* v_as_x27_4327_ = stack[1].m_obj;
lean_object* v_b_4328_ = stack[2].m_obj;
lean_object* v___y_4330_ = stack[4].m_obj;
lean_object* v___y_4331_ = stack[5].m_obj;
lean_object* v___y_4332_ = stack[6].m_obj;
lean_object* v___y_4333_ = stack[7].m_obj;
lean_object* v___y_4334_ = stack[8].m_obj;
lean_object* v___y_4335_ = stack[9].m_obj;
lean_object* v_res_4338_;
v_res_4338_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4326_, v_as_x27_4327_, v_b_4328_, lean_box(0), v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
stack->m_obj
 = v_res_4338_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4339_, lean_object* v_as_x27_4340_, lean_object* v_b_4341_, lean_object* v_a_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4339_, v_as_x27_4340_, v_b_4341_, v_a_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v_as_x27_4340_);
lean_dec(v_as_4339_);
return v_res_4350_;
}
}
lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4351_, lean_object* v_ref_4352_, lean_object* v_msg_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4352_, v_msg_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
return v___x_4361_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4352_ = stack[1].m_obj;
lean_object* v_msg_4353_ = stack[2].m_obj;
lean_object* v___y_4354_ = stack[3].m_obj;
lean_object* v___y_4355_ = stack[4].m_obj;
lean_object* v___y_4356_ = stack[5].m_obj;
lean_object* v___y_4357_ = stack[6].m_obj;
lean_object* v___y_4358_ = stack[7].m_obj;
lean_object* v___y_4359_ = stack[8].m_obj;
lean_object* v_res_4362_;
v_res_4362_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_box(0), v_ref_4352_, v_msg_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
stack->m_obj
 = v_res_4362_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4363_, lean_object* v_ref_4364_, lean_object* v_msg_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4363_, v_ref_4364_, v_msg_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v_ref_4364_);
return v_res_4373_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4374_, lean_object* v_id_4375_, uint8_t v_minIndexable_4376_, lean_object* v_as_4377_, lean_object* v_as_x27_4378_, lean_object* v_b_4379_, lean_object* v_a_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v___x_4388_; 
v___x_4388_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4374_, v_id_4375_, v_minIndexable_4376_, v_as_x27_4378_, v_b_4379_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
return v___x_4388_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_4374_ = stack[0].m_obj;
lean_object* v_id_4375_ = stack[1].m_obj;
uint8_t v_minIndexable_4376_ = stack[2].m_num;
lean_object* v_as_4377_ = stack[3].m_obj;
lean_object* v_as_x27_4378_ = stack[4].m_obj;
lean_object* v_b_4379_ = stack[5].m_obj;
lean_object* v___y_4381_ = stack[7].m_obj;
lean_object* v___y_4382_ = stack[8].m_obj;
lean_object* v___y_4383_ = stack[9].m_obj;
lean_object* v___y_4384_ = stack[10].m_obj;
lean_object* v___y_4385_ = stack[11].m_obj;
lean_object* v___y_4386_ = stack[12].m_obj;
lean_object* v_res_4389_;
v_res_4389_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4374_, v_id_4375_, v_minIndexable_4376_, v_as_4377_, v_as_x27_4378_, v_b_4379_, lean_box(0), v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
stack->m_obj
 = v_res_4389_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4390_, lean_object* v_id_4391_, lean_object* v_minIndexable_4392_, lean_object* v_as_4393_, lean_object* v_as_x27_4394_, lean_object* v_b_4395_, lean_object* v_a_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
uint8_t v_minIndexable_boxed_4404_; lean_object* v_res_4405_; 
v_minIndexable_boxed_4404_ = lean_unbox(v_minIndexable_4392_);
v_res_4405_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4390_, v_id_4391_, v_minIndexable_boxed_4404_, v_as_4393_, v_as_x27_4394_, v_b_4395_, v_a_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec(v___y_4398_);
lean_dec_ref(v___y_4397_);
lean_dec(v_as_x27_4394_);
lean_dec(v_as_4393_);
lean_dec(v_p_4390_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4406_, lean_object* v_t_4407_, lean_object* v_k_4408_){
_start:
{
lean_object* v___x_4409_; 
v___x_4409_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4407_, v_k_4408_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4410_, lean_object* v_t_4411_, lean_object* v_k_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4410_, v_t_4411_, v_k_4412_);
lean_dec(v_k_4412_);
lean_dec(v_t_4411_);
return v_res_4413_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4414_, uint8_t v_skipAuxDecl_4415_, lean_object* v_auxDeclToFullName_4416_, lean_object* v___x_4417_, lean_object* v_givenNameView_4418_, lean_object* v_as_4419_, lean_object* v_i_4420_, lean_object* v_a_4421_){
_start:
{
lean_object* v___x_4422_; 
v___x_4422_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4414_, v_skipAuxDecl_4415_, v_auxDeclToFullName_4416_, v___x_4417_, v_givenNameView_4418_, v_as_4419_, v_i_4420_);
return v___x_4422_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_givenName_4414_ = stack[0].m_obj;
uint8_t v_skipAuxDecl_4415_ = stack[1].m_num;
lean_object* v_auxDeclToFullName_4416_ = stack[2].m_obj;
lean_object* v___x_4417_ = stack[3].m_obj;
lean_object* v_givenNameView_4418_ = stack[4].m_obj;
lean_object* v_as_4419_ = stack[5].m_obj;
lean_object* v_i_4420_ = stack[6].m_obj;
lean_object* v_res_4423_;
v_res_4423_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4414_, v_skipAuxDecl_4415_, v_auxDeclToFullName_4416_, v___x_4417_, v_givenNameView_4418_, v_as_4419_, v_i_4420_, lean_box(0));
stack->m_obj
 = v_res_4423_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4424_, lean_object* v_skipAuxDecl_4425_, lean_object* v_auxDeclToFullName_4426_, lean_object* v___x_4427_, lean_object* v_givenNameView_4428_, lean_object* v_as_4429_, lean_object* v_i_4430_, lean_object* v_a_4431_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4432_; lean_object* v_res_4433_; 
v_skipAuxDecl_boxed_4432_ = lean_unbox(v_skipAuxDecl_4425_);
v_res_4433_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4424_, v_skipAuxDecl_boxed_4432_, v_auxDeclToFullName_4426_, v___x_4427_, v_givenNameView_4428_, v_as_4429_, v_i_4430_, v_a_4431_);
lean_dec_ref(v_as_4429_);
lean_dec(v_auxDeclToFullName_4426_);
lean_dec(v_givenName_4424_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4434_, lean_object* v_givenName_4435_, lean_object* v_as_4436_, lean_object* v_i_4437_, lean_object* v_a_4438_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4434_, v_givenName_4435_, v_as_4436_, v_i_4437_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4440_, lean_object* v_givenName_4441_, lean_object* v_as_4442_, lean_object* v_i_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4440_, v_givenName_4441_, v_as_4442_, v_i_4443_, v_a_4444_);
lean_dec_ref(v_as_4442_);
lean_dec(v_givenName_4441_);
lean_dec(v_localDecl_x3f_4440_);
return v_res_4445_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4446_, uint8_t v_skipAuxDecl_4447_, lean_object* v_auxDeclToFullName_4448_, lean_object* v___x_4449_, lean_object* v_givenNameView_4450_, lean_object* v_as_4451_, lean_object* v_i_4452_, lean_object* v_a_4453_){
_start:
{
lean_object* v___x_4454_; 
v___x_4454_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4446_, v_skipAuxDecl_4447_, v_auxDeclToFullName_4448_, v___x_4449_, v_givenNameView_4450_, v_as_4451_, v_i_4452_);
return v___x_4454_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_givenName_4446_ = stack[0].m_obj;
uint8_t v_skipAuxDecl_4447_ = stack[1].m_num;
lean_object* v_auxDeclToFullName_4448_ = stack[2].m_obj;
lean_object* v___x_4449_ = stack[3].m_obj;
lean_object* v_givenNameView_4450_ = stack[4].m_obj;
lean_object* v_as_4451_ = stack[5].m_obj;
lean_object* v_i_4452_ = stack[6].m_obj;
lean_object* v_res_4455_;
v_res_4455_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4446_, v_skipAuxDecl_4447_, v_auxDeclToFullName_4448_, v___x_4449_, v_givenNameView_4450_, v_as_4451_, v_i_4452_, lean_box(0));
stack->m_obj
 = v_res_4455_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4456_, lean_object* v_skipAuxDecl_4457_, lean_object* v_auxDeclToFullName_4458_, lean_object* v___x_4459_, lean_object* v_givenNameView_4460_, lean_object* v_as_4461_, lean_object* v_i_4462_, lean_object* v_a_4463_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4464_; lean_object* v_res_4465_; 
v_skipAuxDecl_boxed_4464_ = lean_unbox(v_skipAuxDecl_4457_);
v_res_4465_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4456_, v_skipAuxDecl_boxed_4464_, v_auxDeclToFullName_4458_, v___x_4459_, v_givenNameView_4460_, v_as_4461_, v_i_4462_, v_a_4463_);
lean_dec_ref(v_as_4461_);
lean_dec(v_auxDeclToFullName_4458_);
lean_dec(v_givenName_4456_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4466_, lean_object* v_givenName_4467_, lean_object* v_as_4468_, lean_object* v_i_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v___x_4471_; 
v___x_4471_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4466_, v_givenName_4467_, v_as_4468_, v_i_4469_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4472_, lean_object* v_givenName_4473_, lean_object* v_as_4474_, lean_object* v_i_4475_, lean_object* v_a_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4472_, v_givenName_4473_, v_as_4474_, v_i_4475_, v_a_4476_);
lean_dec_ref(v_as_4474_);
lean_dec(v_givenName_4473_);
lean_dec(v_localDecl_x3f_4472_);
return v_res_4477_;
}
}
lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v___x_4486_; 
v___x_4486_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4478_, v___y_4483_);
return v___x_4486_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_4478_ = stack[0].m_obj;
lean_object* v___y_4479_ = stack[1].m_obj;
lean_object* v___y_4480_ = stack[2].m_obj;
lean_object* v___y_4481_ = stack[3].m_obj;
lean_object* v___y_4482_ = stack[4].m_obj;
lean_object* v___y_4483_ = stack[5].m_obj;
lean_object* v___y_4484_ = stack[6].m_obj;
lean_object* v_res_4487_;
v_res_4487_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
stack->m_obj
 = v_res_4487_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec_ref(v_opt_4488_);
return v_res_4496_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4497_, lean_object* v_msgData_4498_, uint8_t v_severity_4499_, uint8_t v_isSilent_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4497_, v_msgData_4498_, v_severity_4499_, v_isSilent_4500_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
return v___x_4508_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4497_ = stack[0].m_obj;
lean_object* v_msgData_4498_ = stack[1].m_obj;
uint8_t v_severity_4499_ = stack[2].m_num;
uint8_t v_isSilent_4500_ = stack[3].m_num;
lean_object* v___y_4501_ = stack[4].m_obj;
lean_object* v___y_4502_ = stack[5].m_obj;
lean_object* v___y_4503_ = stack[6].m_obj;
lean_object* v___y_4504_ = stack[7].m_obj;
lean_object* v___y_4505_ = stack[8].m_obj;
lean_object* v___y_4506_ = stack[9].m_obj;
lean_object* v_res_4509_;
v_res_4509_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4497_, v_msgData_4498_, v_severity_4499_, v_isSilent_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
stack->m_obj
 = v_res_4509_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4510_, lean_object* v_msgData_4511_, lean_object* v_severity_4512_, lean_object* v_isSilent_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
uint8_t v_severity_boxed_4521_; uint8_t v_isSilent_boxed_4522_; lean_object* v_res_4523_; 
v_severity_boxed_4521_ = lean_unbox(v_severity_4512_);
v_isSilent_boxed_4522_ = lean_unbox(v_isSilent_4513_);
v_res_4523_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4510_, v_msgData_4511_, v_severity_boxed_4521_, v_isSilent_boxed_4522_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v_ref_4510_);
return v_res_4523_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4524_, uint8_t v___x_4525_, lean_object* v_b_4526_, lean_object* v_____r_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4535_ = lean_box(0);
v___x_4536_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4524_, v___x_4535_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4538_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc_n(v_a_4537_, 2);
lean_dec_ref_known(v___x_4536_, 1);
v___x_4538_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4537_, v___x_4525_, v___y_4528_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4538_) == 0)
{
uint8_t v___x_4539_; lean_object* v___x_4540_; 
lean_dec_ref_known(v___x_4538_, 1);
v___x_4539_ = 0;
lean_inc(v_a_4537_);
v___x_4540_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4537_, v___x_4539_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4600_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4543_ = v___x_4540_;
v_isShared_4544_ = v_isSharedCheck_4600_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4540_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4600_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
if (lean_obj_tag(v_a_4541_) == 1)
{
lean_object* v_val_4545_; lean_object* v___x_4546_; 
lean_del_object(v___x_4543_);
lean_dec(v_a_4537_);
v_val_4545_ = lean_ctor_get(v_a_4541_, 0);
lean_inc_n(v_val_4545_, 2);
lean_dec_ref_known(v_a_4541_, 1);
v___x_4546_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4545_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v___x_4547_; 
lean_dec_ref_known(v___x_4546_, 1);
v___x_4547_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4526_, v_val_4545_, v___y_4532_, v___y_4533_);
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
else
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
lean_dec(v_val_4545_);
lean_dec_ref(v_b_4526_);
v_a_4566_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4546_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4546_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
else
{
uint8_t v___x_4574_; 
lean_dec(v_a_4541_);
lean_inc(v_a_4537_);
v___x_4574_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4526_, v_a_4537_);
if (v___x_4574_ == 0)
{
lean_object* v___x_4575_; 
lean_del_object(v___x_4543_);
v___x_4575_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4526_, v_a_4537_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4585_; 
v_a_4576_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4578_ = v___x_4575_;
v_isShared_4579_ = v_isSharedCheck_4585_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___x_4575_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4585_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4583_; 
v___x_4580_ = lean_box(0);
v___x_4581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4580_);
lean_ctor_set(v___x_4581_, 1, v_a_4576_);
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 0, v___x_4581_);
v___x_4583_ = v___x_4578_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4581_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
return v___x_4583_;
}
}
}
else
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
v_a_4586_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4588_ = v___x_4575_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4575_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4586_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
}
else
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4598_; 
v___x_4594_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4526_, v_a_4537_);
v___x_4595_ = lean_box(0);
v___x_4596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
lean_ctor_set(v___x_4596_, 1, v___x_4594_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v___x_4596_);
v___x_4598_ = v___x_4543_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
lean_dec(v_a_4537_);
lean_dec_ref(v_b_4526_);
v_a_4601_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4540_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4540_);
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
lean_dec(v_a_4537_);
lean_dec_ref(v_b_4526_);
v_a_4609_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4611_ = v___x_4538_;
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4538_);
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
else
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4624_; 
lean_dec_ref(v_b_4526_);
v_a_4617_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4619_ = v___x_4536_;
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4536_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4622_; 
if (v_isShared_4620_ == 0)
{
v___x_4622_ = v___x_4619_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4524_ = stack[0].m_obj;
uint8_t v___x_4525_ = stack[1].m_num;
lean_object* v_b_4526_ = stack[2].m_obj;
lean_object* v_____r_4527_ = stack[3].m_obj;
lean_object* v___y_4528_ = stack[4].m_obj;
lean_object* v___y_4529_ = stack[5].m_obj;
lean_object* v___y_4530_ = stack[6].m_obj;
lean_object* v___y_4531_ = stack[7].m_obj;
lean_object* v___y_4532_ = stack[8].m_obj;
lean_object* v___y_4533_ = stack[9].m_obj;
lean_object* v_res_4625_;
v_res_4625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4524_, v___x_4525_, v_b_4526_, v_____r_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
stack->m_obj
 = v_res_4625_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4626_, lean_object* v___x_4627_, lean_object* v_b_4628_, lean_object* v_____r_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_){
_start:
{
uint8_t v___x_17514__boxed_4637_; lean_object* v_res_4638_; 
v___x_17514__boxed_4637_ = lean_unbox(v___x_4627_);
v_res_4638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4626_, v___x_17514__boxed_4637_, v_b_4628_, v_____r_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
return v_res_4638_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4642_, lean_object* v_b_4643_, lean_object* v_a_4644_, uint8_t v___x_4645_, uint8_t v_only_4646_, uint8_t v_incremental_4647_, lean_object* v_x_4648_, lean_object* v_mod_x3f_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = lean_unsigned_to_nat(1u);
v___x_4658_ = l_Lean_Syntax_getArg(v___x_4642_, v___x_4657_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4719_; uint8_t v___x_4720_; 
v___x_4719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4658_);
v___x_4720_ = l_Lean_Syntax_isOfKind(v___x_4658_, v___x_4719_);
if (v___x_4720_ == 0)
{
lean_object* v___x_4721_; 
v___x_4721_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4643_, v_a_4644_, v_mod_x3f_4649_, v___x_4658_, v___x_4645_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4731_; 
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4724_ = v___x_4721_;
v_isShared_4725_ = v_isSharedCheck_4731_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4721_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4731_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4729_; 
v___x_4726_ = lean_box(0);
v___x_4727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4726_);
lean_ctor_set(v___x_4727_, 1, v_a_4722_);
if (v_isShared_4725_ == 0)
{
lean_ctor_set(v___x_4724_, 0, v___x_4727_);
v___x_4729_ = v___x_4724_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4727_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
else
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4739_; 
v_a_4732_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4734_ = v___x_4721_;
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4721_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4737_; 
if (v_isShared_4735_ == 0)
{
v___x_4737_ = v___x_4734_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4732_);
v___x_4737_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
return v___x_4737_;
}
}
}
}
else
{
goto v___jp_4679_;
}
}
else
{
goto v___jp_4679_;
}
v___jp_4659_:
{
lean_object* v___x_4660_; 
v___x_4660_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4643_, v_a_4644_, v_mod_x3f_4649_, v___x_4658_, v___x_4645_, v_only_4646_, v_incremental_4647_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4670_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4663_ = v___x_4660_;
v_isShared_4664_ = v_isSharedCheck_4670_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_a_4661_);
lean_dec(v___x_4660_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4670_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4668_; 
v___x_4665_ = lean_box(0);
v___x_4666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4665_);
lean_ctor_set(v___x_4666_, 1, v_a_4661_);
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 0, v___x_4666_);
v___x_4668_ = v___x_4663_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v___x_4666_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4678_; 
v_a_4671_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4673_ = v___x_4660_;
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4660_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4678_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
}
v___jp_4679_:
{
lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4680_ = l_Lean_TSyntax_getId(v___x_4658_);
v___x_4681_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4680_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4682_);
lean_dec_ref_known(v___x_4681_, 1);
if (lean_obj_tag(v_a_4682_) == 1)
{
lean_object* v_val_4683_; lean_object* v_snd_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4709_; 
v_val_4683_ = lean_ctor_get(v_a_4682_, 0);
lean_inc(v_val_4683_);
lean_dec_ref_known(v_a_4682_, 1);
v_snd_4684_ = lean_ctor_get(v_val_4683_, 1);
v_isSharedCheck_4709_ = !lean_is_exclusive(v_val_4683_);
if (v_isSharedCheck_4709_ == 0)
{
lean_object* v_unused_4710_; 
v_unused_4710_ = lean_ctor_get(v_val_4683_, 0);
lean_dec(v_unused_4710_);
v___x_4686_ = v_val_4683_;
v_isShared_4687_ = v_isSharedCheck_4709_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_snd_4684_);
lean_dec(v_val_4683_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4709_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
if (lean_obj_tag(v_snd_4684_) == 1)
{
lean_object* v___x_4688_; 
lean_dec_ref_known(v_snd_4684_, 2);
v___x_4688_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4643_, v_a_4644_, v_mod_x3f_4649_, v___x_4658_, v___x_4645_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4700_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4691_ = v___x_4688_;
v_isShared_4692_ = v_isSharedCheck_4700_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4688_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4700_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4693_; lean_object* v___x_4695_; 
v___x_4693_ = lean_box(0);
if (v_isShared_4687_ == 0)
{
lean_ctor_set(v___x_4686_, 1, v_a_4689_);
lean_ctor_set(v___x_4686_, 0, v___x_4693_);
v___x_4695_ = v___x_4686_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v___x_4693_);
lean_ctor_set(v_reuseFailAlloc_4699_, 1, v_a_4689_);
v___x_4695_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
lean_object* v___x_4697_; 
if (v_isShared_4692_ == 0)
{
lean_ctor_set(v___x_4691_, 0, v___x_4695_);
v___x_4697_ = v___x_4691_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
else
{
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
lean_del_object(v___x_4686_);
v_a_4701_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4703_ = v___x_4688_;
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v___x_4688_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4706_; 
if (v_isShared_4704_ == 0)
{
v___x_4706_ = v___x_4703_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4701_);
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
lean_del_object(v___x_4686_);
lean_dec(v_snd_4684_);
goto v___jp_4659_;
}
}
}
else
{
lean_dec(v_a_4682_);
goto v___jp_4659_;
}
}
else
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
lean_dec(v___x_4658_);
lean_dec(v_mod_x3f_4649_);
lean_dec(v_a_4644_);
lean_dec_ref(v_b_4643_);
v_a_4711_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4713_ = v___x_4681_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4681_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4716_; 
if (v_isShared_4714_ == 0)
{
v___x_4716_ = v___x_4713_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4711_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4642_ = stack[0].m_obj;
lean_object* v_b_4643_ = stack[1].m_obj;
lean_object* v_a_4644_ = stack[2].m_obj;
uint8_t v___x_4645_ = stack[3].m_num;
uint8_t v_only_4646_ = stack[4].m_num;
uint8_t v_incremental_4647_ = stack[5].m_num;
lean_object* v_x_4648_ = stack[6].m_obj;
lean_object* v_mod_x3f_4649_ = stack[7].m_obj;
lean_object* v___y_4650_ = stack[8].m_obj;
lean_object* v___y_4651_ = stack[9].m_obj;
lean_object* v___y_4652_ = stack[10].m_obj;
lean_object* v___y_4653_ = stack[11].m_obj;
lean_object* v___y_4654_ = stack[12].m_obj;
lean_object* v___y_4655_ = stack[13].m_obj;
lean_object* v_res_4740_;
v_res_4740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4642_, v_b_4643_, v_a_4644_, v___x_4645_, v_only_4646_, v_incremental_4647_, v_x_4648_, v_mod_x3f_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
stack->m_obj
 = v_res_4740_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4741_, lean_object* v_b_4742_, lean_object* v_a_4743_, lean_object* v___x_4744_, lean_object* v_only_4745_, lean_object* v_incremental_4746_, lean_object* v_x_4747_, lean_object* v_mod_x3f_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_){
_start:
{
uint8_t v___x_17842__boxed_4756_; uint8_t v_only_boxed_4757_; uint8_t v_incremental_boxed_4758_; lean_object* v_res_4759_; 
v___x_17842__boxed_4756_ = lean_unbox(v___x_4744_);
v_only_boxed_4757_ = lean_unbox(v_only_4745_);
v_incremental_boxed_4758_ = lean_unbox(v_incremental_4746_);
v_res_4759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4741_, v_b_4742_, v_a_4743_, v___x_17842__boxed_4756_, v_only_boxed_4757_, v_incremental_boxed_4758_, v_x_4747_, v_mod_x3f_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
lean_dec(v___y_4754_);
lean_dec_ref(v___y_4753_);
lean_dec(v___y_4752_);
lean_dec_ref(v___y_4751_);
lean_dec(v___y_4750_);
lean_dec_ref(v___y_4749_);
lean_dec(v___x_4741_);
return v_res_4759_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4760_, lean_object* v___x_4761_, lean_object* v_____r_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4760_, v___x_4761_, v___y_4767_, v___y_4768_);
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4780_; 
v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4773_ = v___x_4770_;
v_isShared_4774_ = v_isSharedCheck_4780_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4770_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4780_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4778_; 
v___x_4775_ = lean_box(0);
v___x_4776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4775_);
lean_ctor_set(v___x_4776_, 1, v_a_4771_);
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 0, v___x_4776_);
v___x_4778_ = v___x_4773_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4776_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
else
{
lean_object* v_a_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4788_; 
v_a_4781_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4783_ = v___x_4770_;
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_a_4781_);
lean_dec(v___x_4770_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4786_; 
if (v_isShared_4784_ == 0)
{
v___x_4786_ = v___x_4783_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4781_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_4760_ = stack[0].m_obj;
lean_object* v___x_4761_ = stack[1].m_obj;
lean_object* v_____r_4762_ = stack[2].m_obj;
lean_object* v___y_4763_ = stack[3].m_obj;
lean_object* v___y_4764_ = stack[4].m_obj;
lean_object* v___y_4765_ = stack[5].m_obj;
lean_object* v___y_4766_ = stack[6].m_obj;
lean_object* v___y_4767_ = stack[7].m_obj;
lean_object* v___y_4768_ = stack[8].m_obj;
lean_object* v_res_4789_;
v_res_4789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4760_, v___x_4761_, v_____r_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_);
stack->m_obj
 = v_res_4789_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4790_, lean_object* v___x_4791_, lean_object* v_____r_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
lean_object* v_res_4800_; 
v_res_4800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4790_, v___x_4791_, v_____r_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
lean_dec(v___y_4796_);
lean_dec_ref(v___y_4795_);
lean_dec(v___y_4794_);
lean_dec_ref(v___y_4793_);
lean_dec(v___x_4791_);
return v_res_4800_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4801_, lean_object* v_b_4802_, lean_object* v_a_4803_, uint8_t v___x_4804_, uint8_t v_only_4805_, uint8_t v_incremental_4806_, uint8_t v___x_4807_, lean_object* v_x_4808_, lean_object* v_mod_x3f_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; 
v___x_4817_ = lean_unsigned_to_nat(2u);
v___x_4818_ = l_Lean_Syntax_getArg(v___x_4801_, v___x_4817_);
if (v___x_4807_ == 0)
{
lean_object* v___x_4879_; uint8_t v___x_4880_; 
v___x_4879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4818_);
v___x_4880_ = l_Lean_Syntax_isOfKind(v___x_4818_, v___x_4879_);
if (v___x_4880_ == 0)
{
lean_object* v___x_4881_; 
v___x_4881_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4802_, v_a_4803_, v_mod_x3f_4809_, v___x_4818_, v___x_4804_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4891_; 
v_a_4882_ = lean_ctor_get(v___x_4881_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4881_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4884_ = v___x_4881_;
v_isShared_4885_ = v_isSharedCheck_4891_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4881_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4891_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4889_; 
v___x_4886_ = lean_box(0);
v___x_4887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
lean_ctor_set(v___x_4887_, 1, v_a_4882_);
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 0, v___x_4887_);
v___x_4889_ = v___x_4884_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4887_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
v_a_4892_ = lean_ctor_get(v___x_4881_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4881_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4881_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4881_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
else
{
goto v___jp_4839_;
}
}
else
{
goto v___jp_4839_;
}
v___jp_4819_:
{
lean_object* v___x_4820_; 
v___x_4820_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4802_, v_a_4803_, v_mod_x3f_4809_, v___x_4818_, v___x_4804_, v_only_4805_, v_incremental_4806_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4830_; 
v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4823_ = v___x_4820_;
v_isShared_4824_ = v_isSharedCheck_4830_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4820_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4830_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4825_ = lean_box(0);
v___x_4826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
lean_ctor_set(v___x_4826_, 1, v_a_4821_);
if (v_isShared_4824_ == 0)
{
lean_ctor_set(v___x_4823_, 0, v___x_4826_);
v___x_4828_ = v___x_4823_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4826_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
else
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
v_a_4831_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4833_ = v___x_4820_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4820_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4836_; 
if (v_isShared_4834_ == 0)
{
v___x_4836_ = v___x_4833_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
}
v___jp_4839_:
{
lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4840_ = l_Lean_TSyntax_getId(v___x_4818_);
v___x_4841_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4840_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_object* v_a_4842_; 
v_a_4842_ = lean_ctor_get(v___x_4841_, 0);
lean_inc(v_a_4842_);
lean_dec_ref_known(v___x_4841_, 1);
if (lean_obj_tag(v_a_4842_) == 1)
{
lean_object* v_val_4843_; lean_object* v_snd_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4869_; 
v_val_4843_ = lean_ctor_get(v_a_4842_, 0);
lean_inc(v_val_4843_);
lean_dec_ref_known(v_a_4842_, 1);
v_snd_4844_ = lean_ctor_get(v_val_4843_, 1);
v_isSharedCheck_4869_ = !lean_is_exclusive(v_val_4843_);
if (v_isSharedCheck_4869_ == 0)
{
lean_object* v_unused_4870_; 
v_unused_4870_ = lean_ctor_get(v_val_4843_, 0);
lean_dec(v_unused_4870_);
v___x_4846_ = v_val_4843_;
v_isShared_4847_ = v_isSharedCheck_4869_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_snd_4844_);
lean_dec(v_val_4843_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4869_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
if (lean_obj_tag(v_snd_4844_) == 1)
{
lean_object* v___x_4848_; 
lean_dec_ref_known(v_snd_4844_, 2);
v___x_4848_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4802_, v_a_4803_, v_mod_x3f_4809_, v___x_4818_, v___x_4804_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4860_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4851_ = v___x_4848_;
v_isShared_4852_ = v_isSharedCheck_4860_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4848_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4860_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4853_; lean_object* v___x_4855_; 
v___x_4853_ = lean_box(0);
if (v_isShared_4847_ == 0)
{
lean_ctor_set(v___x_4846_, 1, v_a_4849_);
lean_ctor_set(v___x_4846_, 0, v___x_4853_);
v___x_4855_ = v___x_4846_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4853_);
lean_ctor_set(v_reuseFailAlloc_4859_, 1, v_a_4849_);
v___x_4855_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
lean_object* v___x_4857_; 
if (v_isShared_4852_ == 0)
{
lean_ctor_set(v___x_4851_, 0, v___x_4855_);
v___x_4857_ = v___x_4851_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4855_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
}
else
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
lean_del_object(v___x_4846_);
v_a_4861_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4863_ = v___x_4848_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4848_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4866_; 
if (v_isShared_4864_ == 0)
{
v___x_4866_ = v___x_4863_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
else
{
lean_del_object(v___x_4846_);
lean_dec(v_snd_4844_);
goto v___jp_4819_;
}
}
}
else
{
lean_dec(v_a_4842_);
goto v___jp_4819_;
}
}
else
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4878_; 
lean_dec(v___x_4818_);
lean_dec(v_mod_x3f_4809_);
lean_dec(v_a_4803_);
lean_dec_ref(v_b_4802_);
v_a_4871_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4873_ = v___x_4841_;
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4841_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4876_; 
if (v_isShared_4874_ == 0)
{
v___x_4876_ = v___x_4873_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4801_ = stack[0].m_obj;
lean_object* v_b_4802_ = stack[1].m_obj;
lean_object* v_a_4803_ = stack[2].m_obj;
uint8_t v___x_4804_ = stack[3].m_num;
uint8_t v_only_4805_ = stack[4].m_num;
uint8_t v_incremental_4806_ = stack[5].m_num;
uint8_t v___x_4807_ = stack[6].m_num;
lean_object* v_x_4808_ = stack[7].m_obj;
lean_object* v_mod_x3f_4809_ = stack[8].m_obj;
lean_object* v___y_4810_ = stack[9].m_obj;
lean_object* v___y_4811_ = stack[10].m_obj;
lean_object* v___y_4812_ = stack[11].m_obj;
lean_object* v___y_4813_ = stack[12].m_obj;
lean_object* v___y_4814_ = stack[13].m_obj;
lean_object* v___y_4815_ = stack[14].m_obj;
lean_object* v_res_4900_;
v_res_4900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4801_, v_b_4802_, v_a_4803_, v___x_4804_, v_only_4805_, v_incremental_4806_, v___x_4807_, v_x_4808_, v_mod_x3f_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
stack->m_obj
 = v_res_4900_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4901_, lean_object* v_b_4902_, lean_object* v_a_4903_, lean_object* v___x_4904_, lean_object* v_only_4905_, lean_object* v_incremental_4906_, lean_object* v___x_4907_, lean_object* v_x_4908_, lean_object* v_mod_x3f_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_){
_start:
{
uint8_t v___x_18254__boxed_4917_; uint8_t v_only_boxed_4918_; uint8_t v_incremental_boxed_4919_; uint8_t v___x_18255__boxed_4920_; lean_object* v_res_4921_; 
v___x_18254__boxed_4917_ = lean_unbox(v___x_4904_);
v_only_boxed_4918_ = lean_unbox(v_only_4905_);
v_incremental_boxed_4919_ = lean_unbox(v_incremental_4906_);
v___x_18255__boxed_4920_ = lean_unbox(v___x_4907_);
v_res_4921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4901_, v_b_4902_, v_a_4903_, v___x_18254__boxed_4917_, v_only_boxed_4918_, v_incremental_boxed_4919_, v___x_18255__boxed_4920_, v_x_4908_, v_mod_x3f_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
lean_dec(v___y_4915_);
lean_dec_ref(v___y_4914_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec(v___y_4911_);
lean_dec_ref(v___y_4910_);
lean_dec(v___x_4901_);
return v_res_4921_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4929_; lean_object* v___x_4930_; 
v___x_4929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4930_ = l_Lean_stringToMessageData(v___x_4929_);
return v___x_4930_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13(void){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; 
v___x_4956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12));
v___x_4957_ = l_Lean_stringToMessageData(v___x_4956_);
return v___x_4957_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4963_ = l_Lean_stringToMessageData(v___x_4962_);
return v___x_4963_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4964_, uint8_t v_only_4965_, uint8_t v_incremental_4966_, lean_object* v_as_4967_, size_t v_sz_4968_, size_t v_i_4969_, lean_object* v_b_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_){
_start:
{
lean_object* v_snd_4979_; lean_object* v___y_4984_; uint8_t v___y_4985_; lean_object* v_a_4989_; lean_object* v___y_4993_; uint8_t v___x_4997_; 
v___x_4997_ = lean_usize_dec_lt(v_i_4969_, v_sz_4968_);
if (v___x_4997_ == 0)
{
lean_object* v___x_4998_; 
v___x_4998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4998_, 0, v_b_4970_);
return v___x_4998_;
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5000_; uint8_t v___x_5001_; 
v_a_4999_ = lean_array_uget_borrowed(v_as_4967_, v_i_4969_);
v___x_5000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_4999_);
v___x_5001_ = l_Lean_Syntax_isOfKind(v_a_4999_, v___x_5000_);
if (v___x_5001_ == 0)
{
lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5002_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4999_);
v___x_5003_ = l_Lean_MessageData_ofSyntax(v_a_4999_);
v___x_5004_ = l_Lean_indentD(v___x_5003_);
v___x_5005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5005_, 0, v___x_5002_);
lean_ctor_set(v___x_5005_, 1, v___x_5004_);
v___x_5006_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5005_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
if (lean_obj_tag(v___x_5006_) == 0)
{
lean_dec_ref_known(v___x_5006_, 1);
v_snd_4979_ = v_b_4970_;
goto v___jp_4978_;
}
else
{
lean_object* v_a_5007_; 
v_a_5007_ = lean_ctor_get(v___x_5006_, 0);
lean_inc(v_a_5007_);
lean_dec_ref_known(v___x_5006_, 1);
v_a_4989_ = v_a_5007_;
goto v___jp_4988_;
}
}
else
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; uint8_t v___x_5011_; 
v___x_5008_ = lean_unsigned_to_nat(0u);
v___x_5009_ = l_Lean_Syntax_getArg(v_a_4999_, v___x_5008_);
v___x_5010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_5009_);
v___x_5011_ = l_Lean_Syntax_isOfKind(v___x_5009_, v___x_5010_);
if (v___x_5011_ == 0)
{
lean_object* v___x_5012_; uint8_t v___x_5013_; 
v___x_5012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_5009_);
v___x_5013_ = l_Lean_Syntax_isOfKind(v___x_5009_, v___x_5012_);
if (v___x_5013_ == 0)
{
lean_object* v___x_5014_; uint8_t v___x_5015_; 
v___x_5014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_5009_);
v___x_5015_ = l_Lean_Syntax_isOfKind(v___x_5009_, v___x_5014_);
if (v___x_5015_ == 0)
{
lean_object* v___x_5016_; uint8_t v___x_5017_; 
v___x_5016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_5009_);
v___x_5017_ = l_Lean_Syntax_isOfKind(v___x_5009_, v___x_5016_);
if (v___x_5017_ == 0)
{
lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; 
lean_dec(v___x_5009_);
v___x_5018_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4999_);
v___x_5019_ = l_Lean_MessageData_ofSyntax(v_a_4999_);
v___x_5020_ = l_Lean_indentD(v___x_5019_);
v___x_5021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5021_, 0, v___x_5018_);
lean_ctor_set(v___x_5021_, 1, v___x_5020_);
v___x_5022_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5021_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
if (lean_obj_tag(v___x_5022_) == 0)
{
lean_dec_ref_known(v___x_5022_, 1);
v_snd_4979_ = v_b_4970_;
goto v___jp_4978_;
}
else
{
lean_object* v_a_5023_; 
v_a_5023_ = lean_ctor_get(v___x_5022_, 0);
lean_inc(v_a_5023_);
lean_dec_ref_known(v___x_5022_, 1);
v_a_4989_ = v_a_5023_;
goto v___jp_4988_;
}
}
else
{
lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5024_ = lean_unsigned_to_nat(1u);
v___x_5025_ = l_Lean_Syntax_getArg(v___x_5009_, v___x_5024_);
lean_dec(v___x_5009_);
if (v___x_5015_ == 0)
{
lean_object* v___x_5034_; uint8_t v___x_5035_; 
v___x_5034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15));
lean_inc(v___x_5025_);
v___x_5035_ = l_Lean_Syntax_isOfKind(v___x_5025_, v___x_5034_);
if (v___x_5035_ == 0)
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
lean_dec(v___x_5025_);
v___x_5036_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4999_);
v___x_5037_ = l_Lean_MessageData_ofSyntax(v_a_4999_);
v___x_5038_ = l_Lean_indentD(v___x_5037_);
v___x_5039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5039_, 0, v___x_5036_);
lean_ctor_set(v___x_5039_, 1, v___x_5038_);
v___x_5040_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5039_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
if (lean_obj_tag(v___x_5040_) == 0)
{
lean_dec_ref_known(v___x_5040_, 1);
v_snd_4979_ = v_b_4970_;
goto v___jp_4978_;
}
else
{
lean_object* v_a_5041_; 
v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
lean_inc(v_a_5041_);
lean_dec_ref_known(v___x_5040_, 1);
v_a_4989_ = v_a_5041_;
goto v___jp_4988_;
}
}
else
{
goto v___jp_5026_;
}
}
else
{
goto v___jp_5026_;
}
v___jp_5026_:
{
if (v_only_4965_ == 0)
{
lean_object* v___x_5027_; lean_object* v___x_5028_; 
v___x_5027_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13);
v___x_5028_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_5025_, v___x_5027_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
if (lean_obj_tag(v___x_5028_) == 0)
{
lean_object* v_a_5029_; lean_object* v___x_5030_; 
v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
lean_inc(v_a_5029_);
lean_dec_ref_known(v___x_5028_, 1);
lean_inc_ref(v_b_4970_);
v___x_5030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4970_, v___x_5025_, v_a_5029_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
lean_dec(v___x_5025_);
v___y_4993_ = v___x_5030_;
goto v___jp_4992_;
}
else
{
lean_object* v_a_5031_; 
lean_dec(v___x_5025_);
v_a_5031_ = lean_ctor_get(v___x_5028_, 0);
lean_inc(v_a_5031_);
lean_dec_ref_known(v___x_5028_, 1);
v_a_4989_ = v_a_5031_;
goto v___jp_4988_;
}
}
else
{
lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5032_ = lean_box(0);
lean_inc_ref(v_b_4970_);
v___x_5033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4970_, v___x_5025_, v___x_5032_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
lean_dec(v___x_5025_);
v___y_4993_ = v___x_5033_;
goto v___jp_4992_;
}
}
}
}
else
{
lean_object* v___x_5042_; lean_object* v___x_5043_; uint8_t v___x_5044_; 
v___x_5042_ = lean_unsigned_to_nat(1u);
v___x_5043_ = l_Lean_Syntax_getArg(v___x_5009_, v___x_5042_);
v___x_5044_ = l_Lean_Syntax_isNone(v___x_5043_);
if (v___x_5044_ == 0)
{
uint8_t v___x_5045_; 
lean_inc(v___x_5043_);
v___x_5045_ = l_Lean_Syntax_matchesNull(v___x_5043_, v___x_5042_);
if (v___x_5045_ == 0)
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; 
lean_dec(v___x_5043_);
lean_dec(v___x_5009_);
v___x_5046_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4999_);
v___x_5047_ = l_Lean_MessageData_ofSyntax(v_a_4999_);
v___x_5048_ = l_Lean_indentD(v___x_5047_);
v___x_5049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5049_, 0, v___x_5046_);
lean_ctor_set(v___x_5049_, 1, v___x_5048_);
v___x_5050_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5049_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
if (lean_obj_tag(v___x_5050_) == 0)
{
lean_dec_ref_known(v___x_5050_, 1);
v_snd_4979_ = v_b_4970_;
goto v___jp_4978_;
}
else
{
lean_object* v_a_5051_; 
v_a_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc(v_a_5051_);
lean_dec_ref_known(v___x_5050_, 1);
v_a_4989_ = v_a_5051_;
goto v___jp_4988_;
}
}
else
{
lean_object* v___x_5052_; 
v___x_5052_ = l_Lean_Syntax_getArg(v___x_5043_, v___x_5008_);
lean_dec(v___x_5043_);
if (v___x_5044_ == 0)
{
lean_object* v___x_5057_; uint8_t v___x_5058_; 
v___x_5057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_5052_);
v___x_5058_ = l_Lean_Syntax_isOfKind(v___x_5052_, v___x_5057_);
if (v___x_5058_ == 0)
{
lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
lean_dec(v___x_5052_);
lean_dec(v___x_5009_);
v___x_5059_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4999_);
v___x_5060_ = l_Lean_MessageData_ofSyntax(v_a_4999_);
v___x_5061_ = l_Lean_indentD(v___x_5060_);
v___x_5062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5059_);
lean_ctor_set(v___x_5062_, 1, v___x_5061_);
v___x_5063_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5062_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
if (lean_obj_tag(v___x_5063_) == 0)
{
lean_dec_ref_known(v___x_5063_, 1);
v_snd_4979_ = v_b_4970_;
goto v___jp_4978_;
}
else
{
lean_object* v_a_5064_; 
v_a_5064_ = lean_ctor_get(v___x_5063_, 0);
lean_inc(v_a_5064_);
lean_dec_ref_known(v___x_5063_, 1);
v_a_4989_ = v_a_5064_;
goto v___jp_4988_;
}
}
else
{
goto v___jp_5053_;
}
}
else
{
goto v___jp_5053_;
}
v___jp_5053_:
{
lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5054_ = lean_box(0);
v___x_5055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5055_, 0, v___x_5052_);
lean_inc(v_a_4999_);
lean_inc_ref(v_b_4970_);
v___x_5056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_5009_, v_b_4970_, v_a_4999_, v___x_5001_, v_only_4965_, v_incremental_4966_, v___x_5013_, v___x_5054_, v___x_5055_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
lean_dec(v___x_5009_);
v___y_4993_ = v___x_5056_;
goto v___jp_4992_;
}
}
}
else
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
lean_dec(v___x_5043_);
v___x_5065_ = lean_box(0);
v___x_5066_ = lean_box(0);
lean_inc(v_a_4999_);
lean_inc_ref(v_b_4970_);
v___x_5067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_5009_, v_b_4970_, v_a_4999_, v___x_5001_, v_only_4965_, v_incremental_4966_, v___x_5013_, v___x_5065_, v___x_5066_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
lean_dec(v___x_5009_);
v___y_4993_ = v___x_5067_;
goto v___jp_4992_;
}
}
}
else
{
lean_object* v___x_5068_; uint8_t v___x_5069_; 
v___x_5068_ = l_Lean_Syntax_getArg(v___x_5009_, v___x_5008_);
v___x_5069_ = l_Lean_Syntax_isNone(v___x_5068_);
if (v___x_5069_ == 0)
{
lean_object* v___x_5070_; uint8_t v___x_5071_; 
v___x_5070_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_5068_);
v___x_5071_ = l_Lean_Syntax_matchesNull(v___x_5068_, v___x_5070_);
if (v___x_5071_ == 0)
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
lean_dec(v___x_5068_);
lean_dec(v___x_5009_);
v___x_5072_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4999_);
v___x_5073_ = l_Lean_MessageData_ofSyntax(v_a_4999_);
v___x_5074_ = l_Lean_indentD(v___x_5073_);
v___x_5075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5075_, 0, v___x_5072_);
lean_ctor_set(v___x_5075_, 1, v___x_5074_);
v___x_5076_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5075_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_dec_ref_known(v___x_5076_, 1);
v_snd_4979_ = v_b_4970_;
goto v___jp_4978_;
}
else
{
lean_object* v_a_5077_; 
v_a_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_a_5077_);
lean_dec_ref_known(v___x_5076_, 1);
v_a_4989_ = v_a_5077_;
goto v___jp_4988_;
}
}
else
{
lean_object* v___x_5078_; 
v___x_5078_ = l_Lean_Syntax_getArg(v___x_5068_, v___x_5008_);
lean_dec(v___x_5068_);
if (v___x_5069_ == 0)
{
lean_object* v___x_5083_; uint8_t v___x_5084_; 
v___x_5083_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_5078_);
v___x_5084_ = l_Lean_Syntax_isOfKind(v___x_5078_, v___x_5083_);
if (v___x_5084_ == 0)
{
lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
lean_dec(v___x_5078_);
lean_dec(v___x_5009_);
v___x_5085_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4999_);
v___x_5086_ = l_Lean_MessageData_ofSyntax(v_a_4999_);
v___x_5087_ = l_Lean_indentD(v___x_5086_);
v___x_5088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5088_, 0, v___x_5085_);
lean_ctor_set(v___x_5088_, 1, v___x_5087_);
v___x_5089_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5088_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
if (lean_obj_tag(v___x_5089_) == 0)
{
lean_dec_ref_known(v___x_5089_, 1);
v_snd_4979_ = v_b_4970_;
goto v___jp_4978_;
}
else
{
lean_object* v_a_5090_; 
v_a_5090_ = lean_ctor_get(v___x_5089_, 0);
lean_inc(v_a_5090_);
lean_dec_ref_known(v___x_5089_, 1);
v_a_4989_ = v_a_5090_;
goto v___jp_4988_;
}
}
else
{
goto v___jp_5079_;
}
}
else
{
goto v___jp_5079_;
}
v___jp_5079_:
{
lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
v___x_5080_ = lean_box(0);
v___x_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5081_, 0, v___x_5078_);
lean_inc(v_a_4999_);
lean_inc_ref(v_b_4970_);
v___x_5082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_5009_, v_b_4970_, v_a_4999_, v___x_5011_, v_only_4965_, v_incremental_4966_, v___x_5080_, v___x_5081_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
lean_dec(v___x_5009_);
v___y_4993_ = v___x_5082_;
goto v___jp_4992_;
}
}
}
else
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
lean_dec(v___x_5068_);
v___x_5091_ = lean_box(0);
v___x_5092_ = lean_box(0);
lean_inc(v_a_4999_);
lean_inc_ref(v_b_4970_);
v___x_5093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_5009_, v_b_4970_, v_a_4999_, v___x_5011_, v_only_4965_, v_incremental_4966_, v___x_5091_, v___x_5092_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
lean_dec(v___x_5009_);
v___y_4993_ = v___x_5093_;
goto v___jp_4992_;
}
}
}
else
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; uint8_t v___x_5097_; 
v___x_5094_ = lean_unsigned_to_nat(1u);
v___x_5095_ = l_Lean_Syntax_getArg(v___x_5009_, v___x_5094_);
lean_dec(v___x_5009_);
v___x_5096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_5095_);
v___x_5097_ = l_Lean_Syntax_isOfKind(v___x_5095_, v___x_5096_);
if (v___x_5097_ == 0)
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; 
lean_dec(v___x_5095_);
v___x_5098_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4999_);
v___x_5099_ = l_Lean_MessageData_ofSyntax(v_a_4999_);
v___x_5100_ = l_Lean_indentD(v___x_5099_);
v___x_5101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5098_);
lean_ctor_set(v___x_5101_, 1, v___x_5100_);
v___x_5102_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5101_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_dec_ref_known(v___x_5102_, 1);
v_snd_4979_ = v_b_4970_;
goto v___jp_4978_;
}
else
{
lean_object* v_a_5103_; 
v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
lean_inc(v_a_5103_);
lean_dec_ref_known(v___x_5102_, 1);
v_a_4989_ = v_a_5103_;
goto v___jp_4988_;
}
}
else
{
if (v_incremental_4966_ == 0)
{
lean_object* v___x_5104_; lean_object* v___x_5105_; 
v___x_5104_ = lean_box(0);
lean_inc_ref(v_b_4970_);
v___x_5105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_5095_, v___x_5001_, v_b_4970_, v___x_5104_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
v___y_4993_ = v___x_5105_;
goto v___jp_4992_;
}
else
{
lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5106_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_5107_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_4999_, v___x_5106_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v_a_5108_; lean_object* v___x_5109_; 
v_a_5108_ = lean_ctor_get(v___x_5107_, 0);
lean_inc(v_a_5108_);
lean_dec_ref_known(v___x_5107_, 1);
lean_inc_ref(v_b_4970_);
v___x_5109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_5095_, v___x_5001_, v_b_4970_, v_a_5108_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
v___y_4993_ = v___x_5109_;
goto v___jp_4992_;
}
else
{
lean_object* v_a_5110_; 
lean_dec(v___x_5095_);
v_a_5110_ = lean_ctor_get(v___x_5107_, 0);
lean_inc(v_a_5110_);
lean_dec_ref_known(v___x_5107_, 1);
v_a_4989_ = v_a_5110_;
goto v___jp_4988_;
}
}
}
}
}
}
v___jp_4978_:
{
size_t v___x_4980_; size_t v___x_4981_; 
v___x_4980_ = ((size_t)1ULL);
v___x_4981_ = lean_usize_add(v_i_4969_, v___x_4980_);
v_i_4969_ = v___x_4981_;
v_b_4970_ = v_snd_4979_;
goto _start;
}
v___jp_4983_:
{
if (v___y_4985_ == 0)
{
if (v_lax_4964_ == 0)
{
lean_object* v___x_4986_; 
lean_dec_ref(v_b_4970_);
v___x_4986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4986_, 0, v___y_4984_);
return v___x_4986_;
}
else
{
lean_dec_ref(v___y_4984_);
v_snd_4979_ = v_b_4970_;
goto v___jp_4978_;
}
}
else
{
lean_object* v___x_4987_; 
lean_dec_ref(v_b_4970_);
v___x_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4987_, 0, v___y_4984_);
return v___x_4987_;
}
}
v___jp_4988_:
{
uint8_t v___x_4990_; 
v___x_4990_ = l_Lean_Exception_isInterrupt(v_a_4989_);
if (v___x_4990_ == 0)
{
uint8_t v___x_4991_; 
lean_inc_ref(v_a_4989_);
v___x_4991_ = l_Lean_Exception_isRuntime(v_a_4989_);
v___y_4984_ = v_a_4989_;
v___y_4985_ = v___x_4991_;
goto v___jp_4983_;
}
else
{
v___y_4984_ = v_a_4989_;
v___y_4985_ = v___x_4990_;
goto v___jp_4983_;
}
}
v___jp_4992_:
{
if (lean_obj_tag(v___y_4993_) == 0)
{
lean_object* v_a_4994_; lean_object* v_snd_4995_; 
lean_dec_ref(v_b_4970_);
v_a_4994_ = lean_ctor_get(v___y_4993_, 0);
lean_inc(v_a_4994_);
lean_dec_ref_known(v___y_4993_, 1);
v_snd_4995_ = lean_ctor_get(v_a_4994_, 1);
lean_inc(v_snd_4995_);
lean_dec(v_a_4994_);
v_snd_4979_ = v_snd_4995_;
goto v___jp_4978_;
}
else
{
lean_object* v_a_4996_; 
v_a_4996_ = lean_ctor_get(v___y_4993_, 0);
lean_inc(v_a_4996_);
lean_dec_ref_known(v___y_4993_, 1);
v_a_4989_ = v_a_4996_;
goto v___jp_4988_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_lax_4964_ = stack[0].m_num;
uint8_t v_only_4965_ = stack[1].m_num;
uint8_t v_incremental_4966_ = stack[2].m_num;
lean_object* v_as_4967_ = stack[3].m_obj;
size_t v_sz_4968_ = stack[4].m_num;
size_t v_i_4969_ = stack[5].m_num;
lean_object* v_b_4970_ = stack[6].m_obj;
lean_object* v___y_4971_ = stack[7].m_obj;
lean_object* v___y_4972_ = stack[8].m_obj;
lean_object* v___y_4973_ = stack[9].m_obj;
lean_object* v___y_4974_ = stack[10].m_obj;
lean_object* v___y_4975_ = stack[11].m_obj;
lean_object* v___y_4976_ = stack[12].m_obj;
lean_object* v_res_5111_;
v_res_5111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_4964_, v_only_4965_, v_incremental_4966_, v_as_4967_, v_sz_4968_, v_i_4969_, v_b_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
stack->m_obj
 = v_res_5111_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_5112_, lean_object* v_only_5113_, lean_object* v_incremental_5114_, lean_object* v_as_5115_, lean_object* v_sz_5116_, lean_object* v_i_5117_, lean_object* v_b_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
uint8_t v_lax_boxed_5126_; uint8_t v_only_boxed_5127_; uint8_t v_incremental_boxed_5128_; size_t v_sz_boxed_5129_; size_t v_i_boxed_5130_; lean_object* v_res_5131_; 
v_lax_boxed_5126_ = lean_unbox(v_lax_5112_);
v_only_boxed_5127_ = lean_unbox(v_only_5113_);
v_incremental_boxed_5128_ = lean_unbox(v_incremental_5114_);
v_sz_boxed_5129_ = lean_unbox_usize(v_sz_5116_);
lean_dec(v_sz_5116_);
v_i_boxed_5130_ = lean_unbox_usize(v_i_5117_);
lean_dec(v_i_5117_);
v_res_5131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_5126_, v_only_boxed_5127_, v_incremental_boxed_5128_, v_as_5115_, v_sz_boxed_5129_, v_i_boxed_5130_, v_b_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
lean_dec(v___y_5124_);
lean_dec_ref(v___y_5123_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec_ref(v_as_5115_);
return v_res_5131_;
}
}
lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_5132_, lean_object* v_ps_5133_, uint8_t v_only_5134_, uint8_t v_lax_5135_, uint8_t v_incremental_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_){
_start:
{
size_t v_sz_5144_; size_t v___x_5145_; lean_object* v___x_5146_; 
v_sz_5144_ = lean_array_size(v_ps_5133_);
v___x_5145_ = ((size_t)0ULL);
v___x_5146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_5135_, v_only_5134_, v_incremental_5136_, v_ps_5133_, v_sz_5144_, v___x_5145_, v_params_5132_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_);
return v___x_5146_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabGrindParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_5132_ = stack[0].m_obj;
lean_object* v_ps_5133_ = stack[1].m_obj;
uint8_t v_only_5134_ = stack[2].m_num;
uint8_t v_lax_5135_ = stack[3].m_num;
uint8_t v_incremental_5136_ = stack[4].m_num;
lean_object* v_a_5137_ = stack[5].m_obj;
lean_object* v_a_5138_ = stack[6].m_obj;
lean_object* v_a_5139_ = stack[7].m_obj;
lean_object* v_a_5140_ = stack[8].m_obj;
lean_object* v_a_5141_ = stack[9].m_obj;
lean_object* v_a_5142_ = stack[10].m_obj;
lean_object* v_res_5147_;
v_res_5147_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5132_, v_ps_5133_, v_only_5134_, v_lax_5135_, v_incremental_5136_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_);
stack->m_obj
 = v_res_5147_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_5148_, lean_object* v_ps_5149_, lean_object* v_only_5150_, lean_object* v_lax_5151_, lean_object* v_incremental_5152_, lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_){
_start:
{
uint8_t v_only_boxed_5160_; uint8_t v_lax_boxed_5161_; uint8_t v_incremental_boxed_5162_; lean_object* v_res_5163_; 
v_only_boxed_5160_ = lean_unbox(v_only_5150_);
v_lax_boxed_5161_ = lean_unbox(v_lax_5151_);
v_incremental_boxed_5162_ = lean_unbox(v_incremental_5152_);
v_res_5163_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5148_, v_ps_5149_, v_only_boxed_5160_, v_lax_boxed_5161_, v_incremental_boxed_5162_, v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_);
lean_dec(v_a_5158_);
lean_dec_ref(v_a_5157_);
lean_dec(v_a_5156_);
lean_dec_ref(v_a_5155_);
lean_dec(v_a_5154_);
lean_dec_ref(v_a_5153_);
lean_dec_ref(v_ps_5149_);
return v_res_5163_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_){
_start:
{
lean_object* v_origin_5175_; 
v_origin_5175_ = lean_ctor_get(v_thm_5164_, 5);
if (lean_obj_tag(v_origin_5175_) == 0)
{
lean_object* v_declName_5176_; lean_object* v___x_5177_; 
lean_inc_ref(v_origin_5175_);
lean_dec_ref(v_thm_5164_);
v_declName_5176_ = lean_ctor_get(v_origin_5175_, 0);
lean_inc(v_declName_5176_);
lean_dec_ref_known(v_origin_5175_, 1);
v___x_5177_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_5176_, v_a_5172_, v_a_5173_);
return v___x_5177_;
}
else
{
lean_object* v_proof_5178_; lean_object* v___x_5179_; 
v_proof_5178_ = lean_ctor_get(v_thm_5164_, 1);
lean_inc_ref(v_proof_5178_);
lean_dec_ref(v_thm_5164_);
v___x_5179_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_5178_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_);
return v___x_5179_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_5164_ = stack[0].m_obj;
lean_object* v_a_5165_ = stack[1].m_obj;
lean_object* v_a_5166_ = stack[2].m_obj;
lean_object* v_a_5167_ = stack[3].m_obj;
lean_object* v_a_5168_ = stack[4].m_obj;
lean_object* v_a_5169_ = stack[5].m_obj;
lean_object* v_a_5170_ = stack[6].m_obj;
lean_object* v_a_5171_ = stack[7].m_obj;
lean_object* v_a_5172_ = stack[8].m_obj;
lean_object* v_a_5173_ = stack[9].m_obj;
lean_object* v_res_5180_;
v_res_5180_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_);
stack->m_obj
 = v_res_5180_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_);
lean_dec(v_a_5190_);
lean_dec_ref(v_a_5189_);
lean_dec(v_a_5188_);
lean_dec_ref(v_a_5187_);
lean_dec(v_a_5186_);
lean_dec_ref(v_a_5185_);
lean_dec(v_a_5184_);
lean_dec_ref(v_a_5183_);
lean_dec(v_a_5182_);
return v_res_5192_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_5193_, size_t v_sz_5194_, size_t v_i_5195_, lean_object* v_b_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
uint8_t v___x_5207_; 
v___x_5207_ = lean_usize_dec_lt(v_i_5195_, v_sz_5194_);
if (v___x_5207_ == 0)
{
lean_object* v___x_5208_; 
v___x_5208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5208_, 0, v_b_5196_);
return v___x_5208_;
}
else
{
lean_object* v_snd_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5235_; 
v_snd_5209_ = lean_ctor_get(v_b_5196_, 1);
v_isSharedCheck_5235_ = !lean_is_exclusive(v_b_5196_);
if (v_isSharedCheck_5235_ == 0)
{
lean_object* v_unused_5236_; 
v_unused_5236_ = lean_ctor_get(v_b_5196_, 0);
lean_dec(v_unused_5236_);
v___x_5211_ = v_b_5196_;
v_isShared_5212_ = v_isSharedCheck_5235_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_snd_5209_);
lean_dec(v_b_5196_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5235_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___x_5213_; lean_object* v_a_5215_; lean_object* v_a_5222_; lean_object* v___x_5223_; 
v___x_5213_ = lean_box(0);
v_a_5222_ = lean_array_uget_borrowed(v_as_5193_, v_i_5195_);
lean_inc(v_a_5222_);
v___x_5223_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5222_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
if (lean_obj_tag(v___x_5223_) == 0)
{
lean_object* v_a_5224_; uint8_t v___x_5225_; 
v_a_5224_ = lean_ctor_get(v___x_5223_, 0);
lean_inc(v_a_5224_);
lean_dec_ref_known(v___x_5223_, 1);
v___x_5225_ = lean_unbox(v_a_5224_);
lean_dec(v_a_5224_);
if (v___x_5225_ == 0)
{
v_a_5215_ = v_snd_5209_;
goto v___jp_5214_;
}
else
{
lean_object* v___x_5226_; 
lean_inc(v_a_5222_);
v___x_5226_ = l_Lean_PersistentArray_push___redArg(v_snd_5209_, v_a_5222_);
v_a_5215_ = v___x_5226_;
goto v___jp_5214_;
}
}
else
{
lean_object* v_a_5227_; lean_object* v___x_5229_; uint8_t v_isShared_5230_; uint8_t v_isSharedCheck_5234_; 
lean_del_object(v___x_5211_);
lean_dec(v_snd_5209_);
v_a_5227_ = lean_ctor_get(v___x_5223_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___x_5223_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5229_ = v___x_5223_;
v_isShared_5230_ = v_isSharedCheck_5234_;
goto v_resetjp_5228_;
}
else
{
lean_inc(v_a_5227_);
lean_dec(v___x_5223_);
v___x_5229_ = lean_box(0);
v_isShared_5230_ = v_isSharedCheck_5234_;
goto v_resetjp_5228_;
}
v_resetjp_5228_:
{
lean_object* v___x_5232_; 
if (v_isShared_5230_ == 0)
{
v___x_5232_ = v___x_5229_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v_a_5227_);
v___x_5232_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
return v___x_5232_;
}
}
}
v___jp_5214_:
{
lean_object* v___x_5217_; 
if (v_isShared_5212_ == 0)
{
lean_ctor_set(v___x_5211_, 1, v_a_5215_);
lean_ctor_set(v___x_5211_, 0, v___x_5213_);
v___x_5217_ = v___x_5211_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v___x_5213_);
lean_ctor_set(v_reuseFailAlloc_5221_, 1, v_a_5215_);
v___x_5217_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
size_t v___x_5218_; size_t v___x_5219_; 
v___x_5218_ = ((size_t)1ULL);
v___x_5219_ = lean_usize_add(v_i_5195_, v___x_5218_);
v_i_5195_ = v___x_5219_;
v_b_5196_ = v___x_5217_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5193_ = stack[0].m_obj;
size_t v_sz_5194_ = stack[1].m_num;
size_t v_i_5195_ = stack[2].m_num;
lean_object* v_b_5196_ = stack[3].m_obj;
lean_object* v___y_5197_ = stack[4].m_obj;
lean_object* v___y_5198_ = stack[5].m_obj;
lean_object* v___y_5199_ = stack[6].m_obj;
lean_object* v___y_5200_ = stack[7].m_obj;
lean_object* v___y_5201_ = stack[8].m_obj;
lean_object* v___y_5202_ = stack[9].m_obj;
lean_object* v___y_5203_ = stack[10].m_obj;
lean_object* v___y_5204_ = stack[11].m_obj;
lean_object* v___y_5205_ = stack[12].m_obj;
lean_object* v_res_5237_;
v_res_5237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5193_, v_sz_5194_, v_i_5195_, v_b_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
stack->m_obj
 = v_res_5237_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5238_, lean_object* v_sz_5239_, lean_object* v_i_5240_, lean_object* v_b_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
size_t v_sz_boxed_5252_; size_t v_i_boxed_5253_; lean_object* v_res_5254_; 
v_sz_boxed_5252_ = lean_unbox_usize(v_sz_5239_);
lean_dec(v_sz_5239_);
v_i_boxed_5253_ = lean_unbox_usize(v_i_5240_);
lean_dec(v_i_5240_);
v_res_5254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5238_, v_sz_boxed_5252_, v_i_boxed_5253_, v_b_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5255_, size_t v_sz_5256_, size_t v_i_5257_, lean_object* v_b_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_){
_start:
{
uint8_t v___x_5269_; 
v___x_5269_ = lean_usize_dec_lt(v_i_5257_, v_sz_5256_);
if (v___x_5269_ == 0)
{
lean_object* v___x_5270_; 
v___x_5270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5270_, 0, v_b_5258_);
return v___x_5270_;
}
else
{
lean_object* v_snd_5271_; lean_object* v___x_5273_; uint8_t v_isShared_5274_; uint8_t v_isSharedCheck_5297_; 
v_snd_5271_ = lean_ctor_get(v_b_5258_, 1);
v_isSharedCheck_5297_ = !lean_is_exclusive(v_b_5258_);
if (v_isSharedCheck_5297_ == 0)
{
lean_object* v_unused_5298_; 
v_unused_5298_ = lean_ctor_get(v_b_5258_, 0);
lean_dec(v_unused_5298_);
v___x_5273_ = v_b_5258_;
v_isShared_5274_ = v_isSharedCheck_5297_;
goto v_resetjp_5272_;
}
else
{
lean_inc(v_snd_5271_);
lean_dec(v_b_5258_);
v___x_5273_ = lean_box(0);
v_isShared_5274_ = v_isSharedCheck_5297_;
goto v_resetjp_5272_;
}
v_resetjp_5272_:
{
lean_object* v___x_5275_; lean_object* v_a_5277_; lean_object* v_a_5284_; lean_object* v___x_5285_; 
v___x_5275_ = lean_box(0);
v_a_5284_ = lean_array_uget_borrowed(v_as_5255_, v_i_5257_);
lean_inc(v_a_5284_);
v___x_5285_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5284_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
if (lean_obj_tag(v___x_5285_) == 0)
{
lean_object* v_a_5286_; uint8_t v___x_5287_; 
v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
lean_inc(v_a_5286_);
lean_dec_ref_known(v___x_5285_, 1);
v___x_5287_ = lean_unbox(v_a_5286_);
lean_dec(v_a_5286_);
if (v___x_5287_ == 0)
{
v_a_5277_ = v_snd_5271_;
goto v___jp_5276_;
}
else
{
lean_object* v___x_5288_; 
lean_inc(v_a_5284_);
v___x_5288_ = l_Lean_PersistentArray_push___redArg(v_snd_5271_, v_a_5284_);
v_a_5277_ = v___x_5288_;
goto v___jp_5276_;
}
}
else
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5296_; 
lean_del_object(v___x_5273_);
lean_dec(v_snd_5271_);
v_a_5289_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5296_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5291_ = v___x_5285_;
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5285_);
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
v___jp_5276_:
{
lean_object* v___x_5279_; 
if (v_isShared_5274_ == 0)
{
lean_ctor_set(v___x_5273_, 1, v_a_5277_);
lean_ctor_set(v___x_5273_, 0, v___x_5275_);
v___x_5279_ = v___x_5273_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5275_);
lean_ctor_set(v_reuseFailAlloc_5283_, 1, v_a_5277_);
v___x_5279_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
size_t v___x_5280_; size_t v___x_5281_; lean_object* v___x_5282_; 
v___x_5280_ = ((size_t)1ULL);
v___x_5281_ = lean_usize_add(v_i_5257_, v___x_5280_);
v___x_5282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5255_, v_sz_5256_, v___x_5281_, v___x_5279_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
return v___x_5282_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5255_ = stack[0].m_obj;
size_t v_sz_5256_ = stack[1].m_num;
size_t v_i_5257_ = stack[2].m_num;
lean_object* v_b_5258_ = stack[3].m_obj;
lean_object* v___y_5259_ = stack[4].m_obj;
lean_object* v___y_5260_ = stack[5].m_obj;
lean_object* v___y_5261_ = stack[6].m_obj;
lean_object* v___y_5262_ = stack[7].m_obj;
lean_object* v___y_5263_ = stack[8].m_obj;
lean_object* v___y_5264_ = stack[9].m_obj;
lean_object* v___y_5265_ = stack[10].m_obj;
lean_object* v___y_5266_ = stack[11].m_obj;
lean_object* v___y_5267_ = stack[12].m_obj;
lean_object* v_res_5299_;
v_res_5299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5255_, v_sz_5256_, v_i_5257_, v_b_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
stack->m_obj
 = v_res_5299_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5300_, lean_object* v_sz_5301_, lean_object* v_i_5302_, lean_object* v_b_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_){
_start:
{
size_t v_sz_boxed_5314_; size_t v_i_boxed_5315_; lean_object* v_res_5316_; 
v_sz_boxed_5314_ = lean_unbox_usize(v_sz_5301_);
lean_dec(v_sz_5301_);
v_i_boxed_5315_ = lean_unbox_usize(v_i_5302_);
lean_dec(v_i_5302_);
v_res_5316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5300_, v_sz_boxed_5314_, v_i_boxed_5315_, v_b_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_);
lean_dec(v___y_5312_);
lean_dec_ref(v___y_5311_);
lean_dec(v___y_5310_);
lean_dec_ref(v___y_5309_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec(v___y_5304_);
lean_dec_ref(v_as_5300_);
return v_res_5316_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5317_, size_t v_sz_5318_, size_t v_i_5319_, lean_object* v_b_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_){
_start:
{
uint8_t v___x_5331_; 
v___x_5331_ = lean_usize_dec_lt(v_i_5319_, v_sz_5318_);
if (v___x_5331_ == 0)
{
lean_object* v___x_5332_; 
v___x_5332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5332_, 0, v_b_5320_);
return v___x_5332_;
}
else
{
lean_object* v_snd_5333_; lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5359_; 
v_snd_5333_ = lean_ctor_get(v_b_5320_, 1);
v_isSharedCheck_5359_ = !lean_is_exclusive(v_b_5320_);
if (v_isSharedCheck_5359_ == 0)
{
lean_object* v_unused_5360_; 
v_unused_5360_ = lean_ctor_get(v_b_5320_, 0);
lean_dec(v_unused_5360_);
v___x_5335_ = v_b_5320_;
v_isShared_5336_ = v_isSharedCheck_5359_;
goto v_resetjp_5334_;
}
else
{
lean_inc(v_snd_5333_);
lean_dec(v_b_5320_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5359_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v___x_5337_; lean_object* v_a_5339_; lean_object* v_a_5346_; lean_object* v___x_5347_; 
v___x_5337_ = lean_box(0);
v_a_5346_ = lean_array_uget_borrowed(v_as_5317_, v_i_5319_);
lean_inc(v_a_5346_);
v___x_5347_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5346_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
if (lean_obj_tag(v___x_5347_) == 0)
{
lean_object* v_a_5348_; uint8_t v___x_5349_; 
v_a_5348_ = lean_ctor_get(v___x_5347_, 0);
lean_inc(v_a_5348_);
lean_dec_ref_known(v___x_5347_, 1);
v___x_5349_ = lean_unbox(v_a_5348_);
lean_dec(v_a_5348_);
if (v___x_5349_ == 0)
{
v_a_5339_ = v_snd_5333_;
goto v___jp_5338_;
}
else
{
lean_object* v___x_5350_; 
lean_inc(v_a_5346_);
v___x_5350_ = l_Lean_PersistentArray_push___redArg(v_snd_5333_, v_a_5346_);
v_a_5339_ = v___x_5350_;
goto v___jp_5338_;
}
}
else
{
lean_object* v_a_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5358_; 
lean_del_object(v___x_5335_);
lean_dec(v_snd_5333_);
v_a_5351_ = lean_ctor_get(v___x_5347_, 0);
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5347_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5353_ = v___x_5347_;
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_a_5351_);
lean_dec(v___x_5347_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v___x_5356_; 
if (v_isShared_5354_ == 0)
{
v___x_5356_ = v___x_5353_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v_a_5351_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
v___jp_5338_:
{
lean_object* v___x_5341_; 
if (v_isShared_5336_ == 0)
{
lean_ctor_set(v___x_5335_, 1, v_a_5339_);
lean_ctor_set(v___x_5335_, 0, v___x_5337_);
v___x_5341_ = v___x_5335_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v___x_5337_);
lean_ctor_set(v_reuseFailAlloc_5345_, 1, v_a_5339_);
v___x_5341_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
size_t v___x_5342_; size_t v___x_5343_; 
v___x_5342_ = ((size_t)1ULL);
v___x_5343_ = lean_usize_add(v_i_5319_, v___x_5342_);
v_i_5319_ = v___x_5343_;
v_b_5320_ = v___x_5341_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5317_ = stack[0].m_obj;
size_t v_sz_5318_ = stack[1].m_num;
size_t v_i_5319_ = stack[2].m_num;
lean_object* v_b_5320_ = stack[3].m_obj;
lean_object* v___y_5321_ = stack[4].m_obj;
lean_object* v___y_5322_ = stack[5].m_obj;
lean_object* v___y_5323_ = stack[6].m_obj;
lean_object* v___y_5324_ = stack[7].m_obj;
lean_object* v___y_5325_ = stack[8].m_obj;
lean_object* v___y_5326_ = stack[9].m_obj;
lean_object* v___y_5327_ = stack[10].m_obj;
lean_object* v___y_5328_ = stack[11].m_obj;
lean_object* v___y_5329_ = stack[12].m_obj;
lean_object* v_res_5361_;
v_res_5361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5317_, v_sz_5318_, v_i_5319_, v_b_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
stack->m_obj
 = v_res_5361_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5362_, lean_object* v_sz_5363_, lean_object* v_i_5364_, lean_object* v_b_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
size_t v_sz_boxed_5376_; size_t v_i_boxed_5377_; lean_object* v_res_5378_; 
v_sz_boxed_5376_ = lean_unbox_usize(v_sz_5363_);
lean_dec(v_sz_5363_);
v_i_boxed_5377_ = lean_unbox_usize(v_i_5364_);
lean_dec(v_i_5364_);
v_res_5378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5362_, v_sz_boxed_5376_, v_i_boxed_5377_, v_b_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
lean_dec(v___y_5374_);
lean_dec_ref(v___y_5373_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v___y_5370_);
lean_dec_ref(v___y_5369_);
lean_dec(v___y_5368_);
lean_dec_ref(v___y_5367_);
lean_dec(v___y_5366_);
lean_dec_ref(v_as_5362_);
return v_res_5378_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5379_, size_t v_sz_5380_, size_t v_i_5381_, lean_object* v_b_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_){
_start:
{
uint8_t v___x_5393_; 
v___x_5393_ = lean_usize_dec_lt(v_i_5381_, v_sz_5380_);
if (v___x_5393_ == 0)
{
lean_object* v___x_5394_; 
v___x_5394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5394_, 0, v_b_5382_);
return v___x_5394_;
}
else
{
lean_object* v_snd_5395_; lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5421_; 
v_snd_5395_ = lean_ctor_get(v_b_5382_, 1);
v_isSharedCheck_5421_ = !lean_is_exclusive(v_b_5382_);
if (v_isSharedCheck_5421_ == 0)
{
lean_object* v_unused_5422_; 
v_unused_5422_ = lean_ctor_get(v_b_5382_, 0);
lean_dec(v_unused_5422_);
v___x_5397_ = v_b_5382_;
v_isShared_5398_ = v_isSharedCheck_5421_;
goto v_resetjp_5396_;
}
else
{
lean_inc(v_snd_5395_);
lean_dec(v_b_5382_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5421_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
lean_object* v___x_5399_; lean_object* v_a_5401_; lean_object* v_a_5408_; lean_object* v___x_5409_; 
v___x_5399_ = lean_box(0);
v_a_5408_ = lean_array_uget_borrowed(v_as_5379_, v_i_5381_);
lean_inc(v_a_5408_);
v___x_5409_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5408_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_);
if (lean_obj_tag(v___x_5409_) == 0)
{
lean_object* v_a_5410_; uint8_t v___x_5411_; 
v_a_5410_ = lean_ctor_get(v___x_5409_, 0);
lean_inc(v_a_5410_);
lean_dec_ref_known(v___x_5409_, 1);
v___x_5411_ = lean_unbox(v_a_5410_);
lean_dec(v_a_5410_);
if (v___x_5411_ == 0)
{
v_a_5401_ = v_snd_5395_;
goto v___jp_5400_;
}
else
{
lean_object* v___x_5412_; 
lean_inc(v_a_5408_);
v___x_5412_ = l_Lean_PersistentArray_push___redArg(v_snd_5395_, v_a_5408_);
v_a_5401_ = v___x_5412_;
goto v___jp_5400_;
}
}
else
{
lean_object* v_a_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5420_; 
lean_del_object(v___x_5397_);
lean_dec(v_snd_5395_);
v_a_5413_ = lean_ctor_get(v___x_5409_, 0);
v_isSharedCheck_5420_ = !lean_is_exclusive(v___x_5409_);
if (v_isSharedCheck_5420_ == 0)
{
v___x_5415_ = v___x_5409_;
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_a_5413_);
lean_dec(v___x_5409_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
lean_object* v___x_5418_; 
if (v_isShared_5416_ == 0)
{
v___x_5418_ = v___x_5415_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5413_);
v___x_5418_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
return v___x_5418_;
}
}
}
v___jp_5400_:
{
lean_object* v___x_5403_; 
if (v_isShared_5398_ == 0)
{
lean_ctor_set(v___x_5397_, 1, v_a_5401_);
lean_ctor_set(v___x_5397_, 0, v___x_5399_);
v___x_5403_ = v___x_5397_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v___x_5399_);
lean_ctor_set(v_reuseFailAlloc_5407_, 1, v_a_5401_);
v___x_5403_ = v_reuseFailAlloc_5407_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
size_t v___x_5404_; size_t v___x_5405_; lean_object* v___x_5406_; 
v___x_5404_ = ((size_t)1ULL);
v___x_5405_ = lean_usize_add(v_i_5381_, v___x_5404_);
v___x_5406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5379_, v_sz_5380_, v___x_5405_, v___x_5403_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_);
return v___x_5406_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5379_ = stack[0].m_obj;
size_t v_sz_5380_ = stack[1].m_num;
size_t v_i_5381_ = stack[2].m_num;
lean_object* v_b_5382_ = stack[3].m_obj;
lean_object* v___y_5383_ = stack[4].m_obj;
lean_object* v___y_5384_ = stack[5].m_obj;
lean_object* v___y_5385_ = stack[6].m_obj;
lean_object* v___y_5386_ = stack[7].m_obj;
lean_object* v___y_5387_ = stack[8].m_obj;
lean_object* v___y_5388_ = stack[9].m_obj;
lean_object* v___y_5389_ = stack[10].m_obj;
lean_object* v___y_5390_ = stack[11].m_obj;
lean_object* v___y_5391_ = stack[12].m_obj;
lean_object* v_res_5423_;
v_res_5423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5379_, v_sz_5380_, v_i_5381_, v_b_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_);
stack->m_obj
 = v_res_5423_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5424_, lean_object* v_sz_5425_, lean_object* v_i_5426_, lean_object* v_b_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_){
_start:
{
size_t v_sz_boxed_5438_; size_t v_i_boxed_5439_; lean_object* v_res_5440_; 
v_sz_boxed_5438_ = lean_unbox_usize(v_sz_5425_);
lean_dec(v_sz_5425_);
v_i_boxed_5439_ = lean_unbox_usize(v_i_5426_);
lean_dec(v_i_5426_);
v_res_5440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5424_, v_sz_boxed_5438_, v_i_boxed_5439_, v_b_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
lean_dec(v___y_5430_);
lean_dec_ref(v___y_5429_);
lean_dec(v___y_5428_);
lean_dec_ref(v_as_5424_);
return v_res_5440_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5441_, lean_object* v_n_5442_, lean_object* v_b_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_){
_start:
{
if (lean_obj_tag(v_n_5442_) == 0)
{
lean_object* v_cs_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; size_t v_sz_5457_; size_t v___x_5458_; lean_object* v___x_5459_; 
v_cs_5454_ = lean_ctor_get(v_n_5442_, 0);
v___x_5455_ = lean_box(0);
v___x_5456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5456_, 0, v___x_5455_);
lean_ctor_set(v___x_5456_, 1, v_b_5443_);
v_sz_5457_ = lean_array_size(v_cs_5454_);
v___x_5458_ = ((size_t)0ULL);
v___x_5459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5441_, v_cs_5454_, v_sz_5457_, v___x_5458_, v___x_5456_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_);
if (lean_obj_tag(v___x_5459_) == 0)
{
lean_object* v_a_5460_; lean_object* v___x_5462_; uint8_t v_isShared_5463_; uint8_t v_isSharedCheck_5474_; 
v_a_5460_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5474_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5474_ == 0)
{
v___x_5462_ = v___x_5459_;
v_isShared_5463_ = v_isSharedCheck_5474_;
goto v_resetjp_5461_;
}
else
{
lean_inc(v_a_5460_);
lean_dec(v___x_5459_);
v___x_5462_ = lean_box(0);
v_isShared_5463_ = v_isSharedCheck_5474_;
goto v_resetjp_5461_;
}
v_resetjp_5461_:
{
lean_object* v_fst_5464_; 
v_fst_5464_ = lean_ctor_get(v_a_5460_, 0);
if (lean_obj_tag(v_fst_5464_) == 0)
{
lean_object* v_snd_5465_; lean_object* v___x_5466_; lean_object* v___x_5468_; 
v_snd_5465_ = lean_ctor_get(v_a_5460_, 1);
lean_inc(v_snd_5465_);
lean_dec(v_a_5460_);
v___x_5466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5466_, 0, v_snd_5465_);
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 0, v___x_5466_);
v___x_5468_ = v___x_5462_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v___x_5466_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
else
{
lean_object* v_val_5470_; lean_object* v___x_5472_; 
lean_inc_ref(v_fst_5464_);
lean_dec(v_a_5460_);
v_val_5470_ = lean_ctor_get(v_fst_5464_, 0);
lean_inc(v_val_5470_);
lean_dec_ref_known(v_fst_5464_, 1);
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 0, v_val_5470_);
v___x_5472_ = v___x_5462_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_val_5470_);
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
else
{
lean_object* v_a_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5482_; 
v_a_5475_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5477_ = v___x_5459_;
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_a_5475_);
lean_dec(v___x_5459_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v___x_5480_; 
if (v_isShared_5478_ == 0)
{
v___x_5480_ = v___x_5477_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v_a_5475_);
v___x_5480_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
return v___x_5480_;
}
}
}
}
else
{
lean_object* v_vs_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; size_t v_sz_5486_; size_t v___x_5487_; lean_object* v___x_5488_; 
v_vs_5483_ = lean_ctor_get(v_n_5442_, 0);
v___x_5484_ = lean_box(0);
v___x_5485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5485_, 0, v___x_5484_);
lean_ctor_set(v___x_5485_, 1, v_b_5443_);
v_sz_5486_ = lean_array_size(v_vs_5483_);
v___x_5487_ = ((size_t)0ULL);
v___x_5488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5483_, v_sz_5486_, v___x_5487_, v___x_5485_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_);
if (lean_obj_tag(v___x_5488_) == 0)
{
lean_object* v_a_5489_; lean_object* v___x_5491_; uint8_t v_isShared_5492_; uint8_t v_isSharedCheck_5503_; 
v_a_5489_ = lean_ctor_get(v___x_5488_, 0);
v_isSharedCheck_5503_ = !lean_is_exclusive(v___x_5488_);
if (v_isSharedCheck_5503_ == 0)
{
v___x_5491_ = v___x_5488_;
v_isShared_5492_ = v_isSharedCheck_5503_;
goto v_resetjp_5490_;
}
else
{
lean_inc(v_a_5489_);
lean_dec(v___x_5488_);
v___x_5491_ = lean_box(0);
v_isShared_5492_ = v_isSharedCheck_5503_;
goto v_resetjp_5490_;
}
v_resetjp_5490_:
{
lean_object* v_fst_5493_; 
v_fst_5493_ = lean_ctor_get(v_a_5489_, 0);
if (lean_obj_tag(v_fst_5493_) == 0)
{
lean_object* v_snd_5494_; lean_object* v___x_5495_; lean_object* v___x_5497_; 
v_snd_5494_ = lean_ctor_get(v_a_5489_, 1);
lean_inc(v_snd_5494_);
lean_dec(v_a_5489_);
v___x_5495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5495_, 0, v_snd_5494_);
if (v_isShared_5492_ == 0)
{
lean_ctor_set(v___x_5491_, 0, v___x_5495_);
v___x_5497_ = v___x_5491_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v___x_5495_);
v___x_5497_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
return v___x_5497_;
}
}
else
{
lean_object* v_val_5499_; lean_object* v___x_5501_; 
lean_inc_ref(v_fst_5493_);
lean_dec(v_a_5489_);
v_val_5499_ = lean_ctor_get(v_fst_5493_, 0);
lean_inc(v_val_5499_);
lean_dec_ref_known(v_fst_5493_, 1);
if (v_isShared_5492_ == 0)
{
lean_ctor_set(v___x_5491_, 0, v_val_5499_);
v___x_5501_ = v___x_5491_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v_val_5499_);
v___x_5501_ = v_reuseFailAlloc_5502_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
return v___x_5501_;
}
}
}
}
else
{
lean_object* v_a_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5511_; 
v_a_5504_ = lean_ctor_get(v___x_5488_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v___x_5488_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5506_ = v___x_5488_;
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_a_5504_);
lean_dec(v___x_5488_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5509_; 
if (v_isShared_5507_ == 0)
{
v___x_5509_ = v___x_5506_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5504_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_5441_ = stack[0].m_obj;
lean_object* v_n_5442_ = stack[1].m_obj;
lean_object* v_b_5443_ = stack[2].m_obj;
lean_object* v___y_5444_ = stack[3].m_obj;
lean_object* v___y_5445_ = stack[4].m_obj;
lean_object* v___y_5446_ = stack[5].m_obj;
lean_object* v___y_5447_ = stack[6].m_obj;
lean_object* v___y_5448_ = stack[7].m_obj;
lean_object* v___y_5449_ = stack[8].m_obj;
lean_object* v___y_5450_ = stack[9].m_obj;
lean_object* v___y_5451_ = stack[10].m_obj;
lean_object* v___y_5452_ = stack[11].m_obj;
lean_object* v_res_5512_;
v_res_5512_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5441_, v_n_5442_, v_b_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_);
stack->m_obj
 = v_res_5512_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5513_, lean_object* v_as_5514_, size_t v_sz_5515_, size_t v_i_5516_, lean_object* v_b_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_){
_start:
{
uint8_t v___x_5528_; 
v___x_5528_ = lean_usize_dec_lt(v_i_5516_, v_sz_5515_);
if (v___x_5528_ == 0)
{
lean_object* v___x_5529_; 
v___x_5529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5529_, 0, v_b_5517_);
return v___x_5529_;
}
else
{
lean_object* v_snd_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5564_; 
v_snd_5530_ = lean_ctor_get(v_b_5517_, 1);
v_isSharedCheck_5564_ = !lean_is_exclusive(v_b_5517_);
if (v_isSharedCheck_5564_ == 0)
{
lean_object* v_unused_5565_; 
v_unused_5565_ = lean_ctor_get(v_b_5517_, 0);
lean_dec(v_unused_5565_);
v___x_5532_ = v_b_5517_;
v_isShared_5533_ = v_isSharedCheck_5564_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_snd_5530_);
lean_dec(v_b_5517_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5564_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v___x_5534_; lean_object* v_a_5535_; lean_object* v___x_5536_; 
v___x_5534_ = lean_box(0);
v_a_5535_ = lean_array_uget_borrowed(v_as_5514_, v_i_5516_);
lean_inc(v_snd_5530_);
v___x_5536_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5513_, v_a_5535_, v_snd_5530_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_);
if (lean_obj_tag(v___x_5536_) == 0)
{
lean_object* v_a_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5555_; 
v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5555_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5555_ == 0)
{
v___x_5539_ = v___x_5536_;
v_isShared_5540_ = v_isSharedCheck_5555_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_a_5537_);
lean_dec(v___x_5536_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5555_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
if (lean_obj_tag(v_a_5537_) == 0)
{
lean_object* v___x_5541_; lean_object* v___x_5543_; 
v___x_5541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5541_, 0, v_a_5537_);
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 0, v___x_5541_);
v___x_5543_ = v___x_5532_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v___x_5541_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v_snd_5530_);
v___x_5543_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
lean_object* v___x_5545_; 
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 0, v___x_5543_);
v___x_5545_ = v___x_5539_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v___x_5543_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
return v___x_5545_;
}
}
}
else
{
lean_object* v_a_5548_; lean_object* v___x_5550_; 
lean_del_object(v___x_5539_);
lean_dec(v_snd_5530_);
v_a_5548_ = lean_ctor_get(v_a_5537_, 0);
lean_inc(v_a_5548_);
lean_dec_ref_known(v_a_5537_, 1);
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 1, v_a_5548_);
lean_ctor_set(v___x_5532_, 0, v___x_5534_);
v___x_5550_ = v___x_5532_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v___x_5534_);
lean_ctor_set(v_reuseFailAlloc_5554_, 1, v_a_5548_);
v___x_5550_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
size_t v___x_5551_; size_t v___x_5552_; 
v___x_5551_ = ((size_t)1ULL);
v___x_5552_ = lean_usize_add(v_i_5516_, v___x_5551_);
v_i_5516_ = v___x_5552_;
v_b_5517_ = v___x_5550_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5556_; lean_object* v___x_5558_; uint8_t v_isShared_5559_; uint8_t v_isSharedCheck_5563_; 
lean_del_object(v___x_5532_);
lean_dec(v_snd_5530_);
v_a_5556_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5563_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5563_ == 0)
{
v___x_5558_ = v___x_5536_;
v_isShared_5559_ = v_isSharedCheck_5563_;
goto v_resetjp_5557_;
}
else
{
lean_inc(v_a_5556_);
lean_dec(v___x_5536_);
v___x_5558_ = lean_box(0);
v_isShared_5559_ = v_isSharedCheck_5563_;
goto v_resetjp_5557_;
}
v_resetjp_5557_:
{
lean_object* v___x_5561_; 
if (v_isShared_5559_ == 0)
{
v___x_5561_ = v___x_5558_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5562_; 
v_reuseFailAlloc_5562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_a_5556_);
v___x_5561_ = v_reuseFailAlloc_5562_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
return v___x_5561_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_5513_ = stack[0].m_obj;
lean_object* v_as_5514_ = stack[1].m_obj;
size_t v_sz_5515_ = stack[2].m_num;
size_t v_i_5516_ = stack[3].m_num;
lean_object* v_b_5517_ = stack[4].m_obj;
lean_object* v___y_5518_ = stack[5].m_obj;
lean_object* v___y_5519_ = stack[6].m_obj;
lean_object* v___y_5520_ = stack[7].m_obj;
lean_object* v___y_5521_ = stack[8].m_obj;
lean_object* v___y_5522_ = stack[9].m_obj;
lean_object* v___y_5523_ = stack[10].m_obj;
lean_object* v___y_5524_ = stack[11].m_obj;
lean_object* v___y_5525_ = stack[12].m_obj;
lean_object* v___y_5526_ = stack[13].m_obj;
lean_object* v_res_5566_;
v_res_5566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5513_, v_as_5514_, v_sz_5515_, v_i_5516_, v_b_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_);
stack->m_obj
 = v_res_5566_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5567_, lean_object* v_as_5568_, lean_object* v_sz_5569_, lean_object* v_i_5570_, lean_object* v_b_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_){
_start:
{
size_t v_sz_boxed_5582_; size_t v_i_boxed_5583_; lean_object* v_res_5584_; 
v_sz_boxed_5582_ = lean_unbox_usize(v_sz_5569_);
lean_dec(v_sz_5569_);
v_i_boxed_5583_ = lean_unbox_usize(v_i_5570_);
lean_dec(v_i_5570_);
v_res_5584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5567_, v_as_5568_, v_sz_boxed_5582_, v_i_boxed_5583_, v_b_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_);
lean_dec(v___y_5580_);
lean_dec_ref(v___y_5579_);
lean_dec(v___y_5578_);
lean_dec_ref(v___y_5577_);
lean_dec(v___y_5576_);
lean_dec_ref(v___y_5575_);
lean_dec(v___y_5574_);
lean_dec_ref(v___y_5573_);
lean_dec(v___y_5572_);
lean_dec_ref(v_as_5568_);
lean_dec_ref(v_init_5567_);
return v_res_5584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5585_, lean_object* v_n_5586_, lean_object* v_b_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_){
_start:
{
lean_object* v_res_5598_; 
v_res_5598_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5585_, v_n_5586_, v_b_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
lean_dec(v___y_5592_);
lean_dec_ref(v___y_5591_);
lean_dec(v___y_5590_);
lean_dec_ref(v___y_5589_);
lean_dec(v___y_5588_);
lean_dec_ref(v_n_5586_);
lean_dec_ref(v_init_5585_);
return v_res_5598_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5599_, lean_object* v_init_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_){
_start:
{
lean_object* v_root_5611_; lean_object* v_tail_5612_; lean_object* v___x_5613_; 
v_root_5611_ = lean_ctor_get(v_t_5599_, 0);
v_tail_5612_ = lean_ctor_get(v_t_5599_, 1);
lean_inc_ref(v_init_5600_);
v___x_5613_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5600_, v_root_5611_, v_init_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_);
lean_dec_ref(v_init_5600_);
if (lean_obj_tag(v___x_5613_) == 0)
{
lean_object* v_a_5614_; lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5650_; 
v_a_5614_ = lean_ctor_get(v___x_5613_, 0);
v_isSharedCheck_5650_ = !lean_is_exclusive(v___x_5613_);
if (v_isSharedCheck_5650_ == 0)
{
v___x_5616_ = v___x_5613_;
v_isShared_5617_ = v_isSharedCheck_5650_;
goto v_resetjp_5615_;
}
else
{
lean_inc(v_a_5614_);
lean_dec(v___x_5613_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5650_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
if (lean_obj_tag(v_a_5614_) == 0)
{
lean_object* v_a_5618_; lean_object* v___x_5620_; 
v_a_5618_ = lean_ctor_get(v_a_5614_, 0);
lean_inc(v_a_5618_);
lean_dec_ref_known(v_a_5614_, 1);
if (v_isShared_5617_ == 0)
{
lean_ctor_set(v___x_5616_, 0, v_a_5618_);
v___x_5620_ = v___x_5616_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5618_);
v___x_5620_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
return v___x_5620_;
}
}
else
{
lean_object* v_a_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; size_t v_sz_5625_; size_t v___x_5626_; lean_object* v___x_5627_; 
lean_del_object(v___x_5616_);
v_a_5622_ = lean_ctor_get(v_a_5614_, 0);
lean_inc(v_a_5622_);
lean_dec_ref_known(v_a_5614_, 1);
v___x_5623_ = lean_box(0);
v___x_5624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5624_, 0, v___x_5623_);
lean_ctor_set(v___x_5624_, 1, v_a_5622_);
v_sz_5625_ = lean_array_size(v_tail_5612_);
v___x_5626_ = ((size_t)0ULL);
v___x_5627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5612_, v_sz_5625_, v___x_5626_, v___x_5624_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_);
if (lean_obj_tag(v___x_5627_) == 0)
{
lean_object* v_a_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5641_; 
v_a_5628_ = lean_ctor_get(v___x_5627_, 0);
v_isSharedCheck_5641_ = !lean_is_exclusive(v___x_5627_);
if (v_isSharedCheck_5641_ == 0)
{
v___x_5630_ = v___x_5627_;
v_isShared_5631_ = v_isSharedCheck_5641_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_a_5628_);
lean_dec(v___x_5627_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5641_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
lean_object* v_fst_5632_; 
v_fst_5632_ = lean_ctor_get(v_a_5628_, 0);
if (lean_obj_tag(v_fst_5632_) == 0)
{
lean_object* v_snd_5633_; lean_object* v___x_5635_; 
v_snd_5633_ = lean_ctor_get(v_a_5628_, 1);
lean_inc(v_snd_5633_);
lean_dec(v_a_5628_);
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 0, v_snd_5633_);
v___x_5635_ = v___x_5630_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5636_; 
v_reuseFailAlloc_5636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5636_, 0, v_snd_5633_);
v___x_5635_ = v_reuseFailAlloc_5636_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
return v___x_5635_;
}
}
else
{
lean_object* v_val_5637_; lean_object* v___x_5639_; 
lean_inc_ref(v_fst_5632_);
lean_dec(v_a_5628_);
v_val_5637_ = lean_ctor_get(v_fst_5632_, 0);
lean_inc(v_val_5637_);
lean_dec_ref_known(v_fst_5632_, 1);
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 0, v_val_5637_);
v___x_5639_ = v___x_5630_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_val_5637_);
v___x_5639_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
return v___x_5639_;
}
}
}
}
else
{
lean_object* v_a_5642_; lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5649_; 
v_a_5642_ = lean_ctor_get(v___x_5627_, 0);
v_isSharedCheck_5649_ = !lean_is_exclusive(v___x_5627_);
if (v_isSharedCheck_5649_ == 0)
{
v___x_5644_ = v___x_5627_;
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
else
{
lean_inc(v_a_5642_);
lean_dec(v___x_5627_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v___x_5647_; 
if (v_isShared_5645_ == 0)
{
v___x_5647_ = v___x_5644_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_a_5642_);
v___x_5647_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
return v___x_5647_;
}
}
}
}
}
}
else
{
lean_object* v_a_5651_; lean_object* v___x_5653_; uint8_t v_isShared_5654_; uint8_t v_isSharedCheck_5658_; 
v_a_5651_ = lean_ctor_get(v___x_5613_, 0);
v_isSharedCheck_5658_ = !lean_is_exclusive(v___x_5613_);
if (v_isSharedCheck_5658_ == 0)
{
v___x_5653_ = v___x_5613_;
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
else
{
lean_inc(v_a_5651_);
lean_dec(v___x_5613_);
v___x_5653_ = lean_box(0);
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
v_resetjp_5652_:
{
lean_object* v___x_5656_; 
if (v_isShared_5654_ == 0)
{
v___x_5656_ = v___x_5653_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5651_);
v___x_5656_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
return v___x_5656_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_5599_ = stack[0].m_obj;
lean_object* v_init_5600_ = stack[1].m_obj;
lean_object* v___y_5601_ = stack[2].m_obj;
lean_object* v___y_5602_ = stack[3].m_obj;
lean_object* v___y_5603_ = stack[4].m_obj;
lean_object* v___y_5604_ = stack[5].m_obj;
lean_object* v___y_5605_ = stack[6].m_obj;
lean_object* v___y_5606_ = stack[7].m_obj;
lean_object* v___y_5607_ = stack[8].m_obj;
lean_object* v___y_5608_ = stack[9].m_obj;
lean_object* v___y_5609_ = stack[10].m_obj;
lean_object* v_res_5659_;
v_res_5659_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5599_, v_init_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_);
stack->m_obj
 = v_res_5659_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5660_, lean_object* v_init_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_){
_start:
{
lean_object* v_res_5672_; 
v_res_5672_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5660_, v_init_5661_, v___y_5662_, v___y_5663_, v___y_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_);
lean_dec(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v___y_5668_);
lean_dec_ref(v___y_5667_);
lean_dec(v___y_5666_);
lean_dec_ref(v___y_5665_);
lean_dec(v___y_5664_);
lean_dec_ref(v___y_5663_);
lean_dec(v___y_5662_);
lean_dec_ref(v_t_5660_);
return v_res_5672_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; 
v___x_5673_ = lean_unsigned_to_nat(32u);
v___x_5674_ = lean_mk_empty_array_with_capacity(v___x_5673_);
v___x_5675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5675_, 0, v___x_5674_);
return v___x_5675_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v_result_5681_; 
v___x_5676_ = ((size_t)5ULL);
v___x_5677_ = lean_unsigned_to_nat(0u);
v___x_5678_ = lean_unsigned_to_nat(32u);
v___x_5679_ = lean_mk_empty_array_with_capacity(v___x_5678_);
v___x_5680_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5681_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5681_, 0, v___x_5680_);
lean_ctor_set(v_result_5681_, 1, v___x_5679_);
lean_ctor_set(v_result_5681_, 2, v___x_5677_);
lean_ctor_set(v_result_5681_, 3, v___x_5677_);
lean_ctor_set_usize(v_result_5681_, 4, v___x_5676_);
return v_result_5681_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_){
_start:
{
lean_object* v_result_5693_; lean_object* v___x_5694_; 
v_result_5693_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5694_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5682_, v_result_5693_, v_a_5683_, v_a_5684_, v_a_5685_, v_a_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_);
return v___x_5694_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_0interp(lean_interpreter_value* stack)
{
lean_object* v_thms_5682_ = stack[0].m_obj;
lean_object* v_a_5683_ = stack[1].m_obj;
lean_object* v_a_5684_ = stack[2].m_obj;
lean_object* v_a_5685_ = stack[3].m_obj;
lean_object* v_a_5686_ = stack[4].m_obj;
lean_object* v_a_5687_ = stack[5].m_obj;
lean_object* v_a_5688_ = stack[6].m_obj;
lean_object* v_a_5689_ = stack[7].m_obj;
lean_object* v_a_5690_ = stack[8].m_obj;
lean_object* v_a_5691_ = stack[9].m_obj;
lean_object* v_res_5695_;
v_res_5695_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5682_, v_a_5683_, v_a_5684_, v_a_5685_, v_a_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_);
stack->m_obj
 = v_res_5695_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_){
_start:
{
lean_object* v_res_5707_; 
v_res_5707_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5696_, v_a_5697_, v_a_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_);
lean_dec(v_a_5705_);
lean_dec_ref(v_a_5704_);
lean_dec(v_a_5703_);
lean_dec_ref(v_a_5702_);
lean_dec(v_a_5701_);
lean_dec_ref(v_a_5700_);
lean_dec(v_a_5699_);
lean_dec_ref(v_a_5698_);
lean_dec(v_a_5697_);
lean_dec_ref(v_thms_5696_);
return v_res_5707_;
}
}
lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_5710_, lean_object* v_newThms_5711_, lean_object* v_gmt_5712_, lean_object* v_numInstances_5713_, lean_object* v_numDelayedInstances_5714_, lean_object* v_num_5715_, lean_object* v_preInstances_5716_, lean_object* v_nextThmIdx_5717_, lean_object* v_matchEqNames_5718_, lean_object* v_delayedThmInsts_5719_, lean_object* v_nextDeclIdx_5720_, lean_object* v_enodeMap_5721_, lean_object* v_exprs_5722_, lean_object* v_parents_5723_, lean_object* v_congrTable_5724_, lean_object* v_appMap_5725_, lean_object* v_indicesFound_5726_, lean_object* v_toProcess_5727_, uint8_t v_inconsistent_5728_, lean_object* v_nextIdx_5729_, lean_object* v_newRawFacts_5730_, lean_object* v_facts_5731_, lean_object* v_extThms_5732_, lean_object* v_inj_5733_, lean_object* v_split_5734_, lean_object* v_clean_5735_, lean_object* v_sstates_5736_, lean_object* v_mvarId_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_){
_start:
{
lean_object* v___x_5748_; 
v___x_5748_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5710_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_);
if (lean_obj_tag(v___x_5748_) == 0)
{
lean_object* v_a_5749_; lean_object* v___x_5750_; 
v_a_5749_ = lean_ctor_get(v___x_5748_, 0);
lean_inc(v_a_5749_);
lean_dec_ref_known(v___x_5748_, 1);
v___x_5750_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_5711_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_);
if (lean_obj_tag(v___x_5750_) == 0)
{
lean_object* v_a_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5762_; 
v_a_5751_ = lean_ctor_get(v___x_5750_, 0);
v_isSharedCheck_5762_ = !lean_is_exclusive(v___x_5750_);
if (v_isSharedCheck_5762_ == 0)
{
v___x_5753_ = v___x_5750_;
v_isShared_5754_ = v_isSharedCheck_5762_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_a_5751_);
lean_dec(v___x_5750_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5762_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5760_; 
v___x_5755_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_5756_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5755_);
lean_ctor_set(v___x_5756_, 1, v_gmt_5712_);
lean_ctor_set(v___x_5756_, 2, v_a_5749_);
lean_ctor_set(v___x_5756_, 3, v_a_5751_);
lean_ctor_set(v___x_5756_, 4, v_numInstances_5713_);
lean_ctor_set(v___x_5756_, 5, v_numDelayedInstances_5714_);
lean_ctor_set(v___x_5756_, 6, v_num_5715_);
lean_ctor_set(v___x_5756_, 7, v_preInstances_5716_);
lean_ctor_set(v___x_5756_, 8, v_nextThmIdx_5717_);
lean_ctor_set(v___x_5756_, 9, v_matchEqNames_5718_);
lean_ctor_set(v___x_5756_, 10, v_delayedThmInsts_5719_);
v___x_5757_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_5757_, 0, v_nextDeclIdx_5720_);
lean_ctor_set(v___x_5757_, 1, v_enodeMap_5721_);
lean_ctor_set(v___x_5757_, 2, v_exprs_5722_);
lean_ctor_set(v___x_5757_, 3, v_parents_5723_);
lean_ctor_set(v___x_5757_, 4, v_congrTable_5724_);
lean_ctor_set(v___x_5757_, 5, v_appMap_5725_);
lean_ctor_set(v___x_5757_, 6, v_indicesFound_5726_);
lean_ctor_set(v___x_5757_, 7, v_toProcess_5727_);
lean_ctor_set(v___x_5757_, 8, v_nextIdx_5729_);
lean_ctor_set(v___x_5757_, 9, v_newRawFacts_5730_);
lean_ctor_set(v___x_5757_, 10, v_facts_5731_);
lean_ctor_set(v___x_5757_, 11, v_extThms_5732_);
lean_ctor_set(v___x_5757_, 12, v___x_5756_);
lean_ctor_set(v___x_5757_, 13, v_inj_5733_);
lean_ctor_set(v___x_5757_, 14, v_split_5734_);
lean_ctor_set(v___x_5757_, 15, v_clean_5735_);
lean_ctor_set(v___x_5757_, 16, v_sstates_5736_);
lean_ctor_set_uint8(v___x_5757_, sizeof(void*)*17, v_inconsistent_5728_);
v___x_5758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5758_, 0, v___x_5757_);
lean_ctor_set(v___x_5758_, 1, v_mvarId_5737_);
if (v_isShared_5754_ == 0)
{
lean_ctor_set(v___x_5753_, 0, v___x_5758_);
v___x_5760_ = v___x_5753_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5761_; 
v_reuseFailAlloc_5761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5761_, 0, v___x_5758_);
v___x_5760_ = v_reuseFailAlloc_5761_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
return v___x_5760_;
}
}
}
else
{
lean_object* v_a_5763_; lean_object* v___x_5765_; uint8_t v_isShared_5766_; uint8_t v_isSharedCheck_5770_; 
lean_dec(v_a_5749_);
lean_dec(v_mvarId_5737_);
lean_dec_ref(v_sstates_5736_);
lean_dec_ref(v_clean_5735_);
lean_dec_ref(v_split_5734_);
lean_dec_ref(v_inj_5733_);
lean_dec_ref(v_extThms_5732_);
lean_dec_ref(v_facts_5731_);
lean_dec_ref(v_newRawFacts_5730_);
lean_dec(v_nextIdx_5729_);
lean_dec_ref(v_toProcess_5727_);
lean_dec_ref(v_indicesFound_5726_);
lean_dec_ref(v_appMap_5725_);
lean_dec_ref(v_congrTable_5724_);
lean_dec_ref(v_parents_5723_);
lean_dec_ref(v_exprs_5722_);
lean_dec_ref(v_enodeMap_5721_);
lean_dec(v_nextDeclIdx_5720_);
lean_dec_ref(v_delayedThmInsts_5719_);
lean_dec_ref(v_matchEqNames_5718_);
lean_dec(v_nextThmIdx_5717_);
lean_dec_ref(v_preInstances_5716_);
lean_dec(v_num_5715_);
lean_dec(v_numDelayedInstances_5714_);
lean_dec(v_numInstances_5713_);
lean_dec(v_gmt_5712_);
v_a_5763_ = lean_ctor_get(v___x_5750_, 0);
v_isSharedCheck_5770_ = !lean_is_exclusive(v___x_5750_);
if (v_isSharedCheck_5770_ == 0)
{
v___x_5765_ = v___x_5750_;
v_isShared_5766_ = v_isSharedCheck_5770_;
goto v_resetjp_5764_;
}
else
{
lean_inc(v_a_5763_);
lean_dec(v___x_5750_);
v___x_5765_ = lean_box(0);
v_isShared_5766_ = v_isSharedCheck_5770_;
goto v_resetjp_5764_;
}
v_resetjp_5764_:
{
lean_object* v___x_5768_; 
if (v_isShared_5766_ == 0)
{
v___x_5768_ = v___x_5765_;
goto v_reusejp_5767_;
}
else
{
lean_object* v_reuseFailAlloc_5769_; 
v_reuseFailAlloc_5769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5769_, 0, v_a_5763_);
v___x_5768_ = v_reuseFailAlloc_5769_;
goto v_reusejp_5767_;
}
v_reusejp_5767_:
{
return v___x_5768_;
}
}
}
}
else
{
lean_object* v_a_5771_; lean_object* v___x_5773_; uint8_t v_isShared_5774_; uint8_t v_isSharedCheck_5778_; 
lean_dec(v_mvarId_5737_);
lean_dec_ref(v_sstates_5736_);
lean_dec_ref(v_clean_5735_);
lean_dec_ref(v_split_5734_);
lean_dec_ref(v_inj_5733_);
lean_dec_ref(v_extThms_5732_);
lean_dec_ref(v_facts_5731_);
lean_dec_ref(v_newRawFacts_5730_);
lean_dec(v_nextIdx_5729_);
lean_dec_ref(v_toProcess_5727_);
lean_dec_ref(v_indicesFound_5726_);
lean_dec_ref(v_appMap_5725_);
lean_dec_ref(v_congrTable_5724_);
lean_dec_ref(v_parents_5723_);
lean_dec_ref(v_exprs_5722_);
lean_dec_ref(v_enodeMap_5721_);
lean_dec(v_nextDeclIdx_5720_);
lean_dec_ref(v_delayedThmInsts_5719_);
lean_dec_ref(v_matchEqNames_5718_);
lean_dec(v_nextThmIdx_5717_);
lean_dec_ref(v_preInstances_5716_);
lean_dec(v_num_5715_);
lean_dec(v_numDelayedInstances_5714_);
lean_dec(v_numInstances_5713_);
lean_dec(v_gmt_5712_);
v_a_5771_ = lean_ctor_get(v___x_5748_, 0);
v_isSharedCheck_5778_ = !lean_is_exclusive(v___x_5748_);
if (v_isSharedCheck_5778_ == 0)
{
v___x_5773_ = v___x_5748_;
v_isShared_5774_ = v_isSharedCheck_5778_;
goto v_resetjp_5772_;
}
else
{
lean_inc(v_a_5771_);
lean_dec(v___x_5748_);
v___x_5773_ = lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5778_;
goto v_resetjp_5772_;
}
v_resetjp_5772_:
{
lean_object* v___x_5776_; 
if (v_isShared_5774_ == 0)
{
v___x_5776_ = v___x_5773_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_a_5771_);
v___x_5776_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
return v___x_5776_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_thms_5710_ = stack[0].m_obj;
lean_object* v_newThms_5711_ = stack[1].m_obj;
lean_object* v_gmt_5712_ = stack[2].m_obj;
lean_object* v_numInstances_5713_ = stack[3].m_obj;
lean_object* v_numDelayedInstances_5714_ = stack[4].m_obj;
lean_object* v_num_5715_ = stack[5].m_obj;
lean_object* v_preInstances_5716_ = stack[6].m_obj;
lean_object* v_nextThmIdx_5717_ = stack[7].m_obj;
lean_object* v_matchEqNames_5718_ = stack[8].m_obj;
lean_object* v_delayedThmInsts_5719_ = stack[9].m_obj;
lean_object* v_nextDeclIdx_5720_ = stack[10].m_obj;
lean_object* v_enodeMap_5721_ = stack[11].m_obj;
lean_object* v_exprs_5722_ = stack[12].m_obj;
lean_object* v_parents_5723_ = stack[13].m_obj;
lean_object* v_congrTable_5724_ = stack[14].m_obj;
lean_object* v_appMap_5725_ = stack[15].m_obj;
lean_object* v_indicesFound_5726_ = stack[16].m_obj;
lean_object* v_toProcess_5727_ = stack[17].m_obj;
uint8_t v_inconsistent_5728_ = stack[18].m_num;
lean_object* v_nextIdx_5729_ = stack[19].m_obj;
lean_object* v_newRawFacts_5730_ = stack[20].m_obj;
lean_object* v_facts_5731_ = stack[21].m_obj;
lean_object* v_extThms_5732_ = stack[22].m_obj;
lean_object* v_inj_5733_ = stack[23].m_obj;
lean_object* v_split_5734_ = stack[24].m_obj;
lean_object* v_clean_5735_ = stack[25].m_obj;
lean_object* v_sstates_5736_ = stack[26].m_obj;
lean_object* v_mvarId_5737_ = stack[27].m_obj;
lean_object* v___y_5738_ = stack[28].m_obj;
lean_object* v___y_5739_ = stack[29].m_obj;
lean_object* v___y_5740_ = stack[30].m_obj;
lean_object* v___y_5741_ = stack[31].m_obj;
lean_object* v___y_5742_ = stack[32].m_obj;
lean_object* v___y_5743_ = stack[33].m_obj;
lean_object* v___y_5744_ = stack[34].m_obj;
lean_object* v___y_5745_ = stack[35].m_obj;
lean_object* v___y_5746_ = stack[36].m_obj;
lean_object* v_res_5779_;
v_res_5779_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_5710_, v_newThms_5711_, v_gmt_5712_, v_numInstances_5713_, v_numDelayedInstances_5714_, v_num_5715_, v_preInstances_5716_, v_nextThmIdx_5717_, v_matchEqNames_5718_, v_delayedThmInsts_5719_, v_nextDeclIdx_5720_, v_enodeMap_5721_, v_exprs_5722_, v_parents_5723_, v_congrTable_5724_, v_appMap_5725_, v_indicesFound_5726_, v_toProcess_5727_, v_inconsistent_5728_, v_nextIdx_5729_, v_newRawFacts_5730_, v_facts_5731_, v_extThms_5732_, v_inj_5733_, v_split_5734_, v_clean_5735_, v_sstates_5736_, v_mvarId_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_);
stack->m_obj
 = v_res_5779_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_5780_ = _args[0];
lean_object* v_newThms_5781_ = _args[1];
lean_object* v_gmt_5782_ = _args[2];
lean_object* v_numInstances_5783_ = _args[3];
lean_object* v_numDelayedInstances_5784_ = _args[4];
lean_object* v_num_5785_ = _args[5];
lean_object* v_preInstances_5786_ = _args[6];
lean_object* v_nextThmIdx_5787_ = _args[7];
lean_object* v_matchEqNames_5788_ = _args[8];
lean_object* v_delayedThmInsts_5789_ = _args[9];
lean_object* v_nextDeclIdx_5790_ = _args[10];
lean_object* v_enodeMap_5791_ = _args[11];
lean_object* v_exprs_5792_ = _args[12];
lean_object* v_parents_5793_ = _args[13];
lean_object* v_congrTable_5794_ = _args[14];
lean_object* v_appMap_5795_ = _args[15];
lean_object* v_indicesFound_5796_ = _args[16];
lean_object* v_toProcess_5797_ = _args[17];
lean_object* v_inconsistent_5798_ = _args[18];
lean_object* v_nextIdx_5799_ = _args[19];
lean_object* v_newRawFacts_5800_ = _args[20];
lean_object* v_facts_5801_ = _args[21];
lean_object* v_extThms_5802_ = _args[22];
lean_object* v_inj_5803_ = _args[23];
lean_object* v_split_5804_ = _args[24];
lean_object* v_clean_5805_ = _args[25];
lean_object* v_sstates_5806_ = _args[26];
lean_object* v_mvarId_5807_ = _args[27];
lean_object* v___y_5808_ = _args[28];
lean_object* v___y_5809_ = _args[29];
lean_object* v___y_5810_ = _args[30];
lean_object* v___y_5811_ = _args[31];
lean_object* v___y_5812_ = _args[32];
lean_object* v___y_5813_ = _args[33];
lean_object* v___y_5814_ = _args[34];
lean_object* v___y_5815_ = _args[35];
lean_object* v___y_5816_ = _args[36];
lean_object* v___y_5817_ = _args[37];
_start:
{
uint8_t v_inconsistent_boxed_5818_; lean_object* v_res_5819_; 
v_inconsistent_boxed_5818_ = lean_unbox(v_inconsistent_5798_);
v_res_5819_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_5780_, v_newThms_5781_, v_gmt_5782_, v_numInstances_5783_, v_numDelayedInstances_5784_, v_num_5785_, v_preInstances_5786_, v_nextThmIdx_5787_, v_matchEqNames_5788_, v_delayedThmInsts_5789_, v_nextDeclIdx_5790_, v_enodeMap_5791_, v_exprs_5792_, v_parents_5793_, v_congrTable_5794_, v_appMap_5795_, v_indicesFound_5796_, v_toProcess_5797_, v_inconsistent_boxed_5818_, v_nextIdx_5799_, v_newRawFacts_5800_, v_facts_5801_, v_extThms_5802_, v_inj_5803_, v_split_5804_, v_clean_5805_, v_sstates_5806_, v_mvarId_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_);
lean_dec(v___y_5816_);
lean_dec_ref(v___y_5815_);
lean_dec(v___y_5814_);
lean_dec_ref(v___y_5813_);
lean_dec(v___y_5812_);
lean_dec_ref(v___y_5811_);
lean_dec(v___y_5810_);
lean_dec_ref(v___y_5809_);
lean_dec(v___y_5808_);
lean_dec_ref(v_newThms_5781_);
lean_dec_ref(v_thms_5780_);
return v_res_5819_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5820_; 
v___x_5820_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_5820_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_5821_, size_t v_i_5822_, lean_object* v_bs_5823_){
_start:
{
uint8_t v___x_5824_; 
v___x_5824_ = lean_usize_dec_lt(v_i_5822_, v_sz_5821_);
if (v___x_5824_ == 0)
{
return v_bs_5823_;
}
else
{
lean_object* v_v_5825_; lean_object* v_casesTypes_5826_; lean_object* v_extThms_5827_; lean_object* v_funCC_5828_; lean_object* v_inj_5829_; lean_object* v___x_5831_; uint8_t v_isShared_5832_; uint8_t v_isSharedCheck_5843_; 
v_v_5825_ = lean_array_uget(v_bs_5823_, v_i_5822_);
v_casesTypes_5826_ = lean_ctor_get(v_v_5825_, 0);
v_extThms_5827_ = lean_ctor_get(v_v_5825_, 1);
v_funCC_5828_ = lean_ctor_get(v_v_5825_, 2);
v_inj_5829_ = lean_ctor_get(v_v_5825_, 4);
v_isSharedCheck_5843_ = !lean_is_exclusive(v_v_5825_);
if (v_isSharedCheck_5843_ == 0)
{
lean_object* v_unused_5844_; 
v_unused_5844_ = lean_ctor_get(v_v_5825_, 3);
lean_dec(v_unused_5844_);
v___x_5831_ = v_v_5825_;
v_isShared_5832_ = v_isSharedCheck_5843_;
goto v_resetjp_5830_;
}
else
{
lean_inc(v_inj_5829_);
lean_inc(v_funCC_5828_);
lean_inc(v_extThms_5827_);
lean_inc(v_casesTypes_5826_);
lean_dec(v_v_5825_);
v___x_5831_ = lean_box(0);
v_isShared_5832_ = v_isSharedCheck_5843_;
goto v_resetjp_5830_;
}
v_resetjp_5830_:
{
lean_object* v___x_5833_; lean_object* v_bs_x27_5834_; lean_object* v___x_5835_; lean_object* v___x_5837_; 
v___x_5833_ = lean_unsigned_to_nat(0u);
v_bs_x27_5834_ = lean_array_uset(v_bs_5823_, v_i_5822_, v___x_5833_);
v___x_5835_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_5832_ == 0)
{
lean_ctor_set(v___x_5831_, 3, v___x_5835_);
v___x_5837_ = v___x_5831_;
goto v_reusejp_5836_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v_casesTypes_5826_);
lean_ctor_set(v_reuseFailAlloc_5842_, 1, v_extThms_5827_);
lean_ctor_set(v_reuseFailAlloc_5842_, 2, v_funCC_5828_);
lean_ctor_set(v_reuseFailAlloc_5842_, 3, v___x_5835_);
lean_ctor_set(v_reuseFailAlloc_5842_, 4, v_inj_5829_);
v___x_5837_ = v_reuseFailAlloc_5842_;
goto v_reusejp_5836_;
}
v_reusejp_5836_:
{
size_t v___x_5838_; size_t v___x_5839_; lean_object* v___x_5840_; 
v___x_5838_ = ((size_t)1ULL);
v___x_5839_ = lean_usize_add(v_i_5822_, v___x_5838_);
v___x_5840_ = lean_array_uset(v_bs_x27_5834_, v_i_5822_, v___x_5837_);
v_i_5822_ = v___x_5839_;
v_bs_5823_ = v___x_5840_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_5821_ = stack[0].m_num;
size_t v_i_5822_ = stack[1].m_num;
lean_object* v_bs_5823_ = stack[2].m_obj;
lean_object* v_res_5845_;
v_res_5845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_5821_, v_i_5822_, v_bs_5823_);
stack->m_obj
 = v_res_5845_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_5846_, lean_object* v_i_5847_, lean_object* v_bs_5848_){
_start:
{
size_t v_sz_boxed_5849_; size_t v_i_boxed_5850_; lean_object* v_res_5851_; 
v_sz_boxed_5849_ = lean_unbox_usize(v_sz_5846_);
lean_dec(v_sz_5846_);
v_i_boxed_5850_ = lean_unbox_usize(v_i_5847_);
lean_dec(v_i_5847_);
v_res_5851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_5849_, v_i_boxed_5850_, v_bs_5848_);
return v_res_5851_;
}
}
lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_5852_, lean_object* v_ps_5853_, uint8_t v_only_5854_, lean_object* v_k_5855_, lean_object* v_a_5856_, lean_object* v_a_5857_, lean_object* v_a_5858_, lean_object* v_a_5859_, lean_object* v_a_5860_, lean_object* v_a_5861_, lean_object* v_a_5862_, lean_object* v_a_5863_){
_start:
{
lean_object* v___y_5866_; lean_object* v___y_5867_; lean_object* v___y_5868_; lean_object* v___y_5869_; lean_object* v___y_5870_; lean_object* v___y_5871_; lean_object* v___y_5872_; lean_object* v___y_5873_; lean_object* v___y_5874_; uint8_t v___y_5887_; uint8_t v___y_5888_; lean_object* v_params_5889_; lean_object* v___y_5890_; lean_object* v___y_5891_; lean_object* v___y_5892_; lean_object* v___y_5893_; lean_object* v___y_5894_; lean_object* v___y_5895_; lean_object* v___y_5896_; lean_object* v___y_5897_; uint8_t v___y_6000_; 
if (v_only_5854_ == 0)
{
lean_object* v___x_6022_; lean_object* v___x_6023_; uint8_t v___x_6024_; 
v___x_6022_ = lean_array_get_size(v_ps_5853_);
v___x_6023_ = lean_unsigned_to_nat(0u);
v___x_6024_ = lean_nat_dec_eq(v___x_6022_, v___x_6023_);
if (v___x_6024_ == 0)
{
v___y_6000_ = v___x_6024_;
goto v___jp_5999_;
}
else
{
lean_object* v___x_6025_; 
lean_dec_ref(v_params_5852_);
lean_inc(v_a_5863_);
lean_inc_ref(v_a_5862_);
lean_inc(v_a_5861_);
lean_inc_ref(v_a_5860_);
lean_inc(v_a_5859_);
lean_inc_ref(v_a_5858_);
lean_inc(v_a_5857_);
lean_inc_ref(v_a_5856_);
v___x_6025_ = lean_apply_9(v_k_5855_, v_a_5856_, v_a_5857_, v_a_5858_, v_a_5859_, v_a_5860_, v_a_5861_, v_a_5862_, v_a_5863_, lean_box(0));
return v___x_6025_;
}
}
else
{
uint8_t v___x_6026_; 
v___x_6026_ = 0;
v___y_6000_ = v___x_6026_;
goto v___jp_5999_;
}
v___jp_5865_:
{
lean_object* v___x_5875_; lean_object* v___x_5876_; 
v___x_5875_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_5875_, 0, v___y_5866_);
v___x_5876_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_5875_, v___y_5867_, v___y_5868_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_);
if (lean_obj_tag(v___x_5876_) == 0)
{
lean_object* v___x_5877_; 
lean_dec_ref_known(v___x_5876_, 1);
lean_inc(v___y_5874_);
lean_inc_ref(v___y_5873_);
lean_inc(v___y_5872_);
lean_inc_ref(v___y_5871_);
lean_inc(v___y_5870_);
lean_inc_ref(v___y_5869_);
lean_inc(v___y_5868_);
v___x_5877_ = lean_apply_9(v_k_5855_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, lean_box(0));
return v___x_5877_;
}
else
{
lean_object* v_a_5878_; lean_object* v___x_5880_; uint8_t v_isShared_5881_; uint8_t v_isSharedCheck_5885_; 
lean_dec_ref(v___y_5867_);
lean_dec_ref(v_k_5855_);
v_a_5878_ = lean_ctor_get(v___x_5876_, 0);
v_isSharedCheck_5885_ = !lean_is_exclusive(v___x_5876_);
if (v_isSharedCheck_5885_ == 0)
{
v___x_5880_ = v___x_5876_;
v_isShared_5881_ = v_isSharedCheck_5885_;
goto v_resetjp_5879_;
}
else
{
lean_inc(v_a_5878_);
lean_dec(v___x_5876_);
v___x_5880_ = lean_box(0);
v_isShared_5881_ = v_isSharedCheck_5885_;
goto v_resetjp_5879_;
}
v_resetjp_5879_:
{
lean_object* v___x_5883_; 
if (v_isShared_5881_ == 0)
{
v___x_5883_ = v___x_5880_;
goto v_reusejp_5882_;
}
else
{
lean_object* v_reuseFailAlloc_5884_; 
v_reuseFailAlloc_5884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5884_, 0, v_a_5878_);
v___x_5883_ = v_reuseFailAlloc_5884_;
goto v_reusejp_5882_;
}
v_reusejp_5882_:
{
return v___x_5883_;
}
}
}
}
v___jp_5886_:
{
lean_object* v___x_5898_; 
v___x_5898_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5889_, v_ps_5853_, v_only_5854_, v___y_5888_, v___y_5887_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_);
if (lean_obj_tag(v___x_5898_) == 0)
{
lean_object* v_a_5899_; lean_object* v_ctx_5900_; lean_object* v_anchorRefs_x3f_5901_; lean_object* v_toContext_5902_; lean_object* v_sctx_5903_; lean_object* v_methods_5904_; uint8_t v_sym_5905_; lean_object* v_simp_5906_; lean_object* v_simpMethods_5907_; lean_object* v_symSimpMethods_5908_; lean_object* v_symDSimpMethods_5909_; lean_object* v_config_5910_; uint8_t v_cheapCases_5911_; uint8_t v_reportMVarIssue_5912_; lean_object* v_splitSource_5913_; lean_object* v_ematchDiagSource_5914_; lean_object* v_symPrios_5915_; lean_object* v_extensions_5916_; uint8_t v_debug_5917_; uint8_t v_ematchDiag_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; 
v_a_5899_ = lean_ctor_get(v___x_5898_, 0);
lean_inc_n(v_a_5899_, 2);
lean_dec_ref_known(v___x_5898_, 1);
v_ctx_5900_ = lean_ctor_get(v___y_5890_, 1);
v_anchorRefs_x3f_5901_ = lean_ctor_get(v_a_5899_, 8);
v_toContext_5902_ = lean_ctor_get(v___y_5890_, 0);
v_sctx_5903_ = lean_ctor_get(v___y_5890_, 2);
v_methods_5904_ = lean_ctor_get(v___y_5890_, 3);
v_sym_5905_ = lean_ctor_get_uint8(v___y_5890_, sizeof(void*)*5);
v_simp_5906_ = lean_ctor_get(v_ctx_5900_, 0);
v_simpMethods_5907_ = lean_ctor_get(v_ctx_5900_, 1);
v_symSimpMethods_5908_ = lean_ctor_get(v_ctx_5900_, 2);
v_symDSimpMethods_5909_ = lean_ctor_get(v_ctx_5900_, 3);
v_config_5910_ = lean_ctor_get(v_ctx_5900_, 4);
v_cheapCases_5911_ = lean_ctor_get_uint8(v_ctx_5900_, sizeof(void*)*10);
v_reportMVarIssue_5912_ = lean_ctor_get_uint8(v_ctx_5900_, sizeof(void*)*10 + 1);
v_splitSource_5913_ = lean_ctor_get(v_ctx_5900_, 6);
v_ematchDiagSource_5914_ = lean_ctor_get(v_ctx_5900_, 7);
v_symPrios_5915_ = lean_ctor_get(v_ctx_5900_, 8);
v_extensions_5916_ = lean_ctor_get(v_ctx_5900_, 9);
v_debug_5917_ = lean_ctor_get_uint8(v_ctx_5900_, sizeof(void*)*10 + 2);
v_ematchDiag_5918_ = lean_ctor_get_uint8(v_ctx_5900_, sizeof(void*)*10 + 3);
lean_inc_ref(v_extensions_5916_);
lean_inc_ref(v_symPrios_5915_);
lean_inc(v_ematchDiagSource_5914_);
lean_inc(v_splitSource_5913_);
lean_inc(v_anchorRefs_x3f_5901_);
lean_inc_ref(v_config_5910_);
lean_inc_ref(v_symDSimpMethods_5909_);
lean_inc_ref(v_symSimpMethods_5908_);
lean_inc_ref(v_simpMethods_5907_);
lean_inc_ref(v_simp_5906_);
v___x_5919_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_5919_, 0, v_simp_5906_);
lean_ctor_set(v___x_5919_, 1, v_simpMethods_5907_);
lean_ctor_set(v___x_5919_, 2, v_symSimpMethods_5908_);
lean_ctor_set(v___x_5919_, 3, v_symDSimpMethods_5909_);
lean_ctor_set(v___x_5919_, 4, v_config_5910_);
lean_ctor_set(v___x_5919_, 5, v_anchorRefs_x3f_5901_);
lean_ctor_set(v___x_5919_, 6, v_splitSource_5913_);
lean_ctor_set(v___x_5919_, 7, v_ematchDiagSource_5914_);
lean_ctor_set(v___x_5919_, 8, v_symPrios_5915_);
lean_ctor_set(v___x_5919_, 9, v_extensions_5916_);
lean_ctor_set_uint8(v___x_5919_, sizeof(void*)*10, v_cheapCases_5911_);
lean_ctor_set_uint8(v___x_5919_, sizeof(void*)*10 + 1, v_reportMVarIssue_5912_);
lean_ctor_set_uint8(v___x_5919_, sizeof(void*)*10 + 2, v_debug_5917_);
lean_ctor_set_uint8(v___x_5919_, sizeof(void*)*10 + 3, v_ematchDiag_5918_);
lean_inc_ref(v_methods_5904_);
lean_inc_ref(v_sctx_5903_);
lean_inc_ref(v_toContext_5902_);
v___x_5920_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_5920_, 0, v_toContext_5902_);
lean_ctor_set(v___x_5920_, 1, v___x_5919_);
lean_ctor_set(v___x_5920_, 2, v_sctx_5903_);
lean_ctor_set(v___x_5920_, 3, v_methods_5904_);
lean_ctor_set(v___x_5920_, 4, v_a_5899_);
lean_ctor_set_uint8(v___x_5920_, sizeof(void*)*5, v_sym_5905_);
if (v_only_5854_ == 0)
{
v___y_5866_ = v_a_5899_;
v___y_5867_ = v___x_5920_;
v___y_5868_ = v___y_5891_;
v___y_5869_ = v___y_5892_;
v___y_5870_ = v___y_5893_;
v___y_5871_ = v___y_5894_;
v___y_5872_ = v___y_5895_;
v___y_5873_ = v___y_5896_;
v___y_5874_ = v___y_5897_;
goto v___jp_5865_;
}
else
{
lean_object* v___x_5921_; 
v___x_5921_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_5891_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_);
if (lean_obj_tag(v___x_5921_) == 0)
{
lean_object* v_a_5922_; lean_object* v_toGoalState_5923_; lean_object* v_ematch_5924_; lean_object* v_mvarId_5925_; lean_object* v___x_5927_; uint8_t v_isShared_5928_; uint8_t v_isSharedCheck_5981_; 
v_a_5922_ = lean_ctor_get(v___x_5921_, 0);
lean_inc(v_a_5922_);
lean_dec_ref_known(v___x_5921_, 1);
v_toGoalState_5923_ = lean_ctor_get(v_a_5922_, 0);
lean_inc_ref(v_toGoalState_5923_);
v_ematch_5924_ = lean_ctor_get(v_toGoalState_5923_, 12);
lean_inc_ref(v_ematch_5924_);
v_mvarId_5925_ = lean_ctor_get(v_a_5922_, 1);
v_isSharedCheck_5981_ = !lean_is_exclusive(v_a_5922_);
if (v_isSharedCheck_5981_ == 0)
{
lean_object* v_unused_5982_; 
v_unused_5982_ = lean_ctor_get(v_a_5922_, 0);
lean_dec(v_unused_5982_);
v___x_5927_ = v_a_5922_;
v_isShared_5928_ = v_isSharedCheck_5981_;
goto v_resetjp_5926_;
}
else
{
lean_inc(v_mvarId_5925_);
lean_dec(v_a_5922_);
v___x_5927_ = lean_box(0);
v_isShared_5928_ = v_isSharedCheck_5981_;
goto v_resetjp_5926_;
}
v_resetjp_5926_:
{
lean_object* v_nextDeclIdx_5929_; lean_object* v_enodeMap_5930_; lean_object* v_exprs_5931_; lean_object* v_parents_5932_; lean_object* v_congrTable_5933_; lean_object* v_appMap_5934_; lean_object* v_indicesFound_5935_; lean_object* v_toProcess_5936_; uint8_t v_inconsistent_5937_; lean_object* v_nextIdx_5938_; lean_object* v_newRawFacts_5939_; lean_object* v_facts_5940_; lean_object* v_extThms_5941_; lean_object* v_inj_5942_; lean_object* v_split_5943_; lean_object* v_clean_5944_; lean_object* v_sstates_5945_; lean_object* v_gmt_5946_; lean_object* v_thms_5947_; lean_object* v_newThms_5948_; lean_object* v_numInstances_5949_; lean_object* v_numDelayedInstances_5950_; lean_object* v_num_5951_; lean_object* v_preInstances_5952_; lean_object* v_nextThmIdx_5953_; lean_object* v_matchEqNames_5954_; lean_object* v_delayedThmInsts_5955_; lean_object* v___x_5956_; lean_object* v___f_5957_; lean_object* v___x_5958_; 
v_nextDeclIdx_5929_ = lean_ctor_get(v_toGoalState_5923_, 0);
lean_inc(v_nextDeclIdx_5929_);
v_enodeMap_5930_ = lean_ctor_get(v_toGoalState_5923_, 1);
lean_inc_ref(v_enodeMap_5930_);
v_exprs_5931_ = lean_ctor_get(v_toGoalState_5923_, 2);
lean_inc_ref(v_exprs_5931_);
v_parents_5932_ = lean_ctor_get(v_toGoalState_5923_, 3);
lean_inc_ref(v_parents_5932_);
v_congrTable_5933_ = lean_ctor_get(v_toGoalState_5923_, 4);
lean_inc_ref(v_congrTable_5933_);
v_appMap_5934_ = lean_ctor_get(v_toGoalState_5923_, 5);
lean_inc_ref(v_appMap_5934_);
v_indicesFound_5935_ = lean_ctor_get(v_toGoalState_5923_, 6);
lean_inc_ref(v_indicesFound_5935_);
v_toProcess_5936_ = lean_ctor_get(v_toGoalState_5923_, 7);
lean_inc_ref(v_toProcess_5936_);
v_inconsistent_5937_ = lean_ctor_get_uint8(v_toGoalState_5923_, sizeof(void*)*17);
v_nextIdx_5938_ = lean_ctor_get(v_toGoalState_5923_, 8);
lean_inc(v_nextIdx_5938_);
v_newRawFacts_5939_ = lean_ctor_get(v_toGoalState_5923_, 9);
lean_inc_ref(v_newRawFacts_5939_);
v_facts_5940_ = lean_ctor_get(v_toGoalState_5923_, 10);
lean_inc_ref(v_facts_5940_);
v_extThms_5941_ = lean_ctor_get(v_toGoalState_5923_, 11);
lean_inc_ref(v_extThms_5941_);
v_inj_5942_ = lean_ctor_get(v_toGoalState_5923_, 13);
lean_inc_ref(v_inj_5942_);
v_split_5943_ = lean_ctor_get(v_toGoalState_5923_, 14);
lean_inc_ref(v_split_5943_);
v_clean_5944_ = lean_ctor_get(v_toGoalState_5923_, 15);
lean_inc_ref(v_clean_5944_);
v_sstates_5945_ = lean_ctor_get(v_toGoalState_5923_, 16);
lean_inc_ref(v_sstates_5945_);
lean_dec_ref(v_toGoalState_5923_);
v_gmt_5946_ = lean_ctor_get(v_ematch_5924_, 1);
lean_inc(v_gmt_5946_);
v_thms_5947_ = lean_ctor_get(v_ematch_5924_, 2);
lean_inc_ref(v_thms_5947_);
v_newThms_5948_ = lean_ctor_get(v_ematch_5924_, 3);
lean_inc_ref(v_newThms_5948_);
v_numInstances_5949_ = lean_ctor_get(v_ematch_5924_, 4);
lean_inc(v_numInstances_5949_);
v_numDelayedInstances_5950_ = lean_ctor_get(v_ematch_5924_, 5);
lean_inc(v_numDelayedInstances_5950_);
v_num_5951_ = lean_ctor_get(v_ematch_5924_, 6);
lean_inc(v_num_5951_);
v_preInstances_5952_ = lean_ctor_get(v_ematch_5924_, 7);
lean_inc_ref(v_preInstances_5952_);
v_nextThmIdx_5953_ = lean_ctor_get(v_ematch_5924_, 8);
lean_inc(v_nextThmIdx_5953_);
v_matchEqNames_5954_ = lean_ctor_get(v_ematch_5924_, 9);
lean_inc_ref(v_matchEqNames_5954_);
v_delayedThmInsts_5955_ = lean_ctor_get(v_ematch_5924_, 10);
lean_inc_ref(v_delayedThmInsts_5955_);
lean_dec_ref(v_ematch_5924_);
v___x_5956_ = lean_box(v_inconsistent_5937_);
v___f_5957_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 38, 28);
lean_closure_set(v___f_5957_, 0, v_thms_5947_);
lean_closure_set(v___f_5957_, 1, v_newThms_5948_);
lean_closure_set(v___f_5957_, 2, v_gmt_5946_);
lean_closure_set(v___f_5957_, 3, v_numInstances_5949_);
lean_closure_set(v___f_5957_, 4, v_numDelayedInstances_5950_);
lean_closure_set(v___f_5957_, 5, v_num_5951_);
lean_closure_set(v___f_5957_, 6, v_preInstances_5952_);
lean_closure_set(v___f_5957_, 7, v_nextThmIdx_5953_);
lean_closure_set(v___f_5957_, 8, v_matchEqNames_5954_);
lean_closure_set(v___f_5957_, 9, v_delayedThmInsts_5955_);
lean_closure_set(v___f_5957_, 10, v_nextDeclIdx_5929_);
lean_closure_set(v___f_5957_, 11, v_enodeMap_5930_);
lean_closure_set(v___f_5957_, 12, v_exprs_5931_);
lean_closure_set(v___f_5957_, 13, v_parents_5932_);
lean_closure_set(v___f_5957_, 14, v_congrTable_5933_);
lean_closure_set(v___f_5957_, 15, v_appMap_5934_);
lean_closure_set(v___f_5957_, 16, v_indicesFound_5935_);
lean_closure_set(v___f_5957_, 17, v_toProcess_5936_);
lean_closure_set(v___f_5957_, 18, v___x_5956_);
lean_closure_set(v___f_5957_, 19, v_nextIdx_5938_);
lean_closure_set(v___f_5957_, 20, v_newRawFacts_5939_);
lean_closure_set(v___f_5957_, 21, v_facts_5940_);
lean_closure_set(v___f_5957_, 22, v_extThms_5941_);
lean_closure_set(v___f_5957_, 23, v_inj_5942_);
lean_closure_set(v___f_5957_, 24, v_split_5943_);
lean_closure_set(v___f_5957_, 25, v_clean_5944_);
lean_closure_set(v___f_5957_, 26, v_sstates_5945_);
lean_closure_set(v___f_5957_, 27, v_mvarId_5925_);
v___x_5958_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_5957_, v___x_5920_, v___y_5891_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_);
if (lean_obj_tag(v___x_5958_) == 0)
{
lean_object* v_a_5959_; lean_object* v___x_5960_; lean_object* v___x_5962_; 
v_a_5959_ = lean_ctor_get(v___x_5958_, 0);
lean_inc(v_a_5959_);
lean_dec_ref_known(v___x_5958_, 1);
v___x_5960_ = lean_box(0);
if (v_isShared_5928_ == 0)
{
lean_ctor_set_tag(v___x_5927_, 1);
lean_ctor_set(v___x_5927_, 1, v___x_5960_);
lean_ctor_set(v___x_5927_, 0, v_a_5959_);
v___x_5962_ = v___x_5927_;
goto v_reusejp_5961_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_a_5959_);
lean_ctor_set(v_reuseFailAlloc_5972_, 1, v___x_5960_);
v___x_5962_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5961_;
}
v_reusejp_5961_:
{
lean_object* v___x_5963_; 
v___x_5963_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_5962_, v___y_5891_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_);
if (lean_obj_tag(v___x_5963_) == 0)
{
lean_dec_ref_known(v___x_5963_, 1);
v___y_5866_ = v_a_5899_;
v___y_5867_ = v___x_5920_;
v___y_5868_ = v___y_5891_;
v___y_5869_ = v___y_5892_;
v___y_5870_ = v___y_5893_;
v___y_5871_ = v___y_5894_;
v___y_5872_ = v___y_5895_;
v___y_5873_ = v___y_5896_;
v___y_5874_ = v___y_5897_;
goto v___jp_5865_;
}
else
{
lean_object* v_a_5964_; lean_object* v___x_5966_; uint8_t v_isShared_5967_; uint8_t v_isSharedCheck_5971_; 
lean_dec_ref_known(v___x_5920_, 5);
lean_dec(v_a_5899_);
lean_dec_ref(v_k_5855_);
v_a_5964_ = lean_ctor_get(v___x_5963_, 0);
v_isSharedCheck_5971_ = !lean_is_exclusive(v___x_5963_);
if (v_isSharedCheck_5971_ == 0)
{
v___x_5966_ = v___x_5963_;
v_isShared_5967_ = v_isSharedCheck_5971_;
goto v_resetjp_5965_;
}
else
{
lean_inc(v_a_5964_);
lean_dec(v___x_5963_);
v___x_5966_ = lean_box(0);
v_isShared_5967_ = v_isSharedCheck_5971_;
goto v_resetjp_5965_;
}
v_resetjp_5965_:
{
lean_object* v___x_5969_; 
if (v_isShared_5967_ == 0)
{
v___x_5969_ = v___x_5966_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v_a_5964_);
v___x_5969_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
return v___x_5969_;
}
}
}
}
}
else
{
lean_object* v_a_5973_; lean_object* v___x_5975_; uint8_t v_isShared_5976_; uint8_t v_isSharedCheck_5980_; 
lean_del_object(v___x_5927_);
lean_dec_ref_known(v___x_5920_, 5);
lean_dec(v_a_5899_);
lean_dec_ref(v_k_5855_);
v_a_5973_ = lean_ctor_get(v___x_5958_, 0);
v_isSharedCheck_5980_ = !lean_is_exclusive(v___x_5958_);
if (v_isSharedCheck_5980_ == 0)
{
v___x_5975_ = v___x_5958_;
v_isShared_5976_ = v_isSharedCheck_5980_;
goto v_resetjp_5974_;
}
else
{
lean_inc(v_a_5973_);
lean_dec(v___x_5958_);
v___x_5975_ = lean_box(0);
v_isShared_5976_ = v_isSharedCheck_5980_;
goto v_resetjp_5974_;
}
v_resetjp_5974_:
{
lean_object* v___x_5978_; 
if (v_isShared_5976_ == 0)
{
v___x_5978_ = v___x_5975_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v_a_5973_);
v___x_5978_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
return v___x_5978_;
}
}
}
}
}
else
{
lean_object* v_a_5983_; lean_object* v___x_5985_; uint8_t v_isShared_5986_; uint8_t v_isSharedCheck_5990_; 
lean_dec_ref_known(v___x_5920_, 5);
lean_dec(v_a_5899_);
lean_dec_ref(v_k_5855_);
v_a_5983_ = lean_ctor_get(v___x_5921_, 0);
v_isSharedCheck_5990_ = !lean_is_exclusive(v___x_5921_);
if (v_isSharedCheck_5990_ == 0)
{
v___x_5985_ = v___x_5921_;
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
else
{
lean_inc(v_a_5983_);
lean_dec(v___x_5921_);
v___x_5985_ = lean_box(0);
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
v_resetjp_5984_:
{
lean_object* v___x_5988_; 
if (v_isShared_5986_ == 0)
{
v___x_5988_ = v___x_5985_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_a_5983_);
v___x_5988_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
return v___x_5988_;
}
}
}
}
}
else
{
lean_object* v_a_5991_; lean_object* v___x_5993_; uint8_t v_isShared_5994_; uint8_t v_isSharedCheck_5998_; 
lean_dec_ref(v_k_5855_);
v_a_5991_ = lean_ctor_get(v___x_5898_, 0);
v_isSharedCheck_5998_ = !lean_is_exclusive(v___x_5898_);
if (v_isSharedCheck_5998_ == 0)
{
v___x_5993_ = v___x_5898_;
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
else
{
lean_inc(v_a_5991_);
lean_dec(v___x_5898_);
v___x_5993_ = lean_box(0);
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
v_resetjp_5992_:
{
lean_object* v___x_5996_; 
if (v_isShared_5994_ == 0)
{
v___x_5996_ = v___x_5993_;
goto v_reusejp_5995_;
}
else
{
lean_object* v_reuseFailAlloc_5997_; 
v_reuseFailAlloc_5997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5997_, 0, v_a_5991_);
v___x_5996_ = v_reuseFailAlloc_5997_;
goto v_reusejp_5995_;
}
v_reusejp_5995_:
{
return v___x_5996_;
}
}
}
}
v___jp_5999_:
{
uint8_t v___x_6001_; 
v___x_6001_ = 1;
if (v_only_5854_ == 0)
{
v___y_5887_ = v___x_6001_;
v___y_5888_ = v___y_6000_;
v_params_5889_ = v_params_5852_;
v___y_5890_ = v_a_5856_;
v___y_5891_ = v_a_5857_;
v___y_5892_ = v_a_5858_;
v___y_5893_ = v_a_5859_;
v___y_5894_ = v_a_5860_;
v___y_5895_ = v_a_5861_;
v___y_5896_ = v_a_5862_;
v___y_5897_ = v_a_5863_;
goto v___jp_5886_;
}
else
{
lean_object* v_config_6002_; lean_object* v_extensions_6003_; lean_object* v_extra_6004_; lean_object* v_extraInj_6005_; lean_object* v_extraFacts_6006_; lean_object* v_symPrios_6007_; lean_object* v_norm_6008_; lean_object* v_normProcs_6009_; lean_object* v___x_6011_; uint8_t v_isShared_6012_; uint8_t v_isSharedCheck_6020_; 
v_config_6002_ = lean_ctor_get(v_params_5852_, 0);
v_extensions_6003_ = lean_ctor_get(v_params_5852_, 1);
v_extra_6004_ = lean_ctor_get(v_params_5852_, 2);
v_extraInj_6005_ = lean_ctor_get(v_params_5852_, 3);
v_extraFacts_6006_ = lean_ctor_get(v_params_5852_, 4);
v_symPrios_6007_ = lean_ctor_get(v_params_5852_, 5);
v_norm_6008_ = lean_ctor_get(v_params_5852_, 6);
v_normProcs_6009_ = lean_ctor_get(v_params_5852_, 7);
v_isSharedCheck_6020_ = !lean_is_exclusive(v_params_5852_);
if (v_isSharedCheck_6020_ == 0)
{
lean_object* v_unused_6021_; 
v_unused_6021_ = lean_ctor_get(v_params_5852_, 8);
lean_dec(v_unused_6021_);
v___x_6011_ = v_params_5852_;
v_isShared_6012_ = v_isSharedCheck_6020_;
goto v_resetjp_6010_;
}
else
{
lean_inc(v_normProcs_6009_);
lean_inc(v_norm_6008_);
lean_inc(v_symPrios_6007_);
lean_inc(v_extraFacts_6006_);
lean_inc(v_extraInj_6005_);
lean_inc(v_extra_6004_);
lean_inc(v_extensions_6003_);
lean_inc(v_config_6002_);
lean_dec(v_params_5852_);
v___x_6011_ = lean_box(0);
v_isShared_6012_ = v_isSharedCheck_6020_;
goto v_resetjp_6010_;
}
v_resetjp_6010_:
{
size_t v_sz_6013_; size_t v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v_params_6018_; 
v_sz_6013_ = lean_array_size(v_extensions_6003_);
v___x_6014_ = ((size_t)0ULL);
v___x_6015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_6013_, v___x_6014_, v_extensions_6003_);
v___x_6016_ = lean_box(0);
if (v_isShared_6012_ == 0)
{
lean_ctor_set(v___x_6011_, 8, v___x_6016_);
lean_ctor_set(v___x_6011_, 1, v___x_6015_);
v_params_6018_ = v___x_6011_;
goto v_reusejp_6017_;
}
else
{
lean_object* v_reuseFailAlloc_6019_; 
v_reuseFailAlloc_6019_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6019_, 0, v_config_6002_);
lean_ctor_set(v_reuseFailAlloc_6019_, 1, v___x_6015_);
lean_ctor_set(v_reuseFailAlloc_6019_, 2, v_extra_6004_);
lean_ctor_set(v_reuseFailAlloc_6019_, 3, v_extraInj_6005_);
lean_ctor_set(v_reuseFailAlloc_6019_, 4, v_extraFacts_6006_);
lean_ctor_set(v_reuseFailAlloc_6019_, 5, v_symPrios_6007_);
lean_ctor_set(v_reuseFailAlloc_6019_, 6, v_norm_6008_);
lean_ctor_set(v_reuseFailAlloc_6019_, 7, v_normProcs_6009_);
lean_ctor_set(v_reuseFailAlloc_6019_, 8, v___x_6016_);
v_params_6018_ = v_reuseFailAlloc_6019_;
goto v_reusejp_6017_;
}
v_reusejp_6017_:
{
v___y_5887_ = v___x_6001_;
v___y_5888_ = v___y_6000_;
v_params_5889_ = v_params_6018_;
v___y_5890_ = v_a_5856_;
v___y_5891_ = v_a_5857_;
v___y_5892_ = v_a_5858_;
v___y_5893_ = v_a_5859_;
v___y_5894_ = v_a_5860_;
v___y_5895_ = v_a_5861_;
v___y_5896_ = v_a_5862_;
v___y_5897_ = v_a_5863_;
goto v___jp_5886_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Grind_withParams___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_5852_ = stack[0].m_obj;
lean_object* v_ps_5853_ = stack[1].m_obj;
uint8_t v_only_5854_ = stack[2].m_num;
lean_object* v_k_5855_ = stack[3].m_obj;
lean_object* v_a_5856_ = stack[4].m_obj;
lean_object* v_a_5857_ = stack[5].m_obj;
lean_object* v_a_5858_ = stack[6].m_obj;
lean_object* v_a_5859_ = stack[7].m_obj;
lean_object* v_a_5860_ = stack[8].m_obj;
lean_object* v_a_5861_ = stack[9].m_obj;
lean_object* v_a_5862_ = stack[10].m_obj;
lean_object* v_a_5863_ = stack[11].m_obj;
lean_object* v_res_6027_;
v_res_6027_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5852_, v_ps_5853_, v_only_5854_, v_k_5855_, v_a_5856_, v_a_5857_, v_a_5858_, v_a_5859_, v_a_5860_, v_a_5861_, v_a_5862_, v_a_5863_);
stack->m_obj
 = v_res_6027_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_6028_, lean_object* v_ps_6029_, lean_object* v_only_6030_, lean_object* v_k_6031_, lean_object* v_a_6032_, lean_object* v_a_6033_, lean_object* v_a_6034_, lean_object* v_a_6035_, lean_object* v_a_6036_, lean_object* v_a_6037_, lean_object* v_a_6038_, lean_object* v_a_6039_, lean_object* v_a_6040_){
_start:
{
uint8_t v_only_boxed_6041_; lean_object* v_res_6042_; 
v_only_boxed_6041_ = lean_unbox(v_only_6030_);
v_res_6042_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_6028_, v_ps_6029_, v_only_boxed_6041_, v_k_6031_, v_a_6032_, v_a_6033_, v_a_6034_, v_a_6035_, v_a_6036_, v_a_6037_, v_a_6038_, v_a_6039_);
lean_dec(v_a_6039_);
lean_dec_ref(v_a_6038_);
lean_dec(v_a_6037_);
lean_dec_ref(v_a_6036_);
lean_dec(v_a_6035_);
lean_dec_ref(v_a_6034_);
lean_dec(v_a_6033_);
lean_dec_ref(v_a_6032_);
lean_dec_ref(v_ps_6029_);
return v_res_6042_;
}
}
lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_6043_, lean_object* v_params_6044_, lean_object* v_ps_6045_, uint8_t v_only_6046_, lean_object* v_k_6047_, lean_object* v_a_6048_, lean_object* v_a_6049_, lean_object* v_a_6050_, lean_object* v_a_6051_, lean_object* v_a_6052_, lean_object* v_a_6053_, lean_object* v_a_6054_, lean_object* v_a_6055_){
_start:
{
lean_object* v___x_6057_; 
v___x_6057_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_6044_, v_ps_6045_, v_only_6046_, v_k_6047_, v_a_6048_, v_a_6049_, v_a_6050_, v_a_6051_, v_a_6052_, v_a_6053_, v_a_6054_, v_a_6055_);
return v___x_6057_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Grind_withParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_6044_ = stack[1].m_obj;
lean_object* v_ps_6045_ = stack[2].m_obj;
uint8_t v_only_6046_ = stack[3].m_num;
lean_object* v_k_6047_ = stack[4].m_obj;
lean_object* v_a_6048_ = stack[5].m_obj;
lean_object* v_a_6049_ = stack[6].m_obj;
lean_object* v_a_6050_ = stack[7].m_obj;
lean_object* v_a_6051_ = stack[8].m_obj;
lean_object* v_a_6052_ = stack[9].m_obj;
lean_object* v_a_6053_ = stack[10].m_obj;
lean_object* v_a_6054_ = stack[11].m_obj;
lean_object* v_a_6055_ = stack[12].m_obj;
lean_object* v_res_6058_;
v_res_6058_ = l_Lean_Elab_Tactic_Grind_withParams(lean_box(0), v_params_6044_, v_ps_6045_, v_only_6046_, v_k_6047_, v_a_6048_, v_a_6049_, v_a_6050_, v_a_6051_, v_a_6052_, v_a_6053_, v_a_6054_, v_a_6055_);
stack->m_obj
 = v_res_6058_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_6059_, lean_object* v_params_6060_, lean_object* v_ps_6061_, lean_object* v_only_6062_, lean_object* v_k_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_, lean_object* v_a_6066_, lean_object* v_a_6067_, lean_object* v_a_6068_, lean_object* v_a_6069_, lean_object* v_a_6070_, lean_object* v_a_6071_, lean_object* v_a_6072_){
_start:
{
uint8_t v_only_boxed_6073_; lean_object* v_res_6074_; 
v_only_boxed_6073_ = lean_unbox(v_only_6062_);
v_res_6074_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_6059_, v_params_6060_, v_ps_6061_, v_only_boxed_6073_, v_k_6063_, v_a_6064_, v_a_6065_, v_a_6066_, v_a_6067_, v_a_6068_, v_a_6069_, v_a_6070_, v_a_6071_);
lean_dec(v_a_6071_);
lean_dec_ref(v_a_6070_);
lean_dec(v_a_6069_);
lean_dec_ref(v_a_6068_);
lean_dec(v_a_6067_);
lean_dec_ref(v_a_6066_);
lean_dec(v_a_6065_);
lean_dec_ref(v_a_6064_);
lean_dec_ref(v_ps_6061_);
return v_res_6074_;
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
