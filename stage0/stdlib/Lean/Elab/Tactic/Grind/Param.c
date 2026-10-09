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
lean_ctor_set(v___x_89_, 0, v___y_82_);
lean_ctor_set(v___x_89_, 1, v___y_88_);
lean_ctor_set(v___x_89_, 2, v___y_83_);
lean_ctor_set(v___x_89_, 3, v___y_87_);
lean_ctor_set(v___x_89_, 4, v___y_86_);
lean_ctor_set(v___x_89_, 5, v___y_85_);
lean_ctor_set(v___x_89_, 6, v___y_81_);
lean_ctor_set(v___x_89_, 7, v___y_84_);
lean_ctor_set(v___x_89_, 8, v___y_80_);
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
v___y_80_ = v_anchorRefs_x3f_99_;
v___y_81_ = v_norm_97_;
v___y_82_ = v_config_91_;
v___y_83_ = v_extra_93_;
v___y_84_ = v_normProcs_98_;
v___y_85_ = v_symPrios_96_;
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
v___y_80_ = v_anchorRefs_x3f_99_;
v___y_81_ = v_norm_97_;
v___y_82_ = v_config_91_;
v___y_83_ = v_extra_93_;
v___y_84_ = v_normProcs_98_;
v___y_85_ = v_symPrios_96_;
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
uint8_t v___x_1646__boxed_324_; size_t v_i_boxed_325_; size_t v_stop_boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v___x_1646__boxed_324_ = lean_unbox(v___x_320_);
v_i_boxed_325_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_stop_boxed_326_ = lean_unbox_usize(v_stop_323_);
lean_dec(v_stop_323_);
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_319_, v___x_1646__boxed_324_, v_as_321_, v_i_boxed_325_, v_stop_boxed_326_);
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
lean_dec_ref_known(v_a_360_, 1);
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
lean_dec_ref_known(v___x_394_, 1);
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
lean_dec_ref_known(v___x_414_, 1);
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
lean_object* v___x_567_; lean_object* v_env_568_; uint8_t v___x_569_; lean_object* v_env_570_; lean_object* v___x_571_; lean_object* v_toCold_572_; lean_object* v_mctx_573_; lean_object* v_lctx_574_; lean_object* v_options_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_567_ = lean_st_ref_get(v___y_565_);
v_env_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc_ref(v_env_568_);
lean_dec(v___x_567_);
v___x_569_ = 0;
v_env_570_ = l_Lean_Environment_setRecordingDeps(v_env_568_, v___x_569_);
v___x_571_ = lean_st_ref_get(v___y_563_);
v_toCold_572_ = lean_ctor_get(v___y_564_, 0);
v_mctx_573_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_mctx_573_);
lean_dec(v___x_571_);
v_lctx_574_ = lean_ctor_get(v___y_562_, 2);
v_options_575_ = lean_ctor_get(v_toCold_572_, 2);
lean_inc_ref(v_options_575_);
lean_inc_ref(v_lctx_574_);
v___x_576_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_576_, 0, v_env_570_);
lean_ctor_set(v___x_576_, 1, v_mctx_573_);
lean_ctor_set(v___x_576_, 2, v_lctx_574_);
lean_ctor_set(v___x_576_, 3, v_options_575_);
v___x_577_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_msgData_561_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_msgData_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msgData_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_585_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_586_, lean_object* v_opt_587_){
_start:
{
lean_object* v_name_588_; lean_object* v_defValue_589_; lean_object* v_map_590_; lean_object* v___x_591_; 
v_name_588_ = lean_ctor_get(v_opt_587_, 0);
v_defValue_589_ = lean_ctor_get(v_opt_587_, 1);
v_map_590_ = lean_ctor_get(v_opts_586_, 0);
v___x_591_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_590_, v_name_588_);
if (lean_obj_tag(v___x_591_) == 0)
{
uint8_t v___x_592_; 
v___x_592_ = lean_unbox(v_defValue_589_);
return v___x_592_;
}
else
{
lean_object* v_val_593_; 
v_val_593_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_val_593_);
lean_dec_ref_known(v___x_591_, 1);
if (lean_obj_tag(v_val_593_) == 1)
{
uint8_t v_v_594_; 
v_v_594_ = lean_ctor_get_uint8(v_val_593_, 0);
lean_dec_ref_known(v_val_593_, 0);
return v_v_594_;
}
else
{
uint8_t v___x_595_; 
lean_dec(v_val_593_);
v___x_595_ = lean_unbox(v_defValue_589_);
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_596_, lean_object* v_opt_597_){
_start:
{
uint8_t v_res_598_; lean_object* v_r_599_; 
v_res_598_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_opts_596_, v_opt_597_);
lean_dec_ref(v_opt_597_);
lean_dec_ref(v_opts_596_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_608_, uint8_t v___y_609_, lean_object* v_x_610_){
_start:
{
if (lean_obj_tag(v_x_610_) == 1)
{
lean_object* v_pre_611_; 
v_pre_611_ = lean_ctor_get(v_x_610_, 0);
switch(lean_obj_tag(v_pre_611_))
{
case 1:
{
lean_object* v_pre_612_; 
v_pre_612_ = lean_ctor_get(v_pre_611_, 0);
switch(lean_obj_tag(v_pre_612_))
{
case 0:
{
lean_object* v_str_613_; lean_object* v_str_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_str_613_ = lean_ctor_get(v_x_610_, 1);
v_str_614_ = lean_ctor_get(v_pre_611_, 1);
v___x_615_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_616_ = lean_string_dec_eq(v_str_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_618_ = lean_string_dec_eq(v_str_614_, v___x_617_);
if (v___x_618_ == 0)
{
return v___x_618_;
}
else
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_620_ = lean_string_dec_eq(v_str_613_, v___x_619_);
if (v___x_620_ == 0)
{
return v___x_620_;
}
else
{
return v_suppressElabErrors_608_;
}
}
}
else
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_622_ = lean_string_dec_eq(v_str_613_, v___x_621_);
if (v___x_622_ == 0)
{
return v___x_622_;
}
else
{
return v_suppressElabErrors_608_;
}
}
}
case 1:
{
lean_object* v_pre_623_; 
v_pre_623_ = lean_ctor_get(v_pre_612_, 0);
if (lean_obj_tag(v_pre_623_) == 0)
{
lean_object* v_str_624_; lean_object* v_str_625_; lean_object* v_str_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_str_624_ = lean_ctor_get(v_x_610_, 1);
v_str_625_ = lean_ctor_get(v_pre_611_, 1);
v_str_626_ = lean_ctor_get(v_pre_612_, 1);
v___x_627_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_628_ = lean_string_dec_eq(v_str_626_, v___x_627_);
if (v___x_628_ == 0)
{
return v___x_628_;
}
else
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_630_ = lean_string_dec_eq(v_str_625_, v___x_629_);
if (v___x_630_ == 0)
{
return v___x_630_;
}
else
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_632_ = lean_string_dec_eq(v_str_624_, v___x_631_);
if (v___x_632_ == 0)
{
return v___x_632_;
}
else
{
return v_suppressElabErrors_608_;
}
}
}
}
else
{
return v___y_609_;
}
}
default: 
{
return v___y_609_;
}
}
}
case 0:
{
lean_object* v_str_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_str_633_ = lean_ctor_get(v_x_610_, 1);
v___x_634_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_635_ = lean_string_dec_eq(v_str_633_, v___x_634_);
if (v___x_635_ == 0)
{
return v___x_635_;
}
else
{
return v_suppressElabErrors_608_;
}
}
default: 
{
return v___y_609_;
}
}
}
else
{
return v___y_609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_636_, lean_object* v___y_637_, lean_object* v_x_638_){
_start:
{
uint8_t v_suppressElabErrors_boxed_639_; uint8_t v___y_4547__boxed_640_; uint8_t v_res_641_; lean_object* v_r_642_; 
v_suppressElabErrors_boxed_639_ = lean_unbox(v_suppressElabErrors_636_);
v___y_4547__boxed_640_ = lean_unbox(v___y_637_);
v_res_641_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_639_, v___y_4547__boxed_640_, v_x_638_);
lean_dec(v_x_638_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* v_ref_644_, lean_object* v_msgData_645_, uint8_t v_severity_646_, uint8_t v_isSilent_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; uint8_t v___y_657_; lean_object* v___y_658_; uint8_t v___y_659_; lean_object* v___y_660_; lean_object* v_toCold_661_; lean_object* v___y_662_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; uint8_t v___y_694_; uint8_t v___y_695_; lean_object* v___y_696_; uint8_t v___y_697_; lean_object* v___y_698_; lean_object* v___y_718_; lean_object* v___y_719_; uint8_t v___y_720_; lean_object* v___y_721_; uint8_t v___y_722_; uint8_t v___y_723_; lean_object* v___y_724_; uint8_t v___y_728_; uint8_t v___y_729_; uint8_t v___y_730_; uint8_t v___x_741_; uint8_t v___y_743_; uint8_t v___y_744_; uint8_t v___y_745_; uint8_t v___y_747_; uint8_t v___x_755_; 
v___x_741_ = 2;
v___x_755_ = l_Lean_instBEqMessageSeverity_beq(v_severity_646_, v___x_741_);
if (v___x_755_ == 0)
{
v___y_747_ = v___x_755_;
goto v___jp_746_;
}
else
{
uint8_t v___x_756_; 
lean_inc_ref(v_msgData_645_);
v___x_756_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_645_);
v___y_747_ = v___x_756_;
goto v___jp_746_;
}
v___jp_653_:
{
lean_object* v_currNamespace_663_; lean_object* v_openDecls_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_env_669_; lean_object* v_nextMacroScope_670_; lean_object* v_ngen_671_; lean_object* v_auxDeclNGen_672_; lean_object* v_traceState_673_; lean_object* v_cache_674_; lean_object* v_recordedDeps_675_; lean_object* v_messages_676_; lean_object* v_infoState_677_; lean_object* v_snapshotTasks_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_689_; 
v_currNamespace_663_ = lean_ctor_get(v_toCold_661_, 4);
v_openDecls_664_ = lean_ctor_get(v_toCold_661_, 5);
lean_inc(v_openDecls_664_);
lean_inc(v_currNamespace_663_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_currNamespace_663_);
lean_ctor_set(v___x_665_, 1, v_openDecls_664_);
v___x_666_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v___y_655_);
lean_inc_ref(v___y_654_);
lean_inc_ref(v___y_660_);
v___x_667_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_667_, 0, v___y_660_);
lean_ctor_set(v___x_667_, 1, v___y_658_);
lean_ctor_set(v___x_667_, 2, v___y_656_);
lean_ctor_set(v___x_667_, 3, v___y_654_);
lean_ctor_set(v___x_667_, 4, v___x_666_);
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*5, v___y_657_);
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*5 + 1, v___y_659_);
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*5 + 2, v_isSilent_647_);
v___x_668_ = lean_st_ref_take(v___y_662_);
v_env_669_ = lean_ctor_get(v___x_668_, 0);
v_nextMacroScope_670_ = lean_ctor_get(v___x_668_, 1);
v_ngen_671_ = lean_ctor_get(v___x_668_, 2);
v_auxDeclNGen_672_ = lean_ctor_get(v___x_668_, 3);
v_traceState_673_ = lean_ctor_get(v___x_668_, 4);
v_cache_674_ = lean_ctor_get(v___x_668_, 5);
v_recordedDeps_675_ = lean_ctor_get(v___x_668_, 6);
v_messages_676_ = lean_ctor_get(v___x_668_, 7);
v_infoState_677_ = lean_ctor_get(v___x_668_, 8);
v_snapshotTasks_678_ = lean_ctor_get(v___x_668_, 9);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_689_ == 0)
{
v___x_680_ = v___x_668_;
v_isShared_681_ = v_isSharedCheck_689_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_snapshotTasks_678_);
lean_inc(v_infoState_677_);
lean_inc(v_messages_676_);
lean_inc(v_recordedDeps_675_);
lean_inc(v_cache_674_);
lean_inc(v_traceState_673_);
lean_inc(v_auxDeclNGen_672_);
lean_inc(v_ngen_671_);
lean_inc(v_nextMacroScope_670_);
lean_inc(v_env_669_);
lean_dec(v___x_668_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_689_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_682_ = lean_box(0);
v___x_683_ = l_Lean_MessageLog_add(v___x_667_, v_messages_676_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 7, v___x_683_);
v___x_685_ = v___x_680_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_env_669_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_nextMacroScope_670_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_ngen_671_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_auxDeclNGen_672_);
lean_ctor_set(v_reuseFailAlloc_688_, 4, v_traceState_673_);
lean_ctor_set(v_reuseFailAlloc_688_, 5, v_cache_674_);
lean_ctor_set(v_reuseFailAlloc_688_, 6, v_recordedDeps_675_);
lean_ctor_set(v_reuseFailAlloc_688_, 7, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_688_, 8, v_infoState_677_);
lean_ctor_set(v_reuseFailAlloc_688_, 9, v_snapshotTasks_678_);
v___x_685_ = v_reuseFailAlloc_688_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_st_ref_put(v___y_662_, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_682_);
return v___x_687_;
}
}
}
v___jp_690_:
{
lean_object* v_fileName_699_; lean_object* v_fileMap_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_716_; 
v_fileName_699_ = lean_ctor_get(v___y_693_, 0);
v_fileMap_700_ = lean_ctor_get(v___y_693_, 1);
v___x_701_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_645_);
v___x_702_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_701_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
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
lean_inc_ref_n(v_fileMap_700_, 2);
v___x_707_ = l_Lean_FileMap_toPosition(v_fileMap_700_, v___y_696_);
lean_dec(v___y_696_);
v___x_708_ = l_Lean_FileMap_toPosition(v_fileMap_700_, v___y_698_);
lean_dec(v___y_698_);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
v___x_710_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_694_ == 0)
{
lean_del_object(v___x_705_);
lean_dec_ref(v___y_692_);
v___y_654_ = v___x_710_;
v___y_655_ = v_a_703_;
v___y_656_ = v___x_709_;
v___y_657_ = v___y_695_;
v___y_658_ = v___x_707_;
v___y_659_ = v___y_697_;
v___y_660_ = v_fileName_699_;
v_toCold_661_ = v___y_691_;
v___y_662_ = v___y_651_;
goto v___jp_653_;
}
else
{
uint8_t v___x_711_; 
lean_inc(v_a_703_);
v___x_711_ = l_Lean_MessageData_hasTag(v___y_692_, v_a_703_);
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
v___y_654_ = v___x_710_;
v___y_655_ = v_a_703_;
v___y_656_ = v___x_709_;
v___y_657_ = v___y_695_;
v___y_658_ = v___x_707_;
v___y_659_ = v___y_697_;
v___y_660_ = v_fileName_699_;
v_toCold_661_ = v___y_691_;
v___y_662_ = v___y_651_;
goto v___jp_653_;
}
}
}
}
v___jp_717_:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Syntax_getTailPos_x3f(v___y_721_, v___y_722_);
lean_dec(v___y_721_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_inc(v___y_724_);
v___y_691_ = v___y_718_;
v___y_692_ = v___y_719_;
v___y_693_ = v___y_718_;
v___y_694_ = v___y_720_;
v___y_695_ = v___y_722_;
v___y_696_ = v___y_724_;
v___y_697_ = v___y_723_;
v___y_698_ = v___y_724_;
goto v___jp_690_;
}
else
{
lean_object* v_val_726_; 
v_val_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v___x_725_, 1);
v___y_691_ = v___y_718_;
v___y_692_ = v___y_719_;
v___y_693_ = v___y_718_;
v___y_694_ = v___y_720_;
v___y_695_ = v___y_722_;
v___y_696_ = v___y_724_;
v___y_697_ = v___y_723_;
v___y_698_ = v_val_726_;
goto v___jp_690_;
}
}
v___jp_727_:
{
lean_object* v_toCold_731_; lean_object* v_ref_732_; uint8_t v_suppressElabErrors_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___f_736_; lean_object* v_ref_737_; lean_object* v___x_738_; 
v_toCold_731_ = lean_ctor_get(v___y_650_, 0);
v_ref_732_ = lean_ctor_get(v___y_650_, 2);
v_suppressElabErrors_733_ = lean_ctor_get_uint8(v___y_650_, sizeof(void*)*3 + 2);
v___x_734_ = lean_box(v_suppressElabErrors_733_);
v___x_735_ = lean_box(v___y_728_);
v___f_736_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_736_, 0, v___x_734_);
lean_closure_set(v___f_736_, 1, v___x_735_);
v_ref_737_ = l_Lean_replaceRef(v_ref_644_, v_ref_732_);
v___x_738_ = l_Lean_Syntax_getPos_x3f(v_ref_737_, v___y_729_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v___x_739_; 
v___x_739_ = lean_unsigned_to_nat(0u);
v___y_718_ = v_toCold_731_;
v___y_719_ = v___f_736_;
v___y_720_ = v_suppressElabErrors_733_;
v___y_721_ = v_ref_737_;
v___y_722_ = v___y_729_;
v___y_723_ = v___y_730_;
v___y_724_ = v___x_739_;
goto v___jp_717_;
}
else
{
lean_object* v_val_740_; 
v_val_740_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v___x_738_, 1);
v___y_718_ = v_toCold_731_;
v___y_719_ = v___f_736_;
v___y_720_ = v_suppressElabErrors_733_;
v___y_721_ = v_ref_737_;
v___y_722_ = v___y_729_;
v___y_723_ = v___y_730_;
v___y_724_ = v_val_740_;
goto v___jp_717_;
}
}
v___jp_742_:
{
if (v___y_745_ == 0)
{
v___y_728_ = v___y_743_;
v___y_729_ = v___y_744_;
v___y_730_ = v_severity_646_;
goto v___jp_727_;
}
else
{
v___y_728_ = v___y_743_;
v___y_729_ = v___y_744_;
v___y_730_ = v___x_741_;
goto v___jp_727_;
}
}
v___jp_746_:
{
if (v___y_747_ == 0)
{
uint8_t v___x_748_; uint8_t v___x_749_; 
v___x_748_ = 1;
v___x_749_ = l_Lean_instBEqMessageSeverity_beq(v_severity_646_, v___x_748_);
if (v___x_749_ == 0)
{
v___y_743_ = v___y_747_;
v___y_744_ = v___y_747_;
v___y_745_ = v___x_749_;
goto v___jp_742_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_650_);
v___x_751_ = l_Lean_warningAsError;
v___x_752_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_750_, v___x_751_);
lean_dec_ref(v___x_750_);
v___y_743_ = v___y_747_;
v___y_744_ = v___y_747_;
v___y_745_ = v___x_752_;
goto v___jp_742_;
}
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v_msgData_645_);
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_757_, lean_object* v_msgData_758_, lean_object* v_severity_759_, lean_object* v_isSilent_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
uint8_t v_severity_boxed_766_; uint8_t v_isSilent_boxed_767_; lean_object* v_res_768_; 
v_severity_boxed_766_ = lean_unbox(v_severity_759_);
v_isSilent_boxed_767_ = lean_unbox(v_isSilent_760_);
v_res_768_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_757_, v_msgData_758_, v_severity_boxed_766_, v_isSilent_boxed_767_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v_ref_757_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object* v_msgData_769_, uint8_t v_severity_770_, uint8_t v_isSilent_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_ref_777_; lean_object* v___x_778_; 
v_ref_777_ = lean_ctor_get(v___y_774_, 2);
v___x_778_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_777_, v_msgData_769_, v_severity_770_, v_isSilent_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object* v_msgData_779_, lean_object* v_severity_780_, lean_object* v_isSilent_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
uint8_t v_severity_boxed_787_; uint8_t v_isSilent_boxed_788_; lean_object* v_res_789_; 
v_severity_boxed_787_ = lean_unbox(v_severity_780_);
v_isSilent_boxed_788_ = lean_unbox(v_isSilent_781_);
v_res_789_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_779_, v_severity_boxed_787_, v_isSilent_boxed_788_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object* v_msgData_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
uint8_t v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; 
v___x_796_ = 1;
v___x_797_ = 0;
v___x_798_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_790_, v___x_796_, v___x_797_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object* v_msgData_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v_msgData_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
return v_res_805_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0));
v___x_808_ = l_Lean_stringToMessageData(v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
if (lean_obj_tag(v_a_809_) == 0)
{
lean_object* v___x_811_; 
v___x_811_ = l_List_reverse___redArg(v_a_810_);
return v___x_811_;
}
else
{
lean_object* v_head_812_; lean_object* v_tail_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_826_; 
v_head_812_ = lean_ctor_get(v_a_809_, 0);
v_tail_813_ = lean_ctor_get(v_a_809_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v_a_809_);
if (v_isSharedCheck_826_ == 0)
{
v___x_815_ = v_a_809_;
v_isShared_816_ = v_isSharedCheck_826_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_tail_813_);
lean_inc(v_head_812_);
lean_dec(v_a_809_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_826_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint8_t v_minIndexable_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v_minIndexable_817_ = 0;
v___x_818_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_819_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_812_, v_minIndexable_817_);
lean_dec(v_head_812_);
v___x_820_ = l_Lean_stringToMessageData(v___x_819_);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_818_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 1, v_a_810_);
lean_ctor_set(v___x_815_, 0, v___x_821_);
v___x_823_ = v___x_815_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_a_810_);
v___x_823_ = v_reuseFailAlloc_825_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
v_a_809_ = v_tail_813_;
v_a_810_ = v___x_823_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
if (lean_obj_tag(v_a_827_) == 0)
{
lean_object* v___x_829_; 
v___x_829_ = l_List_reverse___redArg(v_a_828_);
return v___x_829_;
}
else
{
lean_object* v_head_830_; lean_object* v_tail_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_839_; 
v_head_830_ = lean_ctor_get(v_a_827_, 0);
v_tail_831_ = lean_ctor_get(v_a_827_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_a_827_);
if (v_isSharedCheck_839_ == 0)
{
v___x_833_ = v_a_827_;
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_tail_831_);
lean_inc(v_head_830_);
lean_dec(v_a_827_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v_a_828_);
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_head_830_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_a_828_);
v___x_836_ = v_reuseFailAlloc_838_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
v_a_827_ = v_tail_831_;
v_a_828_ = v___x_836_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0));
v___x_842_ = l_Lean_stringToMessageData(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2));
v___x_845_ = l_Lean_stringToMessageData(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4));
v___x_848_ = l_Lean_stringToMessageData(v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object* v_s_849_, lean_object* v_declName_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_kinds_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v_ks_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_inc(v_declName_850_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v_declName_850_);
v___x_882_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_849_, v___x_881_);
lean_dec_ref_known(v___x_881_, 1);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec(v_declName_850_);
v___x_883_ = lean_box(0);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
return v___x_884_;
}
else
{
lean_object* v_head_885_; lean_object* v_tail_886_; uint8_t v_minIndexable_887_; uint8_t v_gen_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; 
v_head_885_ = lean_ctor_get(v___x_882_, 0);
v_tail_886_ = lean_ctor_get(v___x_882_, 1);
v_minIndexable_887_ = 0;
if (lean_obj_tag(v_tail_886_) == 0)
{
lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_908_; 
lean_inc(v_head_885_);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; lean_object* v_unused_910_; 
v_unused_909_ = lean_ctor_get(v___x_882_, 1);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v___x_882_, 0);
lean_dec(v_unused_910_);
v___x_900_ = v___x_882_;
v_isShared_901_ = v_isSharedCheck_908_;
goto v_resetjp_899_;
}
else
{
lean_dec(v___x_882_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_908_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_902_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_903_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_885_, v_minIndexable_887_);
lean_dec(v_head_885_);
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 7);
lean_ctor_set(v___x_900_, 1, v___x_904_);
lean_ctor_set(v___x_900_, 0, v___x_902_);
v___x_906_ = v___x_900_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
v_kinds_857_ = v___x_906_;
v___y_858_ = v_a_851_;
v___y_859_ = v_a_852_;
v___y_860_ = v_a_853_;
v___y_861_ = v_a_854_;
goto v___jp_856_;
}
}
}
else
{
lean_object* v_head_911_; 
v_head_911_ = lean_ctor_get(v_tail_886_, 0);
switch(lean_obj_tag(v_head_911_))
{
case 1:
{
lean_object* v_tail_912_; 
v_tail_912_ = lean_ctor_get(v_tail_886_, 1);
if (lean_obj_tag(v_tail_912_) == 0)
{
if (lean_obj_tag(v_head_885_) == 0)
{
uint8_t v_gen_913_; 
lean_inc_ref(v_head_885_);
lean_dec_ref_known(v___x_882_, 2);
v_gen_913_ = lean_ctor_get_uint8(v_head_885_, 0);
lean_dec_ref_known(v_head_885_, 0);
v_gen_889_ = v_gen_913_;
v___y_890_ = v_a_851_;
v___y_891_ = v_a_852_;
v___y_892_ = v_a_853_;
v___y_893_ = v_a_854_;
goto v___jp_888_;
}
else
{
v_ks_872_ = v___x_882_;
v___y_873_ = v_a_851_;
v___y_874_ = v_a_852_;
v___y_875_ = v_a_853_;
v___y_876_ = v_a_854_;
goto v___jp_871_;
}
}
else
{
v_ks_872_ = v___x_882_;
v___y_873_ = v_a_851_;
v___y_874_ = v_a_852_;
v___y_875_ = v_a_853_;
v___y_876_ = v_a_854_;
goto v___jp_871_;
}
}
case 0:
{
lean_object* v_tail_914_; 
v_tail_914_ = lean_ctor_get(v_tail_886_, 1);
if (lean_obj_tag(v_tail_914_) == 0)
{
if (lean_obj_tag(v_head_885_) == 1)
{
uint8_t v_gen_915_; 
lean_inc_ref(v_head_885_);
lean_dec_ref_known(v___x_882_, 2);
v_gen_915_ = lean_ctor_get_uint8(v_head_885_, 0);
lean_dec_ref_known(v_head_885_, 0);
v_gen_889_ = v_gen_915_;
v___y_890_ = v_a_851_;
v___y_891_ = v_a_852_;
v___y_892_ = v_a_853_;
v___y_893_ = v_a_854_;
goto v___jp_888_;
}
else
{
v_ks_872_ = v___x_882_;
v___y_873_ = v_a_851_;
v___y_874_ = v_a_852_;
v___y_875_ = v_a_853_;
v___y_876_ = v_a_854_;
goto v___jp_871_;
}
}
else
{
v_ks_872_ = v___x_882_;
v___y_873_ = v_a_851_;
v___y_874_ = v_a_852_;
v___y_875_ = v_a_853_;
v___y_876_ = v_a_854_;
goto v___jp_871_;
}
}
default: 
{
v_ks_872_ = v___x_882_;
v___y_873_ = v_a_851_;
v___y_874_ = v_a_852_;
v___y_875_ = v_a_853_;
v___y_876_ = v_a_854_;
goto v___jp_871_;
}
}
}
v___jp_888_:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_894_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_895_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_895_, 0, v_gen_889_);
v___x_896_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v___x_895_, v_minIndexable_887_);
lean_dec_ref_known(v___x_895_, 0);
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_894_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v_kinds_857_ = v___x_898_;
v___y_858_ = v___y_890_;
v___y_859_ = v___y_891_;
v___y_860_ = v___y_892_;
v___y_861_ = v___y_893_;
goto v___jp_856_;
}
}
v___jp_856_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_862_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1);
v___x_863_ = l_Lean_MessageData_ofName(v_declName_850_);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v_kinds_857_);
v___x_868_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v___x_869_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_870_;
}
v___jp_871_:
{
lean_object* v___x_877_; lean_object* v_ks_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_877_ = lean_box(0);
v_ks_878_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(v_ks_872_, v___x_877_);
v___x_879_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(v_ks_878_, v___x_877_);
v___x_880_ = l_Lean_MessageData_ofList(v___x_879_);
v_kinds_857_ = v___x_880_;
v___y_858_ = v___y_873_;
v___y_859_ = v___y_874_;
v___y_860_ = v___y_875_;
v___y_861_ = v___y_876_;
goto v___jp_856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object* v_s_916_, lean_object* v_declName_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_s_916_, v_declName_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec_ref(v_s_916_);
return v_res_923_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_924_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_927_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_928_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_929_ = lean_unsigned_to_nat(0u);
v___x_930_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
lean_ctor_set(v___x_930_, 2, v___x_929_);
lean_ctor_set(v___x_930_, 3, v___x_929_);
lean_ctor_set(v___x_930_, 4, v___x_928_);
lean_ctor_set(v___x_930_, 5, v___x_928_);
lean_ctor_set(v___x_930_, 6, v___x_928_);
lean_ctor_set(v___x_930_, 7, v___x_928_);
lean_ctor_set(v___x_930_, 8, v___x_928_);
lean_ctor_set(v___x_930_, 9, v___x_928_);
lean_ctor_set(v___x_930_, 10, v___x_928_);
lean_ctor_set(v___x_930_, 11, v___x_927_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_unsigned_to_nat(32u);
v___x_932_ = lean_mk_empty_array_with_capacity(v___x_931_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_934_ = ((size_t)5ULL);
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = lean_unsigned_to_nat(32u);
v___x_937_ = lean_mk_empty_array_with_capacity(v___x_936_);
v___x_938_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3);
v___x_939_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_937_);
lean_ctor_set(v___x_939_, 2, v___x_935_);
lean_ctor_set(v___x_939_, 3, v___x_935_);
lean_ctor_set_usize(v___x_939_, 4, v___x_934_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_940_ = lean_box(1);
v___x_941_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4);
v___x_942_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
lean_ctor_set(v___x_943_, 2, v___x_940_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object* v_msgData_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; lean_object* v_toCold_949_; lean_object* v_env_950_; lean_object* v_options_951_; uint8_t v___x_952_; lean_object* v_env_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_948_ = lean_st_ref_get(v___y_946_);
v_toCold_949_ = lean_ctor_get(v___y_945_, 0);
v_env_950_ = lean_ctor_get(v___x_948_, 0);
lean_inc_ref(v_env_950_);
lean_dec(v___x_948_);
v_options_951_ = lean_ctor_get(v_toCold_949_, 2);
v___x_952_ = 0;
v_env_953_ = l_Lean_Environment_setRecordingDeps(v_env_950_, v___x_952_);
v___x_954_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_955_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_951_);
v___x_956_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_956_, 0, v_env_953_);
lean_ctor_set(v___x_956_, 1, v___x_954_);
lean_ctor_set(v___x_956_, 2, v___x_955_);
lean_ctor_set(v___x_956_, 3, v_options_951_);
v___x_957_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v_msgData_944_);
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
v_ref_968_ = lean_ctor_get(v___y_965_, 2);
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
lean_dec_ref_known(v___x_1005_, 1);
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
v_ref_1035_ = lean_ctor_get(v___y_1032_, 2);
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18));
v___x_1119_ = l_Lean_stringToMessageData(v___x_1118_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__20));
v___x_1122_ = l_Lean_stringToMessageData(v___x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1123_, lean_object* v_declHint_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_env_1129_; uint8_t v___x_1130_; 
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_st_ref_get(v___y_1125_);
v_env_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc_ref(v_env_1129_);
lean_dec(v___x_1128_);
v___x_1130_ = l_Lean_Name_isAnonymous(v_declHint_1124_);
if (v___x_1130_ == 0)
{
uint8_t v_isExporting_1131_; 
v_isExporting_1131_ = lean_ctor_get_uint8(v_env_1129_, sizeof(void*)*13);
if (v_isExporting_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref(v_env_1129_);
lean_dec(v_declHint_1124_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_msg_1123_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
lean_inc_ref(v_env_1129_);
v___x_1133_ = l_Lean_Environment_setExporting(v_env_1129_, v___x_1130_);
lean_inc(v_declHint_1124_);
lean_inc_ref(v___x_1133_);
v___x_1134_ = l_Lean_Environment_contains(v___x_1133_, v_declHint_1124_, v_isExporting_1131_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec_ref(v___x_1133_);
lean_dec_ref(v_env_1129_);
lean_dec(v_declHint_1124_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_msg_1123_);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v_c_1141_; lean_object* v___x_1142_; 
v___x_1136_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_1137_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
v___x_1138_ = l_Lean_Options_empty;
v___x_1139_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1133_);
lean_ctor_set(v___x_1139_, 1, v___x_1136_);
lean_ctor_set(v___x_1139_, 2, v___x_1137_);
lean_ctor_set(v___x_1139_, 3, v___x_1138_);
lean_inc(v_declHint_1124_);
v___x_1140_ = l_Lean_MessageData_ofConstName(v_declHint_1124_, v___x_1130_);
v_c_1141_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1141_, 0, v___x_1139_);
lean_ctor_set(v_c_1141_, 1, v___x_1140_);
v___x_1142_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1129_, v_declHint_1124_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec_ref(v_env_1129_);
lean_dec(v_declHint_1124_);
v___x_1143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
lean_ctor_set(v___x_1144_, 1, v_c_1141_);
v___x_1145_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = l_Lean_MessageData_note(v___x_1146_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v_msg_1123_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
else
{
lean_object* v_val_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1206_; 
v_val_1150_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1152_ = v___x_1142_;
v_isShared_1153_ = v_isSharedCheck_1206_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_val_1150_);
lean_dec(v___x_1142_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1206_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v_modules_1155_; lean_object* v_moduleNames_1156_; lean_object* v_mod_1157_; uint8_t v___y_1159_; uint8_t v___x_1189_; 
v___x_1154_ = l_Lean_Environment_header(v_env_1129_);
lean_dec_ref(v_env_1129_);
v_modules_1155_ = lean_ctor_get(v___x_1154_, 3);
lean_inc_ref(v_modules_1155_);
v_moduleNames_1156_ = lean_ctor_get(v___x_1154_, 4);
lean_inc_ref(v_moduleNames_1156_);
lean_dec_ref(v___x_1154_);
v_mod_1157_ = lean_array_get(v___x_1127_, v_moduleNames_1156_, v_val_1150_);
lean_dec_ref(v_moduleNames_1156_);
v___x_1189_ = l_Lean_isPrivateName(v_declHint_1124_);
lean_dec(v_declHint_1124_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = lean_array_get_size(v_modules_1155_);
v___x_1191_ = lean_nat_dec_lt(v_val_1150_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_dec_ref(v_modules_1155_);
lean_dec(v_val_1150_);
v___y_1159_ = v___x_1189_;
goto v___jp_1158_;
}
else
{
lean_object* v___x_1192_; lean_object* v_toImport_1193_; uint8_t v_isExported_1194_; 
v___x_1192_ = lean_array_fget(v_modules_1155_, v_val_1150_);
lean_dec(v_val_1150_);
lean_dec_ref(v_modules_1155_);
v_toImport_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_ref(v_toImport_1193_);
lean_dec(v___x_1192_);
v_isExported_1194_ = lean_ctor_get_uint8(v_toImport_1193_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1193_);
v___y_1159_ = v_isExported_1194_;
goto v___jp_1158_;
}
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec_ref(v_modules_1155_);
lean_del_object(v___x_1152_);
lean_dec(v_val_1150_);
v___x_1195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v_c_1141_);
v___x_1197_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
v___x_1198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = l_Lean_MessageData_ofName(v_mod_1157_);
v___x_1200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__21);
v___x_1202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = l_Lean_MessageData_note(v___x_1202_);
v___x_1204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1204_, 0, v_msg_1123_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
v___jp_1158_:
{
if (v___y_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v_c_1141_);
v___x_1162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_MessageData_ofName(v_mod_1157_);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = l_Lean_MessageData_note(v___x_1167_);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_msg_1123_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1169_);
v___x_1171_ = v___x_1152_;
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
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1173_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v_c_1141_);
v___x_1175_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = l_Lean_MessageData_ofName(v_mod_1157_);
lean_inc_ref(v___x_1177_);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v___x_1177_);
v___x_1182_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = l_Lean_MessageData_note(v___x_1183_);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v_msg_1123_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1185_);
v___x_1187_ = v___x_1152_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
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
lean_object* v___x_1207_; 
lean_dec_ref(v_env_1129_);
lean_dec(v_declHint_1124_);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v_msg_1123_);
return v___x_1207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1208_, lean_object* v_declHint_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1208_, v_declHint_1209_, v___y_1210_);
lean_dec(v___y_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1213_, lean_object* v_declHint_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1230_; 
v___x_1220_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1213_, v_declHint_1214_, v___y_1218_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1230_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1230_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1225_ = l_Lean_unknownIdentifierMessageTag;
v___x_1226_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_a_1221_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1226_);
v___x_1228_ = v___x_1223_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1231_, lean_object* v_declHint_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1231_, v_declHint_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1239_, lean_object* v_msg_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_toCold_1246_; lean_object* v_currRecDepth_1247_; lean_object* v_ref_1248_; uint16_t v_optionFlags_1249_; uint8_t v_suppressElabErrors_1250_; uint8_t v_isRecordingDeps_1251_; lean_object* v_ref_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_toCold_1246_ = lean_ctor_get(v___y_1243_, 0);
v_currRecDepth_1247_ = lean_ctor_get(v___y_1243_, 1);
v_ref_1248_ = lean_ctor_get(v___y_1243_, 2);
v_optionFlags_1249_ = lean_ctor_get_uint16(v___y_1243_, sizeof(void*)*3);
v_suppressElabErrors_1250_ = lean_ctor_get_uint8(v___y_1243_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1251_ = lean_ctor_get_uint8(v___y_1243_, sizeof(void*)*3 + 3);
v_ref_1252_ = l_Lean_replaceRef(v_ref_1239_, v_ref_1248_);
lean_inc(v_currRecDepth_1247_);
lean_inc_ref(v_toCold_1246_);
v___x_1253_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1253_, 0, v_toCold_1246_);
lean_ctor_set(v___x_1253_, 1, v_currRecDepth_1247_);
lean_ctor_set(v___x_1253_, 2, v_ref_1252_);
lean_ctor_set_uint16(v___x_1253_, sizeof(void*)*3, v_optionFlags_1249_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*3 + 2, v_suppressElabErrors_1250_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*3 + 3, v_isRecordingDeps_1251_);
v___x_1254_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1240_, v___y_1241_, v___y_1242_, v___x_1253_, v___y_1244_);
lean_dec_ref_known(v___x_1253_, 3);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1255_, lean_object* v_msg_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1255_, v_msg_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v_ref_1255_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1263_, lean_object* v_msg_1264_, lean_object* v_declHint_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; lean_object* v_a_1272_; lean_object* v___x_1273_; 
v___x_1271_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1264_, v_declHint_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1263_, v_a_1272_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1274_, lean_object* v_msg_1275_, lean_object* v_declHint_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1274_, v_msg_1275_, v_declHint_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v_ref_1274_);
return v_res_1282_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1286_, lean_object* v_constName_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1293_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1294_ = 0;
lean_inc(v_constName_1287_);
v___x_1295_ = l_Lean_MessageData_ofConstName(v_constName_1287_, v___x_1294_);
v___x_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1293_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1286_, v___x_1298_, v_constName_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1300_, lean_object* v_constName_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1300_, v_constName_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v_ref_1300_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_constName_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_ref_1314_; lean_object* v___x_1315_; 
v_ref_1314_ = lean_ctor_get(v___y_1311_, 2);
v___x_1315_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1314_, v_constName_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* v_constName_1323_, uint8_t v_skipRealize_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; lean_object* v_env_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_st_ref_get(v___y_1328_);
v_env_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc_ref(v_env_1331_);
lean_dec(v___x_1330_);
lean_inc(v_constName_1323_);
v___x_1332_ = l_Lean_Environment_findAsync_x3f(v_env_1331_, v_constName_1323_, v_skipRealize_1324_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1323_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
return v___x_1333_;
}
else
{
lean_object* v_val_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_constName_1323_);
v_val_1334_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1332_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_val_1334_);
lean_dec(v___x_1332_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 0);
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_val_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* v_constName_1342_, lean_object* v_skipRealize_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v_skipRealize_boxed_1349_; lean_object* v_res_1350_; 
v_skipRealize_boxed_1349_ = lean_unbox(v_skipRealize_1343_);
v_res_1350_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1342_, v_skipRealize_boxed_1349_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* v_declName_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; lean_object* v_env_1355_; uint8_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1354_ = lean_st_ref_get(v___y_1352_);
v_env_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc_ref(v_env_1355_);
lean_dec(v___x_1354_);
v___x_1356_ = l_Lean_getReducibilityStatusCore(v_env_1355_, v_declName_1351_);
v___x_1357_ = lean_box(v___x_1356_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_declName_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1359_, v___y_1360_);
lean_dec(v___y_1360_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* v_declName_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1385_; 
v___x_1369_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1363_, v___y_1367_);
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1385_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1385_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
uint8_t v___x_1374_; 
v___x_1374_ = lean_unbox(v_a_1370_);
lean_dec(v_a_1370_);
if (v___x_1374_ == 0)
{
uint8_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1375_ = 1;
v___x_1376_ = lean_box(v___x_1375_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1376_);
v___x_1378_ = v___x_1372_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
else
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1380_ = 0;
v___x_1381_ = lean_box(v___x_1380_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1381_);
v___x_1383_ = v___x_1372_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* v_declName_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
return v_res_1392_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
v___x_1395_ = l_Lean_stringToMessageData(v___x_1394_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
v___x_1398_ = l_Lean_stringToMessageData(v___x_1397_);
return v___x_1398_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
v___x_1401_ = l_Lean_stringToMessageData(v___x_1400_);
return v___x_1401_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
v___x_1404_ = l_Lean_stringToMessageData(v___x_1403_);
return v___x_1404_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
v___x_1407_ = l_Lean_stringToMessageData(v___x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* v_params_1408_, lean_object* v_id_1409_, lean_object* v_declName_1410_, lean_object* v_kind_1411_, uint8_t v_minIndexable_1412_, uint8_t v_suggest_1413_, uint8_t v_warn_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v___y_1421_; lean_object* v_thm_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; uint8_t v___x_1476_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___x_1673_; 
v___x_1476_ = 0;
lean_inc(v_declName_1410_);
v___x_1673_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1410_, v___x_1476_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; uint8_t v_kind_1675_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v_kind_1675_ = lean_ctor_get_uint8(v_a_1674_, sizeof(void*)*3);
lean_dec(v_a_1674_);
switch(v_kind_1675_)
{
case 1:
{
v___y_1604_ = v_a_1415_;
v___y_1605_ = v_a_1416_;
v___y_1606_ = v_a_1417_;
v___y_1607_ = v_a_1418_;
goto v___jp_1603_;
}
case 2:
{
v___y_1604_ = v_a_1415_;
v___y_1605_ = v_a_1416_;
v___y_1606_ = v_a_1417_;
v___y_1607_ = v_a_1418_;
goto v___jp_1603_;
}
case 6:
{
v___y_1604_ = v_a_1415_;
v___y_1605_ = v_a_1416_;
v___y_1606_ = v_a_1417_;
v___y_1607_ = v_a_1418_;
goto v___jp_1603_;
}
case 0:
{
lean_object* v___x_1676_; 
lean_dec(v_id_1409_);
lean_inc(v_declName_1410_);
v___x_1676_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1410_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; uint8_t v___x_1678_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v___x_1678_ = lean_unbox(v_a_1677_);
lean_dec(v_a_1677_);
if (v___x_1678_ == 0)
{
v___y_1534_ = v_a_1415_;
v___y_1535_ = v_a_1416_;
v___y_1536_ = v_a_1417_;
v___y_1537_ = v_a_1418_;
goto v___jp_1533_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_kind_1411_);
lean_dec_ref(v_params_1408_);
v___x_1679_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1680_ = l_Lean_MessageData_ofConstName(v_declName_1410_, v___x_1476_);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1683_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec(v_kind_1411_);
lean_dec(v_declName_1410_);
lean_dec_ref(v_params_1408_);
v_a_1693_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1676_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1676_);
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
default: 
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec(v_kind_1411_);
lean_dec(v_id_1409_);
lean_dec_ref(v_params_1408_);
v___x_1701_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1702_ = l_Lean_MessageData_ofConstName(v_declName_1410_, v___x_1476_);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1705_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
return v___x_1706_;
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v_kind_1411_);
lean_dec(v_declName_1410_);
lean_dec(v_id_1409_);
lean_dec_ref(v_params_1408_);
v_a_1707_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1673_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1673_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
v___jp_1420_:
{
lean_object* v_config_1422_; lean_object* v_extensions_1423_; lean_object* v_extra_1424_; lean_object* v_extraInj_1425_; lean_object* v_extraFacts_1426_; lean_object* v_symPrios_1427_; lean_object* v_norm_1428_; lean_object* v_normProcs_1429_; lean_object* v_anchorRefs_x3f_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1439_; 
v_config_1422_ = lean_ctor_get(v_params_1408_, 0);
v_extensions_1423_ = lean_ctor_get(v_params_1408_, 1);
v_extra_1424_ = lean_ctor_get(v_params_1408_, 2);
v_extraInj_1425_ = lean_ctor_get(v_params_1408_, 3);
v_extraFacts_1426_ = lean_ctor_get(v_params_1408_, 4);
v_symPrios_1427_ = lean_ctor_get(v_params_1408_, 5);
v_norm_1428_ = lean_ctor_get(v_params_1408_, 6);
v_normProcs_1429_ = lean_ctor_get(v_params_1408_, 7);
v_anchorRefs_x3f_1430_ = lean_ctor_get(v_params_1408_, 8);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_params_1408_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1432_ = v_params_1408_;
v_isShared_1433_ = v_isSharedCheck_1439_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_anchorRefs_x3f_1430_);
lean_inc(v_normProcs_1429_);
lean_inc(v_norm_1428_);
lean_inc(v_symPrios_1427_);
lean_inc(v_extraFacts_1426_);
lean_inc(v_extraInj_1425_);
lean_inc(v_extra_1424_);
lean_inc(v_extensions_1423_);
lean_inc(v_config_1422_);
lean_dec(v_params_1408_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1439_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = l_Lean_PersistentArray_push___redArg(v_extra_1424_, v___y_1421_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 2, v___x_1434_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_config_1422_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_extensions_1423_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1438_, 3, v_extraInj_1425_);
lean_ctor_set(v_reuseFailAlloc_1438_, 4, v_extraFacts_1426_);
lean_ctor_set(v_reuseFailAlloc_1438_, 5, v_symPrios_1427_);
lean_ctor_set(v_reuseFailAlloc_1438_, 6, v_norm_1428_);
lean_ctor_set(v_reuseFailAlloc_1438_, 7, v_normProcs_1429_);
lean_ctor_set(v_reuseFailAlloc_1438_, 8, v_anchorRefs_x3f_1430_);
v___x_1436_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
return v___x_1437_;
}
}
}
v___jp_1440_:
{
if (v_warn_1414_ == 0)
{
lean_dec(v_declName_1410_);
v___y_1421_ = v_thm_1441_;
goto v___jp_1420_;
}
else
{
lean_object* v_extensions_1446_; lean_object* v_patterns_1447_; lean_object* v_origin_1448_; lean_object* v_cnstrs_1449_; uint8_t v___x_1450_; 
v_extensions_1446_ = lean_ctor_get(v_params_1408_, 1);
v_patterns_1447_ = lean_ctor_get(v_thm_1441_, 3);
v_origin_1448_ = lean_ctor_get(v_thm_1441_, 5);
v_cnstrs_1449_ = lean_ctor_get(v_thm_1441_, 7);
v___x_1450_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1446_, v_origin_1448_, v_patterns_1447_, v_cnstrs_1449_);
if (v___x_1450_ == 0)
{
lean_dec(v_declName_1410_);
v___y_1421_ = v_thm_1441_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1446_, v_declName_1410_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_dec_ref_known(v___x_1451_, 1);
v___y_1421_ = v_thm_1441_;
goto v___jp_1420_;
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec_ref(v_thm_1441_);
lean_dec_ref(v_params_1408_);
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
}
v___jp_1460_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1472_ = l_Lean_PersistentArray_push___redArg(v___y_1470_, v___y_1467_);
v___x_1473_ = l_Lean_PersistentArray_push___redArg(v___x_1472_, v___y_1465_);
v___x_1474_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1474_, 0, v___y_1461_);
lean_ctor_set(v___x_1474_, 1, v___y_1469_);
lean_ctor_set(v___x_1474_, 2, v___x_1473_);
lean_ctor_set(v___x_1474_, 3, v___y_1466_);
lean_ctor_set(v___x_1474_, 4, v___y_1463_);
lean_ctor_set(v___x_1474_, 5, v___y_1464_);
lean_ctor_set(v___x_1474_, 6, v___y_1471_);
lean_ctor_set(v___x_1474_, 7, v___y_1462_);
lean_ctor_set(v___x_1474_, 8, v___y_1468_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
return v___x_1475_;
}
v___jp_1477_:
{
lean_object* v___x_1482_; 
v___x_1482_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1412_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v___x_1483_; 
lean_dec_ref_known(v___x_1482_, 1);
lean_inc(v_declName_1410_);
v___x_1483_ = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(v_declName_1410_, v___x_1476_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1516_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1516_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1516_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
if (lean_obj_tag(v_a_1484_) == 1)
{
lean_object* v_val_1488_; lean_object* v_config_1489_; lean_object* v_extensions_1490_; lean_object* v_extra_1491_; lean_object* v_extraInj_1492_; lean_object* v_extraFacts_1493_; lean_object* v_symPrios_1494_; lean_object* v_norm_1495_; lean_object* v_normProcs_1496_; lean_object* v_anchorRefs_x3f_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_declName_1410_);
v_val_1488_ = lean_ctor_get(v_a_1484_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v_a_1484_, 1);
v_config_1489_ = lean_ctor_get(v_params_1408_, 0);
v_extensions_1490_ = lean_ctor_get(v_params_1408_, 1);
v_extra_1491_ = lean_ctor_get(v_params_1408_, 2);
v_extraInj_1492_ = lean_ctor_get(v_params_1408_, 3);
v_extraFacts_1493_ = lean_ctor_get(v_params_1408_, 4);
v_symPrios_1494_ = lean_ctor_get(v_params_1408_, 5);
v_norm_1495_ = lean_ctor_get(v_params_1408_, 6);
v_normProcs_1496_ = lean_ctor_get(v_params_1408_, 7);
v_anchorRefs_x3f_1497_ = lean_ctor_get(v_params_1408_, 8);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_params_1408_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1499_ = v_params_1408_;
v_isShared_1500_ = v_isSharedCheck_1509_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_anchorRefs_x3f_1497_);
lean_inc(v_normProcs_1496_);
lean_inc(v_norm_1495_);
lean_inc(v_symPrios_1494_);
lean_inc(v_extraFacts_1493_);
lean_inc(v_extraInj_1492_);
lean_inc(v_extra_1491_);
lean_inc(v_extensions_1490_);
lean_inc(v_config_1489_);
lean_dec(v_params_1408_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1509_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1501_ = l_Lean_Array_toPArray_x27___redArg(v_val_1488_);
lean_dec(v_val_1488_);
v___x_1502_ = l_Lean_PersistentArray_append___redArg(v_extra_1491_, v___x_1501_);
lean_dec_ref(v___x_1501_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 2, v___x_1502_);
v___x_1504_ = v___x_1499_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_config_1489_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_extensions_1490_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_extraInj_1492_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_extraFacts_1493_);
lean_ctor_set(v_reuseFailAlloc_1508_, 5, v_symPrios_1494_);
lean_ctor_set(v_reuseFailAlloc_1508_, 6, v_norm_1495_);
lean_ctor_set(v_reuseFailAlloc_1508_, 7, v_normProcs_1496_);
lean_ctor_set(v_reuseFailAlloc_1508_, 8, v_anchorRefs_x3f_1497_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1504_);
v___x_1506_ = v___x_1486_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
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
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_del_object(v___x_1486_);
lean_dec(v_a_1484_);
lean_dec_ref(v_params_1408_);
v___x_1510_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__1, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
v___x_1511_ = l_Lean_MessageData_ofConstName(v_declName_1410_, v___x_1476_);
v___x_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1514_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
return v___x_1515_;
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec(v_declName_1410_);
lean_dec_ref(v_params_1408_);
v_a_1517_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1483_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1483_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_declName_1410_);
lean_dec_ref(v_params_1408_);
v_a_1525_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1482_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1482_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
v___jp_1533_:
{
uint8_t v___x_1538_; 
v___x_1538_ = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(v_kind_1411_);
if (v___x_1538_ == 0)
{
uint8_t v___x_1539_; 
v___x_1539_ = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(v_kind_1411_);
lean_dec(v_kind_1411_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec_ref(v_params_1408_);
v___x_1540_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1541_ = l_Lean_MessageData_ofConstName(v_declName_1410_, v___x_1476_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__5, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1544_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
else
{
v___y_1478_ = v___y_1534_;
v___y_1479_ = v___y_1535_;
v___y_1480_ = v___y_1536_;
v___y_1481_ = v___y_1537_;
goto v___jp_1477_;
}
}
else
{
lean_dec(v_kind_1411_);
v___y_1478_ = v___y_1534_;
v___y_1479_ = v___y_1535_;
v___y_1480_ = v___y_1536_;
v___y_1481_ = v___y_1537_;
goto v___jp_1477_;
}
}
v___jp_1554_:
{
lean_object* v_symPrios_1559_; lean_object* v___x_1560_; 
v_symPrios_1559_ = lean_ctor_get(v_params_1408_, 5);
lean_inc_ref(v_symPrios_1559_);
lean_inc(v_declName_1410_);
v___x_1560_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1410_, v_kind_1411_, v_symPrios_1559_, v___x_1476_, v_minIndexable_1412_, v___y_1557_, v___y_1558_, v___y_1556_, v___y_1555_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v_thm_1441_ = v_a_1561_;
v___y_1442_ = v___y_1557_;
v___y_1443_ = v___y_1558_;
v___y_1444_ = v___y_1556_;
v___y_1445_ = v___y_1555_;
goto v___jp_1440_;
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_declName_1410_);
lean_dec_ref(v_params_1408_);
v_a_1562_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1560_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1560_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
v___jp_1570_:
{
if (v_suggest_1413_ == 0)
{
lean_dec(v_id_1409_);
v___y_1555_ = v___y_1574_;
v___y_1556_ = v___y_1573_;
v___y_1557_ = v___y_1571_;
v___y_1558_ = v___y_1572_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1575_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1573_);
v___x_1576_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1577_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_1575_, v___x_1576_);
lean_dec_ref(v___x_1575_);
if (v___x_1577_ == 0)
{
lean_object* v_symPrios_1578_; lean_object* v___x_1579_; 
lean_dec(v_kind_1411_);
v_symPrios_1578_ = lean_ctor_get(v_params_1408_, 5);
lean_inc_ref(v_symPrios_1578_);
lean_inc(v_declName_1410_);
v___x_1579_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1409_, v_declName_1410_, v_symPrios_1578_, v_minIndexable_1412_, v_suggest_1413_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v_thm_1441_ = v_a_1580_;
v___y_1442_ = v___y_1571_;
v___y_1443_ = v___y_1572_;
v___y_1444_ = v___y_1573_;
v___y_1445_ = v___y_1574_;
goto v___jp_1440_;
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_declName_1410_);
lean_dec_ref(v_params_1408_);
v_a_1581_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1579_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1579_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
lean_dec(v_id_1409_);
v___y_1555_ = v___y_1574_;
v___y_1556_ = v___y_1573_;
v___y_1557_ = v___y_1571_;
v___y_1558_ = v___y_1572_;
goto v___jp_1554_;
}
}
}
v___jp_1589_:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1412_, v___y_1591_, v___y_1593_, v___y_1592_, v___y_1590_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_dec_ref_known(v___x_1594_, 1);
v___y_1571_ = v___y_1591_;
v___y_1572_ = v___y_1593_;
v___y_1573_ = v___y_1592_;
v___y_1574_ = v___y_1590_;
goto v___jp_1570_;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_kind_1411_);
lean_dec(v_declName_1410_);
lean_dec(v_id_1409_);
lean_dec_ref(v_params_1408_);
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
v___jp_1603_:
{
if (lean_obj_tag(v_kind_1411_) == 2)
{
uint8_t v_gen_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_id_1409_);
v_gen_1608_ = lean_ctor_get_uint8(v_kind_1411_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_kind_1411_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1610_ = v_kind_1411_;
v_isShared_1611_ = v_isSharedCheck_1672_;
goto v_resetjp_1609_;
}
else
{
lean_dec(v_kind_1411_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1672_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; 
v___x_1612_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1412_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_config_1613_; lean_object* v_extensions_1614_; lean_object* v_extra_1615_; lean_object* v_extraInj_1616_; lean_object* v_extraFacts_1617_; lean_object* v_symPrios_1618_; lean_object* v_norm_1619_; lean_object* v_normProcs_1620_; lean_object* v_anchorRefs_x3f_1621_; lean_object* v___x_1623_; 
lean_dec_ref_known(v___x_1612_, 1);
v_config_1613_ = lean_ctor_get(v_params_1408_, 0);
lean_inc_ref(v_config_1613_);
v_extensions_1614_ = lean_ctor_get(v_params_1408_, 1);
lean_inc_ref(v_extensions_1614_);
v_extra_1615_ = lean_ctor_get(v_params_1408_, 2);
lean_inc_ref(v_extra_1615_);
v_extraInj_1616_ = lean_ctor_get(v_params_1408_, 3);
lean_inc_ref(v_extraInj_1616_);
v_extraFacts_1617_ = lean_ctor_get(v_params_1408_, 4);
lean_inc_ref(v_extraFacts_1617_);
v_symPrios_1618_ = lean_ctor_get(v_params_1408_, 5);
lean_inc_ref(v_symPrios_1618_);
v_norm_1619_ = lean_ctor_get(v_params_1408_, 6);
lean_inc_ref(v_norm_1619_);
v_normProcs_1620_ = lean_ctor_get(v_params_1408_, 7);
lean_inc_ref(v_normProcs_1620_);
v_anchorRefs_x3f_1621_ = lean_ctor_get(v_params_1408_, 8);
lean_inc(v_anchorRefs_x3f_1621_);
lean_dec_ref(v_params_1408_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 0);
v___x_1623_ = v___x_1610_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_1663_, 0, v_gen_1608_);
v___x_1623_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; 
lean_inc_ref(v_symPrios_1618_);
lean_inc(v_declName_1410_);
v___x_1624_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1410_, v___x_1623_, v_symPrios_1618_, v___x_1476_, v___x_1476_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1626_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1626_, 0, v_gen_1608_);
lean_inc_ref(v_symPrios_1618_);
lean_inc(v_declName_1410_);
v___x_1627_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1410_, v___x_1626_, v_symPrios_1618_, v___x_1476_, v___x_1476_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1627_) == 0)
{
if (v_warn_1414_ == 0)
{
lean_object* v_a_1628_; 
lean_dec(v_declName_1410_);
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1627_, 1);
v___y_1461_ = v_config_1613_;
v___y_1462_ = v_normProcs_1620_;
v___y_1463_ = v_extraFacts_1617_;
v___y_1464_ = v_symPrios_1618_;
v___y_1465_ = v_a_1628_;
v___y_1466_ = v_extraInj_1616_;
v___y_1467_ = v_a_1625_;
v___y_1468_ = v_anchorRefs_x3f_1621_;
v___y_1469_ = v_extensions_1614_;
v___y_1470_ = v_extra_1615_;
v___y_1471_ = v_norm_1619_;
goto v___jp_1460_;
}
else
{
lean_object* v_a_1629_; lean_object* v_patterns_1630_; lean_object* v_origin_1631_; lean_object* v_cnstrs_1632_; uint8_t v___x_1633_; 
v_a_1629_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1627_, 1);
v_patterns_1630_ = lean_ctor_get(v_a_1625_, 3);
v_origin_1631_ = lean_ctor_get(v_a_1625_, 5);
v_cnstrs_1632_ = lean_ctor_get(v_a_1625_, 7);
v___x_1633_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1614_, v_origin_1631_, v_patterns_1630_, v_cnstrs_1632_);
if (v___x_1633_ == 0)
{
lean_dec(v_declName_1410_);
v___y_1461_ = v_config_1613_;
v___y_1462_ = v_normProcs_1620_;
v___y_1463_ = v_extraFacts_1617_;
v___y_1464_ = v_symPrios_1618_;
v___y_1465_ = v_a_1629_;
v___y_1466_ = v_extraInj_1616_;
v___y_1467_ = v_a_1625_;
v___y_1468_ = v_anchorRefs_x3f_1621_;
v___y_1469_ = v_extensions_1614_;
v___y_1470_ = v_extra_1615_;
v___y_1471_ = v_norm_1619_;
goto v___jp_1460_;
}
else
{
lean_object* v_patterns_1634_; lean_object* v_origin_1635_; lean_object* v_cnstrs_1636_; uint8_t v___x_1637_; 
v_patterns_1634_ = lean_ctor_get(v_a_1629_, 3);
v_origin_1635_ = lean_ctor_get(v_a_1629_, 5);
v_cnstrs_1636_ = lean_ctor_get(v_a_1629_, 7);
v___x_1637_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1614_, v_origin_1635_, v_patterns_1634_, v_cnstrs_1636_);
if (v___x_1637_ == 0)
{
lean_dec(v_declName_1410_);
v___y_1461_ = v_config_1613_;
v___y_1462_ = v_normProcs_1620_;
v___y_1463_ = v_extraFacts_1617_;
v___y_1464_ = v_symPrios_1618_;
v___y_1465_ = v_a_1629_;
v___y_1466_ = v_extraInj_1616_;
v___y_1467_ = v_a_1625_;
v___y_1468_ = v_anchorRefs_x3f_1621_;
v___y_1469_ = v_extensions_1614_;
v___y_1470_ = v_extra_1615_;
v___y_1471_ = v_norm_1619_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1638_; 
v___x_1638_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1614_, v_declName_1410_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_dec_ref_known(v___x_1638_, 1);
v___y_1461_ = v_config_1613_;
v___y_1462_ = v_normProcs_1620_;
v___y_1463_ = v_extraFacts_1617_;
v___y_1464_ = v_symPrios_1618_;
v___y_1465_ = v_a_1629_;
v___y_1466_ = v_extraInj_1616_;
v___y_1467_ = v_a_1625_;
v___y_1468_ = v_anchorRefs_x3f_1621_;
v___y_1469_ = v_extensions_1614_;
v___y_1470_ = v_extra_1615_;
v___y_1471_ = v_norm_1619_;
goto v___jp_1460_;
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v_a_1629_);
lean_dec(v_a_1625_);
lean_dec(v_anchorRefs_x3f_1621_);
lean_dec_ref(v_normProcs_1620_);
lean_dec_ref(v_norm_1619_);
lean_dec_ref(v_symPrios_1618_);
lean_dec_ref(v_extraFacts_1617_);
lean_dec_ref(v_extraInj_1616_);
lean_dec_ref(v_extra_1615_);
lean_dec_ref(v_extensions_1614_);
lean_dec_ref(v_config_1613_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
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
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_a_1625_);
lean_dec(v_anchorRefs_x3f_1621_);
lean_dec_ref(v_normProcs_1620_);
lean_dec_ref(v_norm_1619_);
lean_dec_ref(v_symPrios_1618_);
lean_dec_ref(v_extraFacts_1617_);
lean_dec_ref(v_extraInj_1616_);
lean_dec_ref(v_extra_1615_);
lean_dec_ref(v_extensions_1614_);
lean_dec_ref(v_config_1613_);
lean_dec(v_declName_1410_);
v_a_1647_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1627_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1627_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec(v_anchorRefs_x3f_1621_);
lean_dec_ref(v_normProcs_1620_);
lean_dec_ref(v_norm_1619_);
lean_dec_ref(v_symPrios_1618_);
lean_dec_ref(v_extraFacts_1617_);
lean_dec_ref(v_extraInj_1616_);
lean_dec_ref(v_extra_1615_);
lean_dec_ref(v_extensions_1614_);
lean_dec_ref(v_config_1613_);
lean_dec(v_declName_1410_);
v_a_1655_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1624_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1624_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_del_object(v___x_1610_);
lean_dec(v_declName_1410_);
lean_dec_ref(v_params_1408_);
v_a_1664_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1612_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1612_);
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
}
else
{
switch(lean_obj_tag(v_kind_1411_))
{
case 0:
{
v___y_1590_ = v___y_1607_;
v___y_1591_ = v___y_1604_;
v___y_1592_ = v___y_1606_;
v___y_1593_ = v___y_1605_;
goto v___jp_1589_;
}
case 1:
{
v___y_1590_ = v___y_1607_;
v___y_1591_ = v___y_1604_;
v___y_1592_ = v___y_1606_;
v___y_1593_ = v___y_1605_;
goto v___jp_1589_;
}
default: 
{
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v___y_1606_;
v___y_1574_ = v___y_1607_;
goto v___jp_1570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object* v_params_1715_, lean_object* v_id_1716_, lean_object* v_declName_1717_, lean_object* v_kind_1718_, lean_object* v_minIndexable_1719_, lean_object* v_suggest_1720_, lean_object* v_warn_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
uint8_t v_minIndexable_boxed_1727_; uint8_t v_suggest_boxed_1728_; uint8_t v_warn_boxed_1729_; lean_object* v_res_1730_; 
v_minIndexable_boxed_1727_ = lean_unbox(v_minIndexable_1719_);
v_suggest_boxed_1728_ = lean_unbox(v_suggest_1720_);
v_warn_boxed_1729_ = lean_unbox(v_warn_1721_);
v_res_1730_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_1715_, v_id_1716_, v_declName_1717_, v_kind_1718_, v_minIndexable_boxed_1727_, v_suggest_boxed_1728_, v_warn_boxed_1729_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object* v_declName_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1731_, v___y_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object* v_declName_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(v_declName_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_1745_, lean_object* v_constName_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1753_, lean_object* v_constName_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(v_00_u03b1_1753_, v_constName_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1761_, lean_object* v_ref_1762_, lean_object* v_constName_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1762_, v_constName_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1770_, lean_object* v_ref_1771_, lean_object* v_constName_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(v_00_u03b1_1770_, v_ref_1771_, v_constName_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v_ref_1771_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1779_, lean_object* v_ref_1780_, lean_object* v_msg_1781_, lean_object* v_declHint_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1780_, v_msg_1781_, v_declHint_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1789_, lean_object* v_ref_1790_, lean_object* v_msg_1791_, lean_object* v_declHint_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1789_, v_ref_1790_, v_msg_1791_, v_declHint_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v_ref_1790_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1799_, lean_object* v_declHint_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1799_, v_declHint_1800_, v___y_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1807_, lean_object* v_declHint_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1807_, v_declHint_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1815_, lean_object* v_ref_1816_, lean_object* v_msg_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1816_, v_msg_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_ref_1825_, lean_object* v_msg_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1824_, v_ref_1825_, v_msg_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v_ref_1825_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1835_, lean_object* v_val_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_config_1840_; lean_object* v_extensions_1841_; lean_object* v_extra_1842_; lean_object* v_extraInj_1843_; lean_object* v_extraFacts_1844_; lean_object* v_symPrios_1845_; lean_object* v_norm_1846_; lean_object* v_normProcs_1847_; lean_object* v_anchorRefs_x3f_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1878_; 
v_config_1840_ = lean_ctor_get(v_params_1835_, 0);
v_extensions_1841_ = lean_ctor_get(v_params_1835_, 1);
v_extra_1842_ = lean_ctor_get(v_params_1835_, 2);
v_extraInj_1843_ = lean_ctor_get(v_params_1835_, 3);
v_extraFacts_1844_ = lean_ctor_get(v_params_1835_, 4);
v_symPrios_1845_ = lean_ctor_get(v_params_1835_, 5);
v_norm_1846_ = lean_ctor_get(v_params_1835_, 6);
v_normProcs_1847_ = lean_ctor_get(v_params_1835_, 7);
v_anchorRefs_x3f_1848_ = lean_ctor_get(v_params_1835_, 8);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_params_1835_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1850_ = v_params_1835_;
v_isShared_1851_ = v_isSharedCheck_1878_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_anchorRefs_x3f_1848_);
lean_inc(v_normProcs_1847_);
lean_inc(v_norm_1846_);
lean_inc(v_symPrios_1845_);
lean_inc(v_extraFacts_1844_);
lean_inc(v_extraInj_1843_);
lean_inc(v_extra_1842_);
lean_inc(v_extensions_1841_);
lean_inc(v_config_1840_);
lean_dec(v_params_1835_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1878_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___y_1853_; 
if (lean_obj_tag(v_anchorRefs_x3f_1848_) == 0)
{
lean_object* v___x_1876_; 
v___x_1876_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_1853_ = v___x_1876_;
goto v___jp_1852_;
}
else
{
lean_object* v_val_1877_; 
v_val_1877_ = lean_ctor_get(v_anchorRefs_x3f_1848_, 0);
lean_inc(v_val_1877_);
lean_dec_ref_known(v_anchorRefs_x3f_1848_, 1);
v___y_1853_ = v_val_1877_;
goto v___jp_1852_;
}
v___jp_1852_:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1836_, v_a_1837_, v_a_1838_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1867_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1867_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1867_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1859_ = lean_array_push(v___y_1853_, v_a_1855_);
v___x_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 8, v___x_1860_);
v___x_1862_ = v___x_1850_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_config_1840_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_extensions_1841_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_extra_1842_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_extraInj_1843_);
lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_extraFacts_1844_);
lean_ctor_set(v_reuseFailAlloc_1866_, 5, v_symPrios_1845_);
lean_ctor_set(v_reuseFailAlloc_1866_, 6, v_norm_1846_);
lean_ctor_set(v_reuseFailAlloc_1866_, 7, v_normProcs_1847_);
lean_ctor_set(v_reuseFailAlloc_1866_, 8, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1864_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1862_);
v___x_1864_ = v___x_1857_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec_ref(v___y_1853_);
lean_del_object(v___x_1850_);
lean_dec_ref(v_normProcs_1847_);
lean_dec_ref(v_norm_1846_);
lean_dec_ref(v_symPrios_1845_);
lean_dec_ref(v_extraFacts_1844_);
lean_dec_ref(v_extraInj_1843_);
lean_dec_ref(v_extra_1842_);
lean_dec_ref(v_extensions_1841_);
lean_dec_ref(v_config_1840_);
v_a_1868_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1854_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1854_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_1879_, lean_object* v_val_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_1879_, v_val_1880_, v_a_1881_, v_a_1882_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
lean_dec(v_val_1880_);
return v_res_1884_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_1887_ = l_Lean_stringToMessageData(v___x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_config_1892_; uint8_t v_revert_1893_; 
v_config_1892_ = lean_ctor_get(v_params_1888_, 0);
v_revert_1893_ = lean_ctor_get_uint8(v_config_1892_, sizeof(void*)*14 + 30);
if (v_revert_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_box(0);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_1897_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1896_, v_a_1889_, v_a_1890_);
return v___x_1897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_1898_, v_a_1899_, v_a_1900_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec_ref(v_params_1898_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_1903_, lean_object* v___y_1904_){
_start:
{
uint8_t v___x_1906_; 
v___x_1906_ = l_Lean_Expr_hasMVar(v_e_1903_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_e_1903_);
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; lean_object* v_mctx_1909_; lean_object* v___x_1910_; lean_object* v_fst_1911_; lean_object* v_snd_1912_; lean_object* v___x_1913_; lean_object* v_cache_1914_; lean_object* v_zetaDeltaFVarIds_1915_; lean_object* v_postponed_1916_; lean_object* v_diag_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1926_; 
v___x_1908_ = lean_st_ref_get(v___y_1904_);
v_mctx_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc_ref(v_mctx_1909_);
lean_dec(v___x_1908_);
v___x_1910_ = l_Lean_instantiateMVarsCore(v_mctx_1909_, v_e_1903_);
v_fst_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_fst_1911_);
v_snd_1912_ = lean_ctor_get(v___x_1910_, 1);
lean_inc(v_snd_1912_);
lean_dec_ref(v___x_1910_);
v___x_1913_ = lean_st_ref_take(v___y_1904_);
v_cache_1914_ = lean_ctor_get(v___x_1913_, 1);
v_zetaDeltaFVarIds_1915_ = lean_ctor_get(v___x_1913_, 2);
v_postponed_1916_ = lean_ctor_get(v___x_1913_, 3);
v_diag_1917_ = lean_ctor_get(v___x_1913_, 4);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v___x_1913_, 0);
lean_dec(v_unused_1927_);
v___x_1919_ = v___x_1913_;
v_isShared_1920_ = v_isSharedCheck_1926_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_diag_1917_);
lean_inc(v_postponed_1916_);
lean_inc(v_zetaDeltaFVarIds_1915_);
lean_inc(v_cache_1914_);
lean_dec(v___x_1913_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1926_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v_snd_1912_);
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_snd_1912_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_cache_1914_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v_zetaDeltaFVarIds_1915_);
lean_ctor_set(v_reuseFailAlloc_1925_, 3, v_postponed_1916_);
lean_ctor_set(v_reuseFailAlloc_1925_, 4, v_diag_1917_);
v___x_1922_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_st_ref_put(v___y_1904_, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1924_, 0, v_fst_1911_);
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1928_, v___y_1929_);
lean_dec(v___y_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1932_, v___y_1936_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(uint8_t v___x_1950_, uint8_t v___x_1951_, uint8_t v_____do__lift_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
if (v_____do__lift_1952_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_box(v___x_1950_);
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = lean_box(v___x_1951_);
v___x_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v___x_1964_, lean_object* v___x_1965_, lean_object* v_____do__lift_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
uint8_t v___x_14719__boxed_1974_; uint8_t v___x_14720__boxed_1975_; uint8_t v_____do__lift_14721__boxed_1976_; lean_object* v_res_1977_; 
v___x_14719__boxed_1974_ = lean_unbox(v___x_1964_);
v___x_14720__boxed_1975_ = lean_unbox(v___x_1965_);
v_____do__lift_14721__boxed_1976_ = lean_unbox(v_____do__lift_1966_);
v_res_1977_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_14719__boxed_1974_, v___x_14720__boxed_1975_, v_____do__lift_14721__boxed_1976_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(uint8_t v___x_1978_, uint8_t v___x_1979_, lean_object* v_as_1980_, size_t v_i_1981_, size_t v_stop_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_usize_dec_eq(v_i_1981_, v_stop_1982_);
if (v___x_1988_ == 0)
{
uint8_t v___x_1989_; uint8_t v_a_1991_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1989_ = 1;
v___x_1997_ = lean_array_uget_borrowed(v_as_1980_, v_i_1981_);
lean_inc(v___x_1997_);
v___x_1998_ = l_Lean_Meta_isProof(v___x_1997_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; uint8_t v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2000_ = lean_unbox(v_a_1999_);
lean_dec(v_a_1999_);
if (v___x_2000_ == 0)
{
v_a_1991_ = v___x_1978_;
goto v___jp_1990_;
}
else
{
v_a_1991_ = v___x_1979_;
goto v___jp_1990_;
}
}
else
{
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_2001_; uint8_t v___x_2002_; 
v_a_2001_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2002_ = lean_unbox(v_a_2001_);
lean_dec(v_a_2001_);
v_a_1991_ = v___x_2002_;
goto v___jp_1990_;
}
else
{
return v___x_1998_;
}
}
v___jp_1990_:
{
if (v_a_1991_ == 0)
{
size_t v___x_1992_; size_t v___x_1993_; 
v___x_1992_ = ((size_t)1ULL);
v___x_1993_ = lean_usize_add(v_i_1981_, v___x_1992_);
v_i_1981_ = v___x_1993_;
goto _start;
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_box(v___x_1989_);
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
return v___x_1996_;
}
}
}
else
{
uint8_t v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2003_ = 0;
v___x_2004_ = lean_box(v___x_2003_);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v___x_2006_, lean_object* v___x_2007_, lean_object* v_as_2008_, lean_object* v_i_2009_, lean_object* v_stop_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
uint8_t v___x_14757__boxed_2016_; uint8_t v___x_14758__boxed_2017_; size_t v_i_boxed_2018_; size_t v_stop_boxed_2019_; lean_object* v_res_2020_; 
v___x_14757__boxed_2016_ = lean_unbox(v___x_2006_);
v___x_14758__boxed_2017_ = lean_unbox(v___x_2007_);
v_i_boxed_2018_ = lean_unbox_usize(v_i_2009_);
lean_dec(v_i_2009_);
v_stop_boxed_2019_ = lean_unbox_usize(v_stop_2010_);
lean_dec(v_stop_2010_);
v_res_2020_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_14757__boxed_2016_, v___x_14758__boxed_2017_, v_as_2008_, v_i_boxed_2018_, v_stop_boxed_2019_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec_ref(v_as_2008_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_p_2023_, lean_object* v_term_2024_, lean_object* v___x_2025_, uint8_t v___x_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v_toCold_2034_; lean_object* v_currRecDepth_2035_; lean_object* v_ref_2036_; uint16_t v_optionFlags_2037_; uint8_t v_suppressElabErrors_2038_; uint8_t v_isRecordingDeps_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2136_; 
v_toCold_2034_ = lean_ctor_get(v___y_2031_, 0);
v_currRecDepth_2035_ = lean_ctor_get(v___y_2031_, 1);
v_ref_2036_ = lean_ctor_get(v___y_2031_, 2);
v_optionFlags_2037_ = lean_ctor_get_uint16(v___y_2031_, sizeof(void*)*3);
v_suppressElabErrors_2038_ = lean_ctor_get_uint8(v___y_2031_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2039_ = lean_ctor_get_uint8(v___y_2031_, sizeof(void*)*3 + 3);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___y_2031_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2041_ = v___y_2031_;
v_isShared_2042_ = v_isSharedCheck_2136_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_ref_2036_);
lean_inc(v_currRecDepth_2035_);
lean_inc(v_toCold_2034_);
lean_dec(v___y_2031_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2136_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v_ref_2043_; lean_object* v___x_2045_; 
v_ref_2043_ = l_Lean_replaceRef(v_p_2023_, v_ref_2036_);
lean_dec(v_ref_2036_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 2, v_ref_2043_);
v___x_2045_ = v___x_2041_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_toCold_2034_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_currRecDepth_2035_);
lean_ctor_set(v_reuseFailAlloc_2135_, 2, v_ref_2043_);
lean_ctor_set_uint16(v_reuseFailAlloc_2135_, sizeof(void*)*3, v_optionFlags_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2135_, sizeof(void*)*3 + 2, v_suppressElabErrors_2038_);
lean_ctor_set_uint8(v_reuseFailAlloc_2135_, sizeof(void*)*3 + 3, v_isRecordingDeps_2039_);
v___x_2045_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_Elab_Term_elabTerm(v_term_2024_, v___x_2025_, v___x_2026_, v___x_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___x_2045_, v___y_2032_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; uint8_t v___x_2048_; lean_object* v___x_2049_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = 1;
v___x_2049_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_2048_, v___x_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___x_2045_, v___y_2032_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v___x_2050_; lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref_known(v___x_2049_, 1);
v___x_2050_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_2047_, v___y_2030_);
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2118_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2118_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
uint8_t v___x_2055_; 
v___x_2055_ = l_Lean_Expr_hasSyntheticSorry(v_a_2051_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2056_ = l_Lean_Expr_eta(v_a_2051_);
v___x_2057_ = l_Lean_Expr_hasMVar(v___x_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
lean_dec_ref(v___x_2045_);
v___x_2058_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0));
v___x_2059_ = lean_box(v___x_2057_);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2056_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2058_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2062_);
v___x_2064_ = v___x_2053_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
else
{
lean_object* v___x_2066_; 
lean_del_object(v___x_2053_);
v___x_2066_ = l_Lean_Meta_abstractMVars(v___x_2056_, v___x_2026_, v___y_2029_, v___y_2030_, v___x_2045_, v___y_2032_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2105_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2105_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2105_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v_paramNames_2071_; lean_object* v_mvars_2072_; lean_object* v_expr_2073_; uint8_t v_a_2075_; lean_object* v___y_2084_; lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v_paramNames_2071_ = lean_ctor_get(v_a_2067_, 0);
lean_inc_ref(v_paramNames_2071_);
v_mvars_2072_ = lean_ctor_get(v_a_2067_, 1);
lean_inc_ref(v_mvars_2072_);
v_expr_2073_ = lean_ctor_get(v_a_2067_, 2);
lean_inc_ref(v_expr_2073_);
lean_dec(v_a_2067_);
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = lean_array_get_size(v_mvars_2072_);
v___x_2097_ = lean_nat_dec_lt(v___x_2095_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
lean_dec_ref(v_mvars_2072_);
v___x_2098_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2057_, v___x_2055_, v___x_2097_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___x_2045_, v___y_2032_);
lean_dec_ref(v___x_2045_);
v___y_2084_ = v___x_2098_;
goto v___jp_2083_;
}
else
{
if (v___x_2097_ == 0)
{
lean_dec_ref(v_mvars_2072_);
lean_dec_ref(v___x_2045_);
v_a_2075_ = v___x_2057_;
goto v___jp_2074_;
}
else
{
size_t v___x_2099_; size_t v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = ((size_t)0ULL);
v___x_2100_ = lean_usize_of_nat(v___x_2096_);
v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2057_, v___x_2055_, v_mvars_2072_, v___x_2099_, v___x_2100_, v___y_2029_, v___y_2030_, v___x_2045_, v___y_2032_);
lean_dec_ref(v_mvars_2072_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; uint8_t v___x_2103_; lean_object* v___x_2104_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = lean_unbox(v_a_2102_);
lean_dec(v_a_2102_);
v___x_2104_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2057_, v___x_2055_, v___x_2103_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___x_2045_, v___y_2032_);
lean_dec_ref(v___x_2045_);
v___y_2084_ = v___x_2104_;
goto v___jp_2083_;
}
else
{
lean_dec_ref(v___x_2045_);
v___y_2084_ = v___x_2101_;
goto v___jp_2083_;
}
}
}
v___jp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2076_ = lean_box(v_a_2075_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v_expr_2073_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v_paramNames_2071_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2079_);
v___x_2081_ = v___x_2069_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
v___jp_2083_:
{
if (lean_obj_tag(v___y_2084_) == 0)
{
lean_object* v_a_2085_; uint8_t v___x_2086_; 
v_a_2085_ = lean_ctor_get(v___y_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___y_2084_, 1);
v___x_2086_ = lean_unbox(v_a_2085_);
lean_dec(v_a_2085_);
v_a_2075_ = v___x_2086_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref(v_expr_2073_);
lean_dec_ref(v_paramNames_2071_);
lean_del_object(v___x_2069_);
v_a_2087_ = lean_ctor_get(v___y_2084_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___y_2084_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___y_2084_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___y_2084_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec_ref(v___x_2045_);
v_a_2106_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2066_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2066_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
lean_dec(v_a_2051_);
lean_dec_ref(v___x_2045_);
v___x_2114_ = lean_box(0);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2114_);
v___x_2116_ = v___x_2053_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2114_);
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
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_a_2047_);
lean_dec_ref(v___x_2045_);
v_a_2119_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2049_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2049_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v___x_2045_);
v_a_2127_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2046_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2046_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_p_2137_, lean_object* v_term_2138_, lean_object* v___x_2139_, lean_object* v___x_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
uint8_t v___x_14820__boxed_2148_; lean_object* v_res_2149_; 
v___x_14820__boxed_2148_ = lean_unbox(v___x_2140_);
v_res_2149_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_p_2137_, v_term_2138_, v___x_2139_, v___x_14820__boxed_2148_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v_p_2137_);
return v_res_2149_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__2));
v___x_2155_ = l_Lean_stringToMessageData(v___x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(lean_object* v_params_2156_, lean_object* v_p_2157_, lean_object* v_fst_2158_, lean_object* v_fst_2159_, uint8_t v___x_2160_, uint8_t v_minIndexable_2161_, lean_object* v_kind_2162_, lean_object* v_idx_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_symPrios_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; 
v_symPrios_2169_ = lean_ctor_get(v_params_2156_, 5);
lean_inc_ref(v_symPrios_2169_);
lean_dec_ref(v_params_2156_);
v___x_2170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__1));
v___x_2171_ = lean_name_append_index_after(v___x_2170_, v_idx_2163_);
v___x_2172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v_p_2157_);
v___x_2173_ = 0;
v___x_2174_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2172_, v_fst_2158_, v_fst_2159_, v_kind_2162_, v_symPrios_2169_, v___x_2160_, v___x_2173_, v_minIndexable_2161_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2185_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2185_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2185_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
if (lean_obj_tag(v_a_2175_) == 1)
{
lean_object* v_val_2179_; lean_object* v___x_2181_; 
v_val_2179_ = lean_ctor_get(v_a_2175_, 0);
lean_inc(v_val_2179_);
lean_dec_ref_known(v_a_2175_, 1);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v_val_2179_);
v___x_2181_ = v___x_2177_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_val_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_del_object(v___x_2177_);
lean_dec(v_a_2175_);
v___x_2183_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3);
v___x_2184_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2183_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
return v___x_2184_;
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
v_a_2186_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2174_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2174_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed(lean_object* v_params_2194_, lean_object* v_p_2195_, lean_object* v_fst_2196_, lean_object* v_fst_2197_, lean_object* v___x_2198_, lean_object* v_minIndexable_2199_, lean_object* v_kind_2200_, lean_object* v_idx_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
uint8_t v___x_15051__boxed_2207_; uint8_t v_minIndexable_boxed_2208_; lean_object* v_res_2209_; 
v___x_15051__boxed_2207_ = lean_unbox(v___x_2198_);
v_minIndexable_boxed_2208_ = lean_unbox(v_minIndexable_2199_);
v_res_2209_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(v_params_2194_, v_p_2195_, v_fst_2196_, v_fst_2197_, v___x_15051__boxed_2207_, v_minIndexable_boxed_2208_, v_kind_2200_, v_idx_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
return v_res_2209_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = lean_box(1);
v___x_2211_ = l_Lean_MessageData_ofFormat(v___x_2210_);
return v___x_2211_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__2));
v___x_2216_ = l_Lean_MessageData_ofFormat(v___x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(lean_object* v_x_2217_, lean_object* v_x_2218_){
_start:
{
if (lean_obj_tag(v_x_2218_) == 0)
{
return v_x_2217_;
}
else
{
lean_object* v_head_2219_; lean_object* v_tail_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2242_; 
v_head_2219_ = lean_ctor_get(v_x_2218_, 0);
v_tail_2220_ = lean_ctor_get(v_x_2218_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_x_2218_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2222_ = v_x_2218_;
v_isShared_2223_ = v_isSharedCheck_2242_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_tail_2220_);
lean_inc(v_head_2219_);
lean_dec(v_x_2218_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2242_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v_before_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2240_; 
v_before_2224_ = lean_ctor_get(v_head_2219_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_head_2219_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; 
v_unused_2241_ = lean_ctor_get(v_head_2219_, 1);
lean_dec(v_unused_2241_);
v___x_2226_ = v_head_2219_;
v_isShared_2227_ = v_isSharedCheck_2240_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_before_2224_);
lean_dec(v_head_2219_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2240_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2228_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2227_ == 0)
{
lean_ctor_set_tag(v___x_2226_, 7);
lean_ctor_set(v___x_2226_, 1, v___x_2228_);
lean_ctor_set(v___x_2226_, 0, v_x_2217_);
v___x_2230_ = v___x_2226_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_x_2217_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3);
if (v_isShared_2223_ == 0)
{
lean_ctor_set_tag(v___x_2222_, 7);
lean_ctor_set(v___x_2222_, 1, v___x_2231_);
lean_ctor_set(v___x_2222_, 0, v___x_2230_);
v___x_2233_ = v___x_2222_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = l_Lean_MessageData_ofSyntax(v_before_2224_);
v___x_2235_ = l_Lean_indentD(v___x_2234_);
v___x_2236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2233_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
v_x_2217_ = v___x_2236_;
v_x_2218_ = v_tail_2220_;
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
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__1));
v___x_2247_ = l_Lean_MessageData_ofFormat(v___x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(lean_object* v_msgData_2248_, lean_object* v_macroStack_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2252_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2250_);
v___x_2253_ = l_Lean_Elab_pp_macroStack;
v___x_2254_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_2252_, v___x_2253_);
lean_dec_ref(v___x_2252_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; 
lean_dec(v_macroStack_2249_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v_msgData_2248_);
return v___x_2255_;
}
else
{
if (lean_obj_tag(v_macroStack_2249_) == 0)
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v_msgData_2248_);
return v___x_2256_;
}
else
{
lean_object* v_head_2257_; lean_object* v_after_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2273_; 
v_head_2257_ = lean_ctor_get(v_macroStack_2249_, 0);
lean_inc(v_head_2257_);
v_after_2258_ = lean_ctor_get(v_head_2257_, 1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_head_2257_);
if (v_isSharedCheck_2273_ == 0)
{
lean_object* v_unused_2274_; 
v_unused_2274_ = lean_ctor_get(v_head_2257_, 0);
lean_dec(v_unused_2274_);
v___x_2260_ = v_head_2257_;
v_isShared_2261_ = v_isSharedCheck_2273_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_after_2258_);
lean_dec(v_head_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2273_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2262_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2261_ == 0)
{
lean_ctor_set_tag(v___x_2260_, 7);
lean_ctor_set(v___x_2260_, 1, v___x_2262_);
lean_ctor_set(v___x_2260_, 0, v_msgData_2248_);
v___x_2264_ = v___x_2260_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_msgData_2248_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v_msgData_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2265_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2);
v___x_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = l_Lean_MessageData_ofSyntax(v_after_2258_);
v___x_2268_ = l_Lean_indentD(v___x_2267_);
v_msgData_2269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2269_, 0, v___x_2266_);
lean_ctor_set(v_msgData_2269_, 1, v___x_2268_);
v___x_2270_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(v_msgData_2269_, v_macroStack_2249_);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
return v___x_2271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_2275_, lean_object* v_macroStack_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2275_, v_macroStack_2276_, v___y_2277_);
lean_dec_ref(v___y_2277_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(lean_object* v_msg_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_ref_2288_; lean_object* v_macroStack_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v_a_2292_; lean_object* v___x_2293_; lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2302_; 
v_ref_2288_ = lean_ctor_get(v___y_2285_, 2);
v_macroStack_2289_ = lean_ctor_get(v___y_2281_, 1);
v___x_2290_ = l_Lean_Elab_getBetterRef(v_ref_2288_, v_macroStack_2289_);
v___x_2291_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2280_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref(v___x_2291_);
lean_inc(v_macroStack_2289_);
v___x_2293_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_a_2292_, v_macroStack_2289_, v___y_2285_);
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2290_);
lean_ctor_set(v___x_2298_, 1, v_a_2294_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set_tag(v___x_2296_, 1);
lean_ctor_set(v___x_2296_, 0, v___x_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg___boxed(lean_object* v_msg_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2311_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2314_ = l_Lean_stringToMessageData(v___x_2313_);
return v___x_2314_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2317_ = l_Lean_stringToMessageData(v___x_2316_);
return v___x_2317_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2320_ = l_Lean_stringToMessageData(v___x_2319_);
return v___x_2320_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_2323_ = l_Lean_stringToMessageData(v___x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2326_, lean_object* v_p_2327_, lean_object* v_mod_x3f_2328_, lean_object* v_term_2329_, uint8_t v_minIndexable_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v___y_2339_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; uint8_t v___y_2479_; uint8_t v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v_kind_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v_toCold_2700_; lean_object* v_currRecDepth_2701_; lean_object* v_ref_2702_; uint16_t v_optionFlags_2703_; uint8_t v_suppressElabErrors_2704_; uint8_t v_isRecordingDeps_2705_; lean_object* v_ref_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_toCold_2700_ = lean_ctor_get(v_a_2335_, 0);
v_currRecDepth_2701_ = lean_ctor_get(v_a_2335_, 1);
v_ref_2702_ = lean_ctor_get(v_a_2335_, 2);
v_optionFlags_2703_ = lean_ctor_get_uint16(v_a_2335_, sizeof(void*)*3);
v_suppressElabErrors_2704_ = lean_ctor_get_uint8(v_a_2335_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2705_ = lean_ctor_get_uint8(v_a_2335_, sizeof(void*)*3 + 3);
v_ref_2706_ = l_Lean_replaceRef(v_p_2327_, v_ref_2702_);
lean_inc(v_currRecDepth_2701_);
lean_inc_ref(v_toCold_2700_);
v___x_2707_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2707_, 0, v_toCold_2700_);
lean_ctor_set(v___x_2707_, 1, v_currRecDepth_2701_);
lean_ctor_set(v___x_2707_, 2, v_ref_2706_);
lean_ctor_set_uint16(v___x_2707_, sizeof(void*)*3, v_optionFlags_2703_);
lean_ctor_set_uint8(v___x_2707_, sizeof(void*)*3 + 2, v_suppressElabErrors_2704_);
lean_ctor_set_uint8(v___x_2707_, sizeof(void*)*3 + 3, v_isRecordingDeps_2705_);
v___x_2708_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2326_, v___x_2707_, v_a_2336_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_dec_ref_known(v___x_2708_, 1);
if (lean_obj_tag(v_mod_x3f_2328_) == 1)
{
lean_object* v_val_2709_; lean_object* v___x_2710_; 
v_val_2709_ = lean_ctor_get(v_mod_x3f_2328_, 0);
lean_inc(v_val_2709_);
v___x_2710_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2709_, v___x_2707_, v_a_2336_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
switch(lean_obj_tag(v_a_2711_))
{
case 0:
{
lean_object* v_k_2712_; 
v_k_2712_ = lean_ctor_get(v_a_2711_, 0);
lean_inc(v_k_2712_);
lean_dec_ref_known(v_a_2711_, 1);
if (lean_obj_tag(v_k_2712_) == 9)
{
lean_dec_ref_known(v_mod_x3f_2328_, 1);
lean_dec(v_term_2329_);
lean_dec(v_p_2327_);
lean_dec_ref(v_params_2326_);
v___y_2659_ = v_a_2331_;
v___y_2660_ = v_a_2332_;
v___y_2661_ = v_a_2333_;
v___y_2662_ = v_a_2334_;
v___y_2663_ = v___x_2707_;
v___y_2664_ = v_a_2336_;
goto v___jp_2658_;
}
else
{
v_kind_2590_ = v_k_2712_;
v___y_2591_ = v_a_2331_;
v___y_2592_ = v_a_2332_;
v___y_2593_ = v_a_2333_;
v___y_2594_ = v_a_2334_;
v___y_2595_ = v___x_2707_;
v___y_2596_ = v_a_2336_;
goto v___jp_2589_;
}
}
case 1:
{
lean_dec_ref_known(v_a_2711_, 0);
lean_dec_ref_known(v_mod_x3f_2328_, 1);
lean_dec(v_term_2329_);
lean_dec(v_p_2327_);
lean_dec_ref(v_params_2326_);
v___y_2676_ = v_a_2331_;
v___y_2677_ = v_a_2332_;
v___y_2678_ = v_a_2333_;
v___y_2679_ = v_a_2334_;
v___y_2680_ = v___x_2707_;
v___y_2681_ = v_a_2336_;
goto v___jp_2675_;
}
case 3:
{
v___y_2693_ = v_a_2331_;
v___y_2694_ = v_a_2332_;
v___y_2695_ = v_a_2333_;
v___y_2696_ = v_a_2334_;
v___y_2697_ = v___x_2707_;
v___y_2698_ = v_a_2336_;
goto v___jp_2692_;
}
case 5:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec_ref_known(v_a_2711_, 1);
lean_dec_ref_known(v_mod_x3f_2328_, 1);
lean_dec(v_term_2329_);
lean_dec(v_p_2327_);
lean_dec_ref(v_params_2326_);
v___x_2713_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2714_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2713_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v___x_2707_, v_a_2336_);
lean_dec_ref_known(v___x_2707_, 3);
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
case 8:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec_ref_known(v_a_2711_, 0);
lean_dec_ref_known(v_mod_x3f_2328_, 1);
lean_dec(v_term_2329_);
lean_dec(v_p_2327_);
lean_dec_ref(v_params_2326_);
v___x_2723_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2724_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2723_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v___x_2707_, v_a_2336_);
lean_dec_ref_known(v___x_2707_, 3);
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2724_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2724_);
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
case 10:
{
lean_dec_ref_known(v_a_2711_, 0);
lean_dec_ref_known(v_mod_x3f_2328_, 1);
lean_dec(v_term_2329_);
lean_dec(v_p_2327_);
lean_dec_ref(v_params_2326_);
v___y_2676_ = v_a_2331_;
v___y_2677_ = v_a_2332_;
v___y_2678_ = v_a_2333_;
v___y_2679_ = v_a_2334_;
v___y_2680_ = v___x_2707_;
v___y_2681_ = v_a_2336_;
goto v___jp_2675_;
}
default: 
{
lean_dec(v_a_2711_);
lean_dec_ref_known(v_mod_x3f_2328_, 1);
lean_dec(v_term_2329_);
lean_dec(v_p_2327_);
lean_dec_ref(v_params_2326_);
v___y_2659_ = v_a_2331_;
v___y_2660_ = v_a_2332_;
v___y_2661_ = v_a_2333_;
v___y_2662_ = v_a_2334_;
v___y_2663_ = v___x_2707_;
v___y_2664_ = v_a_2336_;
goto v___jp_2658_;
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec_ref_known(v_mod_x3f_2328_, 1);
lean_dec_ref_known(v___x_2707_, 3);
lean_dec(v_term_2329_);
lean_dec(v_p_2327_);
lean_dec_ref(v_params_2326_);
v_a_2733_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2710_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2710_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
v___y_2693_ = v_a_2331_;
v___y_2694_ = v_a_2332_;
v___y_2695_ = v_a_2333_;
v___y_2696_ = v_a_2334_;
v___y_2697_ = v___x_2707_;
v___y_2698_ = v_a_2336_;
goto v___jp_2692_;
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec_ref_known(v___x_2707_, 3);
lean_dec(v_term_2329_);
lean_dec(v_mod_x3f_2328_);
lean_dec(v_p_2327_);
lean_dec_ref(v_params_2326_);
v_a_2741_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2708_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2708_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
v___jp_2338_:
{
lean_object* v_config_2340_; lean_object* v_extensions_2341_; lean_object* v_extra_2342_; lean_object* v_extraInj_2343_; lean_object* v_extraFacts_2344_; lean_object* v_symPrios_2345_; lean_object* v_norm_2346_; lean_object* v_normProcs_2347_; lean_object* v_anchorRefs_x3f_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2357_; 
v_config_2340_ = lean_ctor_get(v_params_2326_, 0);
v_extensions_2341_ = lean_ctor_get(v_params_2326_, 1);
v_extra_2342_ = lean_ctor_get(v_params_2326_, 2);
v_extraInj_2343_ = lean_ctor_get(v_params_2326_, 3);
v_extraFacts_2344_ = lean_ctor_get(v_params_2326_, 4);
v_symPrios_2345_ = lean_ctor_get(v_params_2326_, 5);
v_norm_2346_ = lean_ctor_get(v_params_2326_, 6);
v_normProcs_2347_ = lean_ctor_get(v_params_2326_, 7);
v_anchorRefs_x3f_2348_ = lean_ctor_get(v_params_2326_, 8);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_params_2326_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2350_ = v_params_2326_;
v_isShared_2351_ = v_isSharedCheck_2357_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_anchorRefs_x3f_2348_);
lean_inc(v_normProcs_2347_);
lean_inc(v_norm_2346_);
lean_inc(v_symPrios_2345_);
lean_inc(v_extraFacts_2344_);
lean_inc(v_extraInj_2343_);
lean_inc(v_extra_2342_);
lean_inc(v_extensions_2341_);
lean_inc(v_config_2340_);
lean_dec(v_params_2326_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2357_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2352_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2344_, v___y_2339_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 4, v___x_2352_);
v___x_2354_ = v___x_2350_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_config_2340_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_extensions_2341_);
lean_ctor_set(v_reuseFailAlloc_2356_, 2, v_extra_2342_);
lean_ctor_set(v_reuseFailAlloc_2356_, 3, v_extraInj_2343_);
lean_ctor_set(v_reuseFailAlloc_2356_, 4, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2356_, 5, v_symPrios_2345_);
lean_ctor_set(v_reuseFailAlloc_2356_, 6, v_norm_2346_);
lean_ctor_set(v_reuseFailAlloc_2356_, 7, v_normProcs_2347_);
lean_ctor_set(v_reuseFailAlloc_2356_, 8, v_anchorRefs_x3f_2348_);
v___x_2354_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
return v___x_2355_;
}
}
}
v___jp_2358_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
v___x_2368_ = lean_array_get_size(v___y_2361_);
lean_dec_ref(v___y_2361_);
v___x_2369_ = lean_unsigned_to_nat(0u);
v___x_2370_ = lean_nat_dec_eq(v___x_2368_, v___x_2369_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec_ref(v___y_2359_);
lean_dec_ref(v_params_2326_);
v___x_2371_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2372_ = l_Lean_indentExpr(v___y_2360_);
v___x_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2373_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec_ref(v___y_2366_);
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
else
{
lean_dec_ref(v___y_2366_);
lean_dec_ref(v___y_2360_);
v___y_2339_ = v___y_2359_;
goto v___jp_2338_;
}
}
v___jp_2383_:
{
if (lean_obj_tag(v_mod_x3f_2328_) == 0)
{
v___y_2359_ = v___y_2390_;
v___y_2360_ = v___y_2389_;
v___y_2361_ = v___y_2388_;
v___y_2362_ = v___y_2385_;
v___y_2363_ = v___y_2387_;
v___y_2364_ = v___y_2391_;
v___y_2365_ = v___y_2386_;
v___y_2366_ = v___y_2384_;
v___y_2367_ = v___y_2392_;
goto v___jp_2358_;
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref_known(v_mod_x3f_2328_, 1);
lean_dec_ref(v___y_2390_);
lean_dec_ref(v___y_2388_);
lean_dec_ref(v_params_2326_);
v___x_2393_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2394_ = l_Lean_indentExpr(v___y_2389_);
v___x_2395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2393_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2395_, v___y_2385_, v___y_2387_, v___y_2391_, v___y_2386_, v___y_2384_, v___y_2392_);
lean_dec_ref(v___y_2384_);
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
v___jp_2405_:
{
lean_object* v___x_2422_; 
lean_inc(v___y_2421_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
v___x_2422_ = lean_apply_7(v___y_2412_, v___y_2411_, v___y_2413_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, lean_box(0));
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2432_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2432_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2432_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
v___x_2427_ = l_Lean_PersistentArray_push___redArg(v___y_2407_, v_a_2423_);
v___x_2428_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2428_, 0, v___y_2415_);
lean_ctor_set(v___x_2428_, 1, v___y_2410_);
lean_ctor_set(v___x_2428_, 2, v___x_2427_);
lean_ctor_set(v___x_2428_, 3, v___y_2408_);
lean_ctor_set(v___x_2428_, 4, v___y_2416_);
lean_ctor_set(v___x_2428_, 5, v___y_2406_);
lean_ctor_set(v___x_2428_, 6, v___y_2414_);
lean_ctor_set(v___x_2428_, 7, v___y_2409_);
lean_ctor_set(v___x_2428_, 8, v___y_2417_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2428_);
v___x_2430_ = v___x_2425_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec_ref(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec_ref(v___y_2406_);
v_a_2433_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2422_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2422_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
v___jp_2441_:
{
lean_object* v___x_2458_; 
v___x_2458_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2330_, v___y_2446_, v___y_2450_, v___y_2449_, v___y_2457_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_dec_ref_known(v___x_2458_, 1);
v___y_2406_ = v___y_2451_;
v___y_2407_ = v___y_2442_;
v___y_2408_ = v___y_2443_;
v___y_2409_ = v___y_2452_;
v___y_2410_ = v___y_2444_;
v___y_2411_ = v___y_2445_;
v___y_2412_ = v___y_2453_;
v___y_2413_ = v___y_2454_;
v___y_2414_ = v___y_2456_;
v___y_2415_ = v___y_2455_;
v___y_2416_ = v___y_2447_;
v___y_2417_ = v___y_2448_;
v___y_2418_ = v___y_2446_;
v___y_2419_ = v___y_2450_;
v___y_2420_ = v___y_2449_;
v___y_2421_ = v___y_2457_;
goto v___jp_2405_;
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec_ref(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v___y_2442_);
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
v___jp_2467_:
{
if (v___y_2479_ == 0)
{
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
v___y_2384_ = v___y_2469_;
v___y_2385_ = v___y_2468_;
v___y_2386_ = v___y_2470_;
v___y_2387_ = v___y_2471_;
v___y_2388_ = v___y_2476_;
v___y_2389_ = v___y_2475_;
v___y_2390_ = v___y_2474_;
v___y_2391_ = v___y_2477_;
v___y_2392_ = v___y_2478_;
goto v___jp_2383_;
}
else
{
lean_object* v_extra_2480_; 
lean_dec_ref(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v_mod_x3f_2328_);
v_extra_2480_ = lean_ctor_get(v_params_2326_, 2);
lean_inc_ref(v_extra_2480_);
if (lean_obj_tag(v___y_2473_) == 2)
{
lean_object* v_config_2481_; lean_object* v_extensions_2482_; lean_object* v_extraInj_2483_; lean_object* v_extraFacts_2484_; lean_object* v_symPrios_2485_; lean_object* v_norm_2486_; lean_object* v_normProcs_2487_; lean_object* v_anchorRefs_x3f_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2543_; 
v_config_2481_ = lean_ctor_get(v_params_2326_, 0);
v_extensions_2482_ = lean_ctor_get(v_params_2326_, 1);
v_extraInj_2483_ = lean_ctor_get(v_params_2326_, 3);
v_extraFacts_2484_ = lean_ctor_get(v_params_2326_, 4);
v_symPrios_2485_ = lean_ctor_get(v_params_2326_, 5);
v_norm_2486_ = lean_ctor_get(v_params_2326_, 6);
v_normProcs_2487_ = lean_ctor_get(v_params_2326_, 7);
v_anchorRefs_x3f_2488_ = lean_ctor_get(v_params_2326_, 8);
v_isSharedCheck_2543_ = !lean_is_exclusive(v_params_2326_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v_params_2326_, 2);
lean_dec(v_unused_2544_);
v___x_2490_ = v_params_2326_;
v_isShared_2491_ = v_isSharedCheck_2543_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_anchorRefs_x3f_2488_);
lean_inc(v_normProcs_2487_);
lean_inc(v_norm_2486_);
lean_inc(v_symPrios_2485_);
lean_inc(v_extraFacts_2484_);
lean_inc(v_extraInj_2483_);
lean_inc(v_extensions_2482_);
lean_inc(v_config_2481_);
lean_dec(v_params_2326_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2543_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v_size_2492_; uint8_t v_gen_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2542_; 
v_size_2492_ = lean_ctor_get(v_extra_2480_, 2);
v_gen_2493_ = lean_ctor_get_uint8(v___y_2473_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___y_2473_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2495_ = v___y_2473_;
v_isShared_2496_ = v_isSharedCheck_2542_;
goto v_resetjp_2494_;
}
else
{
lean_dec(v___y_2473_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2542_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; 
v___x_2497_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2330_, v___y_2477_, v___y_2470_, v___y_2469_, v___y_2478_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v___x_2499_; 
lean_dec_ref_known(v___x_2497_, 1);
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 0);
v___x_2499_ = v___x_2495_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2533_, 0, v_gen_2493_);
v___x_2499_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2500_; 
lean_inc_ref(v___y_2472_);
lean_inc(v___y_2478_);
lean_inc_ref(v___y_2469_);
lean_inc(v___y_2470_);
lean_inc_ref(v___y_2477_);
lean_inc(v_size_2492_);
v___x_2500_ = lean_apply_7(v___y_2472_, v___x_2499_, v_size_2492_, v___y_2477_, v___y_2470_, v___y_2469_, v___y_2478_, lean_box(0));
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2500_, 1);
v___x_2502_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2502_, 0, v_gen_2493_);
lean_inc(v___y_2478_);
lean_inc(v___y_2470_);
lean_inc_ref(v___y_2477_);
lean_inc(v_size_2492_);
v___x_2503_ = lean_apply_7(v___y_2472_, v___x_2502_, v_size_2492_, v___y_2477_, v___y_2470_, v___y_2469_, v___y_2478_, lean_box(0));
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2516_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2506_ = v___x_2503_;
v_isShared_2507_ = v_isSharedCheck_2516_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2516_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2508_ = l_Lean_PersistentArray_push___redArg(v_extra_2480_, v_a_2501_);
v___x_2509_ = l_Lean_PersistentArray_push___redArg(v___x_2508_, v_a_2504_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 2, v___x_2509_);
v___x_2511_ = v___x_2490_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_config_2481_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_extensions_2482_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_extraInj_2483_);
lean_ctor_set(v_reuseFailAlloc_2515_, 4, v_extraFacts_2484_);
lean_ctor_set(v_reuseFailAlloc_2515_, 5, v_symPrios_2485_);
lean_ctor_set(v_reuseFailAlloc_2515_, 6, v_norm_2486_);
lean_ctor_set(v_reuseFailAlloc_2515_, 7, v_normProcs_2487_);
lean_ctor_set(v_reuseFailAlloc_2515_, 8, v_anchorRefs_x3f_2488_);
v___x_2511_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2513_; 
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2511_);
v___x_2513_ = v___x_2506_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec(v_a_2501_);
lean_del_object(v___x_2490_);
lean_dec(v_anchorRefs_x3f_2488_);
lean_dec_ref(v_normProcs_2487_);
lean_dec_ref(v_norm_2486_);
lean_dec_ref(v_symPrios_2485_);
lean_dec_ref(v_extraFacts_2484_);
lean_dec_ref(v_extraInj_2483_);
lean_dec_ref(v_extensions_2482_);
lean_dec_ref(v_config_2481_);
lean_dec_ref(v_extra_2480_);
v_a_2517_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2503_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2503_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_del_object(v___x_2490_);
lean_dec(v_anchorRefs_x3f_2488_);
lean_dec_ref(v_normProcs_2487_);
lean_dec_ref(v_norm_2486_);
lean_dec_ref(v_symPrios_2485_);
lean_dec_ref(v_extraFacts_2484_);
lean_dec_ref(v_extraInj_2483_);
lean_dec_ref(v_extensions_2482_);
lean_dec_ref(v_config_2481_);
lean_dec_ref(v_extra_2480_);
lean_dec_ref(v___y_2472_);
lean_dec_ref(v___y_2469_);
v_a_2525_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2500_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2500_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_del_object(v___x_2495_);
lean_del_object(v___x_2490_);
lean_dec(v_anchorRefs_x3f_2488_);
lean_dec_ref(v_normProcs_2487_);
lean_dec_ref(v_norm_2486_);
lean_dec_ref(v_symPrios_2485_);
lean_dec_ref(v_extraFacts_2484_);
lean_dec_ref(v_extraInj_2483_);
lean_dec_ref(v_extensions_2482_);
lean_dec_ref(v_config_2481_);
lean_dec_ref(v_extra_2480_);
lean_dec_ref(v___y_2472_);
lean_dec_ref(v___y_2469_);
v_a_2534_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2497_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2497_);
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
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
else
{
switch(lean_obj_tag(v___y_2473_))
{
case 0:
{
lean_object* v_config_2545_; lean_object* v_extensions_2546_; lean_object* v_extraInj_2547_; lean_object* v_extraFacts_2548_; lean_object* v_symPrios_2549_; lean_object* v_norm_2550_; lean_object* v_normProcs_2551_; lean_object* v_anchorRefs_x3f_2552_; lean_object* v_size_2553_; 
v_config_2545_ = lean_ctor_get(v_params_2326_, 0);
lean_inc_ref(v_config_2545_);
v_extensions_2546_ = lean_ctor_get(v_params_2326_, 1);
lean_inc_ref(v_extensions_2546_);
v_extraInj_2547_ = lean_ctor_get(v_params_2326_, 3);
lean_inc_ref(v_extraInj_2547_);
v_extraFacts_2548_ = lean_ctor_get(v_params_2326_, 4);
lean_inc_ref(v_extraFacts_2548_);
v_symPrios_2549_ = lean_ctor_get(v_params_2326_, 5);
lean_inc_ref(v_symPrios_2549_);
v_norm_2550_ = lean_ctor_get(v_params_2326_, 6);
lean_inc_ref(v_norm_2550_);
v_normProcs_2551_ = lean_ctor_get(v_params_2326_, 7);
lean_inc_ref(v_normProcs_2551_);
v_anchorRefs_x3f_2552_ = lean_ctor_get(v_params_2326_, 8);
lean_inc(v_anchorRefs_x3f_2552_);
lean_dec_ref(v_params_2326_);
v_size_2553_ = lean_ctor_get(v_extra_2480_, 2);
lean_inc(v_size_2553_);
v___y_2442_ = v_extra_2480_;
v___y_2443_ = v_extraInj_2547_;
v___y_2444_ = v_extensions_2546_;
v___y_2445_ = v___y_2473_;
v___y_2446_ = v___y_2477_;
v___y_2447_ = v_extraFacts_2548_;
v___y_2448_ = v_anchorRefs_x3f_2552_;
v___y_2449_ = v___y_2469_;
v___y_2450_ = v___y_2470_;
v___y_2451_ = v_symPrios_2549_;
v___y_2452_ = v_normProcs_2551_;
v___y_2453_ = v___y_2472_;
v___y_2454_ = v_size_2553_;
v___y_2455_ = v_config_2545_;
v___y_2456_ = v_norm_2550_;
v___y_2457_ = v___y_2478_;
goto v___jp_2441_;
}
case 1:
{
lean_object* v_config_2554_; lean_object* v_extensions_2555_; lean_object* v_extraInj_2556_; lean_object* v_extraFacts_2557_; lean_object* v_symPrios_2558_; lean_object* v_norm_2559_; lean_object* v_normProcs_2560_; lean_object* v_anchorRefs_x3f_2561_; lean_object* v_size_2562_; 
v_config_2554_ = lean_ctor_get(v_params_2326_, 0);
lean_inc_ref(v_config_2554_);
v_extensions_2555_ = lean_ctor_get(v_params_2326_, 1);
lean_inc_ref(v_extensions_2555_);
v_extraInj_2556_ = lean_ctor_get(v_params_2326_, 3);
lean_inc_ref(v_extraInj_2556_);
v_extraFacts_2557_ = lean_ctor_get(v_params_2326_, 4);
lean_inc_ref(v_extraFacts_2557_);
v_symPrios_2558_ = lean_ctor_get(v_params_2326_, 5);
lean_inc_ref(v_symPrios_2558_);
v_norm_2559_ = lean_ctor_get(v_params_2326_, 6);
lean_inc_ref(v_norm_2559_);
v_normProcs_2560_ = lean_ctor_get(v_params_2326_, 7);
lean_inc_ref(v_normProcs_2560_);
v_anchorRefs_x3f_2561_ = lean_ctor_get(v_params_2326_, 8);
lean_inc(v_anchorRefs_x3f_2561_);
lean_dec_ref(v_params_2326_);
v_size_2562_ = lean_ctor_get(v_extra_2480_, 2);
lean_inc(v_size_2562_);
v___y_2442_ = v_extra_2480_;
v___y_2443_ = v_extraInj_2556_;
v___y_2444_ = v_extensions_2555_;
v___y_2445_ = v___y_2473_;
v___y_2446_ = v___y_2477_;
v___y_2447_ = v_extraFacts_2557_;
v___y_2448_ = v_anchorRefs_x3f_2561_;
v___y_2449_ = v___y_2469_;
v___y_2450_ = v___y_2470_;
v___y_2451_ = v_symPrios_2558_;
v___y_2452_ = v_normProcs_2560_;
v___y_2453_ = v___y_2472_;
v___y_2454_ = v_size_2562_;
v___y_2455_ = v_config_2554_;
v___y_2456_ = v_norm_2559_;
v___y_2457_ = v___y_2478_;
goto v___jp_2441_;
}
default: 
{
lean_object* v_config_2563_; lean_object* v_extensions_2564_; lean_object* v_extraInj_2565_; lean_object* v_extraFacts_2566_; lean_object* v_symPrios_2567_; lean_object* v_norm_2568_; lean_object* v_normProcs_2569_; lean_object* v_anchorRefs_x3f_2570_; lean_object* v_size_2571_; 
v_config_2563_ = lean_ctor_get(v_params_2326_, 0);
lean_inc_ref(v_config_2563_);
v_extensions_2564_ = lean_ctor_get(v_params_2326_, 1);
lean_inc_ref(v_extensions_2564_);
v_extraInj_2565_ = lean_ctor_get(v_params_2326_, 3);
lean_inc_ref(v_extraInj_2565_);
v_extraFacts_2566_ = lean_ctor_get(v_params_2326_, 4);
lean_inc_ref(v_extraFacts_2566_);
v_symPrios_2567_ = lean_ctor_get(v_params_2326_, 5);
lean_inc_ref(v_symPrios_2567_);
v_norm_2568_ = lean_ctor_get(v_params_2326_, 6);
lean_inc_ref(v_norm_2568_);
v_normProcs_2569_ = lean_ctor_get(v_params_2326_, 7);
lean_inc_ref(v_normProcs_2569_);
v_anchorRefs_x3f_2570_ = lean_ctor_get(v_params_2326_, 8);
lean_inc(v_anchorRefs_x3f_2570_);
lean_dec_ref(v_params_2326_);
v_size_2571_ = lean_ctor_get(v_extra_2480_, 2);
lean_inc(v_size_2571_);
v___y_2406_ = v_symPrios_2567_;
v___y_2407_ = v_extra_2480_;
v___y_2408_ = v_extraInj_2565_;
v___y_2409_ = v_normProcs_2569_;
v___y_2410_ = v_extensions_2564_;
v___y_2411_ = v___y_2473_;
v___y_2412_ = v___y_2472_;
v___y_2413_ = v_size_2571_;
v___y_2414_ = v_norm_2568_;
v___y_2415_ = v_config_2563_;
v___y_2416_ = v_extraFacts_2566_;
v___y_2417_ = v_anchorRefs_x3f_2570_;
v___y_2418_ = v___y_2477_;
v___y_2419_ = v___y_2470_;
v___y_2420_ = v___y_2469_;
v___y_2421_ = v___y_2478_;
goto v___jp_2405_;
}
}
}
}
}
v___jp_2572_:
{
uint8_t v___x_2585_; 
v___x_2585_ = l_Lean_Expr_isForall(v___y_2577_);
if (v___x_2585_ == 0)
{
v___y_2468_ = v___y_2579_;
v___y_2469_ = v___y_2583_;
v___y_2470_ = v___y_2582_;
v___y_2471_ = v___y_2580_;
v___y_2472_ = v___y_2575_;
v___y_2473_ = v___y_2574_;
v___y_2474_ = v___y_2576_;
v___y_2475_ = v___y_2577_;
v___y_2476_ = v___y_2578_;
v___y_2477_ = v___y_2581_;
v___y_2478_ = v___y_2584_;
v___y_2479_ = v___x_2585_;
goto v___jp_2467_;
}
else
{
if (v___y_2573_ == 0)
{
v___y_2468_ = v___y_2579_;
v___y_2469_ = v___y_2583_;
v___y_2470_ = v___y_2582_;
v___y_2471_ = v___y_2580_;
v___y_2472_ = v___y_2575_;
v___y_2473_ = v___y_2574_;
v___y_2474_ = v___y_2576_;
v___y_2475_ = v___y_2577_;
v___y_2476_ = v___y_2578_;
v___y_2477_ = v___y_2581_;
v___y_2478_ = v___y_2584_;
v___y_2479_ = v___x_2585_;
goto v___jp_2467_;
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2586_ = lean_array_get_size(v___y_2578_);
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = lean_nat_dec_eq(v___x_2586_, v___x_2587_);
if (v___x_2588_ == 0)
{
v___y_2468_ = v___y_2579_;
v___y_2469_ = v___y_2583_;
v___y_2470_ = v___y_2582_;
v___y_2471_ = v___y_2580_;
v___y_2472_ = v___y_2575_;
v___y_2473_ = v___y_2574_;
v___y_2474_ = v___y_2576_;
v___y_2475_ = v___y_2577_;
v___y_2476_ = v___y_2578_;
v___y_2477_ = v___y_2581_;
v___y_2478_ = v___y_2584_;
v___y_2479_ = v___x_2585_;
goto v___jp_2467_;
}
else
{
if (lean_obj_tag(v_mod_x3f_2328_) == 0)
{
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
v___y_2384_ = v___y_2583_;
v___y_2385_ = v___y_2579_;
v___y_2386_ = v___y_2582_;
v___y_2387_ = v___y_2580_;
v___y_2388_ = v___y_2578_;
v___y_2389_ = v___y_2577_;
v___y_2390_ = v___y_2576_;
v___y_2391_ = v___y_2581_;
v___y_2392_ = v___y_2584_;
goto v___jp_2383_;
}
else
{
v___y_2468_ = v___y_2579_;
v___y_2469_ = v___y_2583_;
v___y_2470_ = v___y_2582_;
v___y_2471_ = v___y_2580_;
v___y_2472_ = v___y_2575_;
v___y_2473_ = v___y_2574_;
v___y_2474_ = v___y_2576_;
v___y_2475_ = v___y_2577_;
v___y_2476_ = v___y_2578_;
v___y_2477_ = v___y_2581_;
v___y_2478_ = v___y_2584_;
v___y_2479_ = v___x_2585_;
goto v___jp_2467_;
}
}
}
}
}
v___jp_2589_:
{
lean_object* v___x_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___f_2600_; lean_object* v___x_2601_; 
v___x_2597_ = lean_box(0);
v___x_2598_ = 1;
v___x_2599_ = lean_box(v___x_2598_);
lean_inc(v_p_2327_);
v___f_2600_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2600_, 0, v_p_2327_);
lean_closure_set(v___f_2600_, 1, v_term_2329_);
lean_closure_set(v___f_2600_, 2, v___x_2597_);
lean_closure_set(v___f_2600_, 3, v___x_2599_);
v___x_2601_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2600_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2649_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2649_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2649_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
if (lean_obj_tag(v_a_2602_) == 1)
{
lean_object* v_val_2606_; lean_object* v_snd_2607_; lean_object* v_fst_2608_; lean_object* v_fst_2609_; lean_object* v_snd_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___f_2613_; lean_object* v___x_2614_; 
lean_del_object(v___x_2604_);
v_val_2606_ = lean_ctor_get(v_a_2602_, 0);
lean_inc(v_val_2606_);
lean_dec_ref_known(v_a_2602_, 1);
v_snd_2607_ = lean_ctor_get(v_val_2606_, 1);
lean_inc(v_snd_2607_);
v_fst_2608_ = lean_ctor_get(v_val_2606_, 0);
lean_inc_n(v_fst_2608_, 2);
lean_dec(v_val_2606_);
v_fst_2609_ = lean_ctor_get(v_snd_2607_, 0);
lean_inc_n(v_fst_2609_, 3);
v_snd_2610_ = lean_ctor_get(v_snd_2607_, 1);
lean_inc(v_snd_2610_);
lean_dec(v_snd_2607_);
v___x_2611_ = lean_box(v___x_2598_);
v___x_2612_ = lean_box(v_minIndexable_2330_);
lean_inc_ref(v_params_2326_);
v___f_2613_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed), 13, 6);
lean_closure_set(v___f_2613_, 0, v_params_2326_);
lean_closure_set(v___f_2613_, 1, v_p_2327_);
lean_closure_set(v___f_2613_, 2, v_fst_2608_);
lean_closure_set(v___f_2613_, 3, v_fst_2609_);
lean_closure_set(v___f_2613_, 4, v___x_2611_);
lean_closure_set(v___f_2613_, 5, v___x_2612_);
lean_inc(v___y_2596_);
lean_inc_ref(v___y_2595_);
lean_inc(v___y_2594_);
lean_inc_ref(v___y_2593_);
v___x_2614_ = lean_infer_type(v_fst_2609_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2616_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc_n(v_a_2615_, 2);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2616_ = l_Lean_Meta_isProp(v_a_2615_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; uint8_t v___x_2618_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = lean_unbox(v_a_2617_);
lean_dec(v_a_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_a_2615_);
lean_dec_ref(v___f_2613_);
lean_dec(v_snd_2610_);
lean_dec(v_fst_2609_);
lean_dec(v_fst_2608_);
lean_dec(v_kind_2590_);
lean_dec(v_mod_x3f_2328_);
lean_dec_ref(v_params_2326_);
v___x_2619_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2620_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2619_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec_ref(v___y_2595_);
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
else
{
uint8_t v___x_2629_; 
v___x_2629_ = lean_unbox(v_snd_2610_);
lean_dec(v_snd_2610_);
v___y_2573_ = v___x_2629_;
v___y_2574_ = v_kind_2590_;
v___y_2575_ = v___f_2613_;
v___y_2576_ = v_fst_2609_;
v___y_2577_ = v_a_2615_;
v___y_2578_ = v_fst_2608_;
v___y_2579_ = v___y_2591_;
v___y_2580_ = v___y_2592_;
v___y_2581_ = v___y_2593_;
v___y_2582_ = v___y_2594_;
v___y_2583_ = v___y_2595_;
v___y_2584_ = v___y_2596_;
goto v___jp_2572_;
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_a_2615_);
lean_dec_ref(v___f_2613_);
lean_dec(v_snd_2610_);
lean_dec(v_fst_2609_);
lean_dec(v_fst_2608_);
lean_dec_ref(v___y_2595_);
lean_dec(v_kind_2590_);
lean_dec(v_mod_x3f_2328_);
lean_dec_ref(v_params_2326_);
v_a_2630_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2616_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2616_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec_ref(v___f_2613_);
lean_dec(v_snd_2610_);
lean_dec(v_fst_2609_);
lean_dec(v_fst_2608_);
lean_dec_ref(v___y_2595_);
lean_dec(v_kind_2590_);
lean_dec(v_mod_x3f_2328_);
lean_dec_ref(v_params_2326_);
v_a_2638_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2614_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2614_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v___x_2647_; 
lean_dec(v_a_2602_);
lean_dec_ref(v___y_2595_);
lean_dec(v_kind_2590_);
lean_dec(v_mod_x3f_2328_);
lean_dec(v_p_2327_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v_params_2326_);
v___x_2647_ = v___x_2604_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_params_2326_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec_ref(v___y_2595_);
lean_dec(v_kind_2590_);
lean_dec(v_mod_x3f_2328_);
lean_dec(v_p_2327_);
lean_dec_ref(v_params_2326_);
v_a_2650_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2601_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2601_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
v___jp_2658_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
v___x_2665_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2666_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2665_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec_ref(v___y_2663_);
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
v___jp_2675_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
v___x_2682_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2683_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2682_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec_ref(v___y_2680_);
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
v___jp_2692_:
{
lean_object* v___x_2699_; 
v___x_2699_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_kind_2590_ = v___x_2699_;
v___y_2591_ = v___y_2693_;
v___y_2592_ = v___y_2694_;
v___y_2593_ = v___y_2695_;
v___y_2594_ = v___y_2696_;
v___y_2595_ = v___y_2697_;
v___y_2596_ = v___y_2698_;
goto v___jp_2589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2749_, lean_object* v_p_2750_, lean_object* v_mod_x3f_2751_, lean_object* v_term_2752_, lean_object* v_minIndexable_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
uint8_t v_minIndexable_boxed_2761_; lean_object* v_res_2762_; 
v_minIndexable_boxed_2761_ = lean_unbox(v_minIndexable_2753_);
v_res_2762_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2749_, v_p_2750_, v_mod_x3f_2751_, v_term_2752_, v_minIndexable_boxed_2761_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(uint8_t v___x_2763_, uint8_t v___x_2764_, lean_object* v_as_2765_, size_t v_i_2766_, size_t v_stop_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2763_, v___x_2764_, v_as_2765_, v_i_2766_, v_stop_2767_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v___x_2776_, lean_object* v___x_2777_, lean_object* v_as_2778_, lean_object* v_i_2779_, lean_object* v_stop_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
uint8_t v___x_16098__boxed_2788_; uint8_t v___x_16099__boxed_2789_; size_t v_i_boxed_2790_; size_t v_stop_boxed_2791_; lean_object* v_res_2792_; 
v___x_16098__boxed_2788_ = lean_unbox(v___x_2776_);
v___x_16099__boxed_2789_ = lean_unbox(v___x_2777_);
v_i_boxed_2790_ = lean_unbox_usize(v_i_2779_);
lean_dec(v_i_2779_);
v_stop_boxed_2791_ = lean_unbox_usize(v_stop_2780_);
lean_dec(v_stop_2780_);
v_res_2792_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v___x_16098__boxed_2788_, v___x_16099__boxed_2789_, v_as_2778_, v_i_boxed_2790_, v_stop_boxed_2791_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec_ref(v_as_2778_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(lean_object* v_00_u03b1_2793_, lean_object* v_msg_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___boxed(lean_object* v_00_u03b1_2803_, lean_object* v_msg_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(v_00_u03b1_2803_, v_msg_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(lean_object* v_msgData_2813_, lean_object* v_macroStack_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2813_, v_macroStack_2814_, v___y_2819_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___boxed(lean_object* v_msgData_2823_, lean_object* v_macroStack_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(v_msgData_2823_, v_macroStack_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2833_, lean_object* v_val_2834_, lean_object* v___x_2835_, uint8_t v___y_2836_, lean_object* v_____r_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v___x_2845_; lean_object* v_ext_2846_; lean_object* v_toEnvExtension_2847_; lean_object* v_env_2848_; lean_object* v_config_2849_; lean_object* v_extensions_2850_; lean_object* v_extra_2851_; lean_object* v_extraInj_2852_; lean_object* v_extraFacts_2853_; lean_object* v_symPrios_2854_; lean_object* v_norm_2855_; lean_object* v_normProcs_2856_; lean_object* v_anchorRefs_x3f_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2869_; 
v___x_2845_ = lean_st_ref_get(v___y_2843_);
v_ext_2846_ = lean_ctor_get(v_val_2834_, 1);
v_toEnvExtension_2847_ = lean_ctor_get(v_ext_2846_, 0);
v_env_2848_ = lean_ctor_get(v___x_2845_, 0);
lean_inc_ref(v_env_2848_);
lean_dec(v___x_2845_);
v_config_2849_ = lean_ctor_get(v_params_2833_, 0);
v_extensions_2850_ = lean_ctor_get(v_params_2833_, 1);
v_extra_2851_ = lean_ctor_get(v_params_2833_, 2);
v_extraInj_2852_ = lean_ctor_get(v_params_2833_, 3);
v_extraFacts_2853_ = lean_ctor_get(v_params_2833_, 4);
v_symPrios_2854_ = lean_ctor_get(v_params_2833_, 5);
v_norm_2855_ = lean_ctor_get(v_params_2833_, 6);
v_normProcs_2856_ = lean_ctor_get(v_params_2833_, 7);
v_anchorRefs_x3f_2857_ = lean_ctor_get(v_params_2833_, 8);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_params_2833_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2859_ = v_params_2833_;
v_isShared_2860_ = v_isSharedCheck_2869_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_anchorRefs_x3f_2857_);
lean_inc(v_normProcs_2856_);
lean_inc(v_norm_2855_);
lean_inc(v_symPrios_2854_);
lean_inc(v_extraFacts_2853_);
lean_inc(v_extraInj_2852_);
lean_inc(v_extra_2851_);
lean_inc(v_extensions_2850_);
lean_inc(v_config_2849_);
lean_dec(v_params_2833_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2869_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v_asyncMode_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
v_asyncMode_2861_ = lean_ctor_get(v_toEnvExtension_2847_, 2);
v___x_2862_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2835_, v_val_2834_, v_env_2848_, v_asyncMode_2861_, v___y_2836_);
v___x_2863_ = lean_array_push(v_extensions_2850_, v___x_2862_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 1, v___x_2863_);
v___x_2865_ = v___x_2859_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_config_2849_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v___x_2863_);
lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_extra_2851_);
lean_ctor_set(v_reuseFailAlloc_2868_, 3, v_extraInj_2852_);
lean_ctor_set(v_reuseFailAlloc_2868_, 4, v_extraFacts_2853_);
lean_ctor_set(v_reuseFailAlloc_2868_, 5, v_symPrios_2854_);
lean_ctor_set(v_reuseFailAlloc_2868_, 6, v_norm_2855_);
lean_ctor_set(v_reuseFailAlloc_2868_, 7, v_normProcs_2856_);
lean_ctor_set(v_reuseFailAlloc_2868_, 8, v_anchorRefs_x3f_2857_);
v___x_2865_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
return v___x_2867_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2870_, lean_object* v_val_2871_, lean_object* v___x_2872_, lean_object* v___y_2873_, lean_object* v_____r_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
uint8_t v___y_30061__boxed_2882_; lean_object* v_res_2883_; 
v___y_30061__boxed_2882_ = lean_unbox(v___y_2873_);
v_res_2883_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2870_, v_val_2871_, v___x_2872_, v___y_30061__boxed_2882_, v_____r_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec_ref(v___x_2872_);
lean_dec_ref(v_val_2871_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2884_, lean_object* v_id_2885_, uint8_t v_minIndexable_2886_, lean_object* v_as_x27_2887_, lean_object* v_b_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
if (lean_obj_tag(v_as_x27_2887_) == 0)
{
lean_object* v___x_2894_; 
lean_dec(v_id_2885_);
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v_b_2888_);
return v___x_2894_;
}
else
{
lean_object* v_head_2895_; lean_object* v_tail_2896_; lean_object* v_toCold_2897_; lean_object* v_currRecDepth_2898_; lean_object* v_ref_2899_; uint16_t v_optionFlags_2900_; uint8_t v_suppressElabErrors_2901_; uint8_t v_isRecordingDeps_2902_; uint8_t v___x_2903_; lean_object* v___x_2904_; lean_object* v_ref_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_head_2895_ = lean_ctor_get(v_as_x27_2887_, 0);
v_tail_2896_ = lean_ctor_get(v_as_x27_2887_, 1);
v_toCold_2897_ = lean_ctor_get(v___y_2891_, 0);
v_currRecDepth_2898_ = lean_ctor_get(v___y_2891_, 1);
v_ref_2899_ = lean_ctor_get(v___y_2891_, 2);
v_optionFlags_2900_ = lean_ctor_get_uint16(v___y_2891_, sizeof(void*)*3);
v_suppressElabErrors_2901_ = lean_ctor_get_uint8(v___y_2891_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2902_ = lean_ctor_get_uint8(v___y_2891_, sizeof(void*)*3 + 3);
v___x_2903_ = 0;
v___x_2904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_ref_2905_ = l_Lean_replaceRef(v_p_2884_, v_ref_2899_);
lean_inc(v_currRecDepth_2898_);
lean_inc_ref(v_toCold_2897_);
v___x_2906_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2906_, 0, v_toCold_2897_);
lean_ctor_set(v___x_2906_, 1, v_currRecDepth_2898_);
lean_ctor_set(v___x_2906_, 2, v_ref_2905_);
lean_ctor_set_uint16(v___x_2906_, sizeof(void*)*3, v_optionFlags_2900_);
lean_ctor_set_uint8(v___x_2906_, sizeof(void*)*3 + 2, v_suppressElabErrors_2901_);
lean_ctor_set_uint8(v___x_2906_, sizeof(void*)*3 + 3, v_isRecordingDeps_2902_);
lean_inc(v_head_2895_);
lean_inc(v_id_2885_);
v___x_2907_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2888_, v_id_2885_, v_head_2895_, v___x_2904_, v_minIndexable_2886_, v___x_2903_, v___x_2903_, v___y_2889_, v___y_2890_, v___x_2906_, v___y_2892_);
lean_dec_ref_known(v___x_2906_, 3);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2907_, 1);
v_as_x27_2887_ = v_tail_2896_;
v_b_2888_ = v_a_2908_;
goto _start;
}
else
{
lean_dec(v_id_2885_);
return v___x_2907_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_2910_, lean_object* v_id_2911_, lean_object* v_minIndexable_2912_, lean_object* v_as_x27_2913_, lean_object* v_b_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
uint8_t v_minIndexable_boxed_2920_; lean_object* v_res_2921_; 
v_minIndexable_boxed_2920_ = lean_unbox(v_minIndexable_2912_);
v_res_2921_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_2910_, v_id_2911_, v_minIndexable_boxed_2920_, v_as_x27_2913_, v_b_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v_as_x27_2913_);
lean_dec(v_p_2910_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
if (lean_obj_tag(v_a_2923_) == 0)
{
lean_object* v___x_2925_; 
v___x_2925_ = l_List_reverse___redArg(v_a_2924_);
return v___x_2925_;
}
else
{
lean_object* v_head_2926_; lean_object* v_tail_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2938_; 
v_head_2926_ = lean_ctor_get(v_a_2923_, 0);
v_tail_2927_ = lean_ctor_get(v_a_2923_, 1);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_a_2923_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2929_ = v_a_2923_;
v_isShared_2930_ = v_isSharedCheck_2938_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_tail_2927_);
lean_inc(v_head_2926_);
lean_dec(v_a_2923_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2938_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v_kind_2931_; uint8_t v___x_2932_; 
v_kind_2931_ = lean_ctor_get(v_head_2926_, 6);
v___x_2932_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_2931_, v_k_2922_);
if (v___x_2932_ == 0)
{
lean_del_object(v___x_2929_);
lean_dec(v_head_2926_);
v_a_2923_ = v_tail_2927_;
goto _start;
}
else
{
lean_object* v___x_2935_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v_a_2924_);
v___x_2935_ = v___x_2929_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_head_2926_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_a_2924_);
v___x_2935_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
v_a_2923_ = v_tail_2927_;
v_a_2924_ = v___x_2935_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_k_2939_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_2943_, lean_object* v_msg_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_toCold_2952_; lean_object* v_currRecDepth_2953_; lean_object* v_ref_2954_; uint16_t v_optionFlags_2955_; uint8_t v_suppressElabErrors_2956_; uint8_t v_isRecordingDeps_2957_; lean_object* v_ref_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v_toCold_2952_ = lean_ctor_get(v___y_2949_, 0);
v_currRecDepth_2953_ = lean_ctor_get(v___y_2949_, 1);
v_ref_2954_ = lean_ctor_get(v___y_2949_, 2);
v_optionFlags_2955_ = lean_ctor_get_uint16(v___y_2949_, sizeof(void*)*3);
v_suppressElabErrors_2956_ = lean_ctor_get_uint8(v___y_2949_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2957_ = lean_ctor_get_uint8(v___y_2949_, sizeof(void*)*3 + 3);
v_ref_2958_ = l_Lean_replaceRef(v_ref_2943_, v_ref_2954_);
lean_inc(v_currRecDepth_2953_);
lean_inc_ref(v_toCold_2952_);
v___x_2959_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2959_, 0, v_toCold_2952_);
lean_ctor_set(v___x_2959_, 1, v_currRecDepth_2953_);
lean_ctor_set(v___x_2959_, 2, v_ref_2958_);
lean_ctor_set_uint16(v___x_2959_, sizeof(void*)*3, v_optionFlags_2955_);
lean_ctor_set_uint8(v___x_2959_, sizeof(void*)*3 + 2, v_suppressElabErrors_2956_);
lean_ctor_set_uint8(v___x_2959_, sizeof(void*)*3 + 3, v_isRecordingDeps_2957_);
v___x_2960_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___x_2959_, v___y_2950_);
lean_dec_ref_known(v___x_2959_, 3);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_2961_, lean_object* v_msg_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_2961_, v_msg_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v_ref_2961_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_2971_, lean_object* v_id_2972_, uint8_t v_minIndexable_2973_, lean_object* v_as_x27_2974_, lean_object* v_b_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
if (lean_obj_tag(v_as_x27_2974_) == 0)
{
lean_object* v___x_2981_; 
lean_dec(v_id_2972_);
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_b_2975_);
return v___x_2981_;
}
else
{
lean_object* v_head_2982_; lean_object* v_tail_2983_; lean_object* v_toCold_2984_; lean_object* v_currRecDepth_2985_; lean_object* v_ref_2986_; uint16_t v_optionFlags_2987_; uint8_t v_suppressElabErrors_2988_; uint8_t v_isRecordingDeps_2989_; uint8_t v___x_2990_; uint8_t v___x_2991_; lean_object* v___x_2992_; lean_object* v_ref_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_head_2982_ = lean_ctor_get(v_as_x27_2974_, 0);
v_tail_2983_ = lean_ctor_get(v_as_x27_2974_, 1);
v_toCold_2984_ = lean_ctor_get(v___y_2978_, 0);
v_currRecDepth_2985_ = lean_ctor_get(v___y_2978_, 1);
v_ref_2986_ = lean_ctor_get(v___y_2978_, 2);
v_optionFlags_2987_ = lean_ctor_get_uint16(v___y_2978_, sizeof(void*)*3);
v_suppressElabErrors_2988_ = lean_ctor_get_uint8(v___y_2978_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2989_ = lean_ctor_get_uint8(v___y_2978_, sizeof(void*)*3 + 3);
v___x_2990_ = 0;
v___x_2991_ = 1;
v___x_2992_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_ref_2993_ = l_Lean_replaceRef(v_p_2971_, v_ref_2986_);
lean_inc(v_currRecDepth_2985_);
lean_inc_ref(v_toCold_2984_);
v___x_2994_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2994_, 0, v_toCold_2984_);
lean_ctor_set(v___x_2994_, 1, v_currRecDepth_2985_);
lean_ctor_set(v___x_2994_, 2, v_ref_2993_);
lean_ctor_set_uint16(v___x_2994_, sizeof(void*)*3, v_optionFlags_2987_);
lean_ctor_set_uint8(v___x_2994_, sizeof(void*)*3 + 2, v_suppressElabErrors_2988_);
lean_ctor_set_uint8(v___x_2994_, sizeof(void*)*3 + 3, v_isRecordingDeps_2989_);
lean_inc(v_head_2982_);
lean_inc(v_id_2972_);
v___x_2995_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2975_, v_id_2972_, v_head_2982_, v___x_2992_, v_minIndexable_2973_, v___x_2990_, v___x_2991_, v___y_2976_, v___y_2977_, v___x_2994_, v___y_2979_);
lean_dec_ref_known(v___x_2994_, 3);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v_as_x27_2974_ = v_tail_2983_;
v_b_2975_ = v_a_2996_;
goto _start;
}
else
{
lean_dec(v_id_2972_);
return v___x_2995_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_2998_, lean_object* v_id_2999_, lean_object* v_minIndexable_3000_, lean_object* v_as_x27_3001_, lean_object* v_b_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
uint8_t v_minIndexable_boxed_3008_; lean_object* v_res_3009_; 
v_minIndexable_boxed_3008_ = lean_unbox(v_minIndexable_3000_);
v_res_3009_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_2998_, v_id_2999_, v_minIndexable_boxed_3008_, v_as_x27_3001_, v_b_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v_as_x27_3001_);
lean_dec(v_p_2998_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_3010_){
_start:
{
if (lean_obj_tag(v_x_3010_) == 0)
{
lean_object* v___x_3011_; 
v___x_3011_ = lean_box(0);
return v___x_3011_;
}
else
{
lean_object* v_head_3012_; lean_object* v_tail_3013_; lean_object* v_fst_3014_; uint8_t v___x_3015_; 
v_head_3012_ = lean_ctor_get(v_x_3010_, 0);
v_tail_3013_ = lean_ctor_get(v_x_3010_, 1);
v_fst_3014_ = lean_ctor_get(v_head_3012_, 0);
v___x_3015_ = l_Lean_isPrivateName(v_fst_3014_);
if (v___x_3015_ == 0)
{
v_x_3010_ = v_tail_3013_;
goto _start;
}
else
{
lean_object* v___x_3017_; 
lean_inc(v_head_3012_);
v___x_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_head_3012_);
return v___x_3017_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_3018_);
lean_dec(v_x_3018_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_3020_, lean_object* v_msgData_3021_, uint8_t v_severity_3022_, uint8_t v_isSilent_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; uint8_t v___y_3035_; uint8_t v___y_3036_; lean_object* v_toCold_3037_; lean_object* v___y_3038_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; uint8_t v___y_3070_; lean_object* v___y_3071_; uint8_t v___y_3072_; uint8_t v___y_3073_; lean_object* v___y_3074_; uint8_t v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; uint8_t v___y_3098_; uint8_t v___y_3099_; lean_object* v___y_3100_; uint8_t v___y_3104_; uint8_t v___y_3105_; uint8_t v___y_3106_; uint8_t v___x_3117_; uint8_t v___y_3119_; uint8_t v___y_3120_; uint8_t v___y_3121_; uint8_t v___y_3123_; uint8_t v___x_3131_; 
v___x_3117_ = 2;
v___x_3131_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3022_, v___x_3117_);
if (v___x_3131_ == 0)
{
v___y_3123_ = v___x_3131_;
goto v___jp_3122_;
}
else
{
uint8_t v___x_3132_; 
lean_inc_ref(v_msgData_3021_);
v___x_3132_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3021_);
v___y_3123_ = v___x_3132_;
goto v___jp_3122_;
}
v___jp_3029_:
{
lean_object* v_currNamespace_3039_; lean_object* v_openDecls_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v_env_3045_; lean_object* v_nextMacroScope_3046_; lean_object* v_ngen_3047_; lean_object* v_auxDeclNGen_3048_; lean_object* v_traceState_3049_; lean_object* v_cache_3050_; lean_object* v_recordedDeps_3051_; lean_object* v_messages_3052_; lean_object* v_infoState_3053_; lean_object* v_snapshotTasks_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3065_; 
v_currNamespace_3039_ = lean_ctor_get(v_toCold_3037_, 4);
v_openDecls_3040_ = lean_ctor_get(v_toCold_3037_, 5);
lean_inc(v_openDecls_3040_);
lean_inc(v_currNamespace_3039_);
v___x_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3041_, 0, v_currNamespace_3039_);
lean_ctor_set(v___x_3041_, 1, v_openDecls_3040_);
v___x_3042_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
lean_ctor_set(v___x_3042_, 1, v___y_3033_);
lean_inc_ref(v___y_3034_);
lean_inc_ref(v___y_3031_);
v___x_3043_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3043_, 0, v___y_3031_);
lean_ctor_set(v___x_3043_, 1, v___y_3032_);
lean_ctor_set(v___x_3043_, 2, v___y_3030_);
lean_ctor_set(v___x_3043_, 3, v___y_3034_);
lean_ctor_set(v___x_3043_, 4, v___x_3042_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*5, v___y_3036_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*5 + 1, v___y_3035_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*5 + 2, v_isSilent_3023_);
v___x_3044_ = lean_st_ref_take(v___y_3038_);
v_env_3045_ = lean_ctor_get(v___x_3044_, 0);
v_nextMacroScope_3046_ = lean_ctor_get(v___x_3044_, 1);
v_ngen_3047_ = lean_ctor_get(v___x_3044_, 2);
v_auxDeclNGen_3048_ = lean_ctor_get(v___x_3044_, 3);
v_traceState_3049_ = lean_ctor_get(v___x_3044_, 4);
v_cache_3050_ = lean_ctor_get(v___x_3044_, 5);
v_recordedDeps_3051_ = lean_ctor_get(v___x_3044_, 6);
v_messages_3052_ = lean_ctor_get(v___x_3044_, 7);
v_infoState_3053_ = lean_ctor_get(v___x_3044_, 8);
v_snapshotTasks_3054_ = lean_ctor_get(v___x_3044_, 9);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3056_ = v___x_3044_;
v_isShared_3057_ = v_isSharedCheck_3065_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_snapshotTasks_3054_);
lean_inc(v_infoState_3053_);
lean_inc(v_messages_3052_);
lean_inc(v_recordedDeps_3051_);
lean_inc(v_cache_3050_);
lean_inc(v_traceState_3049_);
lean_inc(v_auxDeclNGen_3048_);
lean_inc(v_ngen_3047_);
lean_inc(v_nextMacroScope_3046_);
lean_inc(v_env_3045_);
lean_dec(v___x_3044_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3065_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
v___x_3058_ = lean_box(0);
v___x_3059_ = l_Lean_MessageLog_add(v___x_3043_, v_messages_3052_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 7, v___x_3059_);
v___x_3061_ = v___x_3056_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_env_3045_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_nextMacroScope_3046_);
lean_ctor_set(v_reuseFailAlloc_3064_, 2, v_ngen_3047_);
lean_ctor_set(v_reuseFailAlloc_3064_, 3, v_auxDeclNGen_3048_);
lean_ctor_set(v_reuseFailAlloc_3064_, 4, v_traceState_3049_);
lean_ctor_set(v_reuseFailAlloc_3064_, 5, v_cache_3050_);
lean_ctor_set(v_reuseFailAlloc_3064_, 6, v_recordedDeps_3051_);
lean_ctor_set(v_reuseFailAlloc_3064_, 7, v___x_3059_);
lean_ctor_set(v_reuseFailAlloc_3064_, 8, v_infoState_3053_);
lean_ctor_set(v_reuseFailAlloc_3064_, 9, v_snapshotTasks_3054_);
v___x_3061_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = lean_st_ref_put(v___y_3038_, v___x_3061_);
v___x_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3058_);
return v___x_3063_;
}
}
}
v___jp_3066_:
{
lean_object* v_fileName_3075_; lean_object* v_fileMap_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3092_; 
v_fileName_3075_ = lean_ctor_get(v___y_3071_, 0);
v_fileMap_3076_ = lean_ctor_get(v___y_3071_, 1);
v___x_3077_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3021_);
v___x_3078_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_3077_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3092_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3092_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
lean_inc_ref_n(v_fileMap_3076_, 2);
v___x_3083_ = l_Lean_FileMap_toPosition(v_fileMap_3076_, v___y_3069_);
lean_dec(v___y_3069_);
v___x_3084_ = l_Lean_FileMap_toPosition(v_fileMap_3076_, v___y_3074_);
lean_dec(v___y_3074_);
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
v___x_3086_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_3070_ == 0)
{
lean_del_object(v___x_3081_);
lean_dec_ref(v___y_3068_);
v___y_3030_ = v___x_3085_;
v___y_3031_ = v_fileName_3075_;
v___y_3032_ = v___x_3083_;
v___y_3033_ = v_a_3079_;
v___y_3034_ = v___x_3086_;
v___y_3035_ = v___y_3073_;
v___y_3036_ = v___y_3072_;
v_toCold_3037_ = v___y_3067_;
v___y_3038_ = v___y_3027_;
goto v___jp_3029_;
}
else
{
uint8_t v___x_3087_; 
lean_inc(v_a_3079_);
v___x_3087_ = l_Lean_MessageData_hasTag(v___y_3068_, v_a_3079_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3090_; 
lean_dec_ref_known(v___x_3085_, 1);
lean_dec_ref(v___x_3083_);
lean_dec(v_a_3079_);
v___x_3088_ = lean_box(0);
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 0, v___x_3088_);
v___x_3090_ = v___x_3081_;
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
else
{
lean_del_object(v___x_3081_);
v___y_3030_ = v___x_3085_;
v___y_3031_ = v_fileName_3075_;
v___y_3032_ = v___x_3083_;
v___y_3033_ = v_a_3079_;
v___y_3034_ = v___x_3086_;
v___y_3035_ = v___y_3073_;
v___y_3036_ = v___y_3072_;
v_toCold_3037_ = v___y_3067_;
v___y_3038_ = v___y_3027_;
goto v___jp_3029_;
}
}
}
}
v___jp_3093_:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Lean_Syntax_getTailPos_x3f(v___y_3097_, v___y_3099_);
lean_dec(v___y_3097_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_inc(v___y_3100_);
v___y_3067_ = v___y_3095_;
v___y_3068_ = v___y_3096_;
v___y_3069_ = v___y_3100_;
v___y_3070_ = v___y_3094_;
v___y_3071_ = v___y_3095_;
v___y_3072_ = v___y_3099_;
v___y_3073_ = v___y_3098_;
v___y_3074_ = v___y_3100_;
goto v___jp_3066_;
}
else
{
lean_object* v_val_3102_; 
v_val_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_val_3102_);
lean_dec_ref_known(v___x_3101_, 1);
v___y_3067_ = v___y_3095_;
v___y_3068_ = v___y_3096_;
v___y_3069_ = v___y_3100_;
v___y_3070_ = v___y_3094_;
v___y_3071_ = v___y_3095_;
v___y_3072_ = v___y_3099_;
v___y_3073_ = v___y_3098_;
v___y_3074_ = v_val_3102_;
goto v___jp_3066_;
}
}
v___jp_3103_:
{
lean_object* v_toCold_3107_; lean_object* v_ref_3108_; uint8_t v_suppressElabErrors_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___f_3112_; lean_object* v_ref_3113_; lean_object* v___x_3114_; 
v_toCold_3107_ = lean_ctor_get(v___y_3026_, 0);
v_ref_3108_ = lean_ctor_get(v___y_3026_, 2);
v_suppressElabErrors_3109_ = lean_ctor_get_uint8(v___y_3026_, sizeof(void*)*3 + 2);
v___x_3110_ = lean_box(v_suppressElabErrors_3109_);
v___x_3111_ = lean_box(v___y_3104_);
v___f_3112_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3112_, 0, v___x_3110_);
lean_closure_set(v___f_3112_, 1, v___x_3111_);
v_ref_3113_ = l_Lean_replaceRef(v_ref_3020_, v_ref_3108_);
v___x_3114_ = l_Lean_Syntax_getPos_x3f(v_ref_3113_, v___y_3105_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v___x_3115_; 
v___x_3115_ = lean_unsigned_to_nat(0u);
v___y_3094_ = v_suppressElabErrors_3109_;
v___y_3095_ = v_toCold_3107_;
v___y_3096_ = v___f_3112_;
v___y_3097_ = v_ref_3113_;
v___y_3098_ = v___y_3106_;
v___y_3099_ = v___y_3105_;
v___y_3100_ = v___x_3115_;
goto v___jp_3093_;
}
else
{
lean_object* v_val_3116_; 
v_val_3116_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_val_3116_);
lean_dec_ref_known(v___x_3114_, 1);
v___y_3094_ = v_suppressElabErrors_3109_;
v___y_3095_ = v_toCold_3107_;
v___y_3096_ = v___f_3112_;
v___y_3097_ = v_ref_3113_;
v___y_3098_ = v___y_3106_;
v___y_3099_ = v___y_3105_;
v___y_3100_ = v_val_3116_;
goto v___jp_3093_;
}
}
v___jp_3118_:
{
if (v___y_3121_ == 0)
{
v___y_3104_ = v___y_3119_;
v___y_3105_ = v___y_3120_;
v___y_3106_ = v_severity_3022_;
goto v___jp_3103_;
}
else
{
v___y_3104_ = v___y_3119_;
v___y_3105_ = v___y_3120_;
v___y_3106_ = v___x_3117_;
goto v___jp_3103_;
}
}
v___jp_3122_:
{
if (v___y_3123_ == 0)
{
uint8_t v___x_3124_; uint8_t v___x_3125_; 
v___x_3124_ = 1;
v___x_3125_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3022_, v___x_3124_);
if (v___x_3125_ == 0)
{
v___y_3119_ = v___y_3123_;
v___y_3120_ = v___y_3123_;
v___y_3121_ = v___x_3125_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3126_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3026_);
v___x_3127_ = l_Lean_warningAsError;
v___x_3128_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3126_, v___x_3127_);
lean_dec_ref(v___x_3126_);
v___y_3119_ = v___y_3123_;
v___y_3120_ = v___y_3123_;
v___y_3121_ = v___x_3128_;
goto v___jp_3118_;
}
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_dec_ref(v_msgData_3021_);
v___x_3129_ = lean_box(0);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
return v___x_3130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_3133_, lean_object* v_msgData_3134_, lean_object* v_severity_3135_, lean_object* v_isSilent_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
uint8_t v_severity_boxed_3142_; uint8_t v_isSilent_boxed_3143_; lean_object* v_res_3144_; 
v_severity_boxed_3142_ = lean_unbox(v_severity_3135_);
v_isSilent_boxed_3143_ = lean_unbox(v_isSilent_3136_);
v_res_3144_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3133_, v_msgData_3134_, v_severity_boxed_3142_, v_isSilent_boxed_3143_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v_ref_3133_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_3145_, uint8_t v_severity_3146_, uint8_t v_isSilent_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_ref_3155_; lean_object* v___x_3156_; 
v_ref_3155_ = lean_ctor_get(v___y_3152_, 2);
v___x_3156_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3155_, v_msgData_3145_, v_severity_3146_, v_isSilent_3147_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_3157_, lean_object* v_severity_3158_, lean_object* v_isSilent_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
uint8_t v_severity_boxed_3167_; uint8_t v_isSilent_boxed_3168_; lean_object* v_res_3169_; 
v_severity_boxed_3167_ = lean_unbox(v_severity_3158_);
v_isSilent_boxed_3168_ = lean_unbox(v_isSilent_3159_);
v_res_3169_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3157_, v_severity_boxed_3167_, v_isSilent_boxed_3168_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
uint8_t v___x_3178_; uint8_t v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = 1;
v___x_3179_ = 0;
v___x_3180_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3170_, v___x_3178_, v___x_3179_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v___x_3193_; uint8_t v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3193_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3191_);
v___x_3194_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3193_, v_opt_3190_);
lean_dec_ref(v___x_3193_);
v___x_3195_ = lean_box(v___x_3194_);
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3197_, v___y_3198_);
lean_dec_ref(v___y_3198_);
lean_dec_ref(v_opt_3197_);
return v_res_3200_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3203_ = l_Lean_stringToMessageData(v___x_3202_);
return v___x_3203_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3206_ = l_Lean_stringToMessageData(v___x_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v___x_3215_; lean_object* v_env_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3238_; 
v___x_3215_ = lean_st_ref_get(v___y_3213_);
v_env_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc_ref(v_env_3216_);
lean_dec(v___x_3215_);
v___x_3217_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3218_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3217_, v___y_3212_);
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3238_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3238_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
uint8_t v_isExporting_3228_; 
v_isExporting_3228_ = lean_ctor_get_uint8(v_env_3216_, sizeof(void*)*13);
lean_dec_ref(v_env_3216_);
if (v_isExporting_3228_ == 0)
{
lean_dec(v_a_3219_);
lean_dec(v_id_3207_);
goto v___jp_3223_;
}
else
{
uint8_t v___x_3229_; 
v___x_3229_ = l_Lean_isPrivateName(v_id_3207_);
if (v___x_3229_ == 0)
{
lean_dec(v_a_3219_);
lean_dec(v_id_3207_);
goto v___jp_3223_;
}
else
{
uint8_t v___x_3230_; 
v___x_3230_ = lean_unbox(v_a_3219_);
lean_dec(v_a_3219_);
if (v___x_3230_ == 0)
{
lean_dec(v_id_3207_);
goto v___jp_3223_;
}
else
{
lean_object* v___x_3231_; uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_del_object(v___x_3221_);
v___x_3231_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3232_ = 0;
v___x_3233_ = l_Lean_MessageData_ofConstName(v_id_3207_, v___x_3232_);
v___x_3234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3231_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3234_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3236_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
return v___x_3237_;
}
}
}
v___jp_3223_:
{
lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3224_ = lean_box(0);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v___x_3224_);
v___x_3226_ = v___x_3221_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
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
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3248_, uint8_t v_enableLog_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v___x_3257_; lean_object* v_toCold_3258_; lean_object* v_env_3259_; lean_object* v_currNamespace_3260_; lean_object* v_openDecls_3261_; lean_object* v___x_3262_; lean_object* v_res_3263_; lean_object* v___x_3264_; 
v___x_3257_ = lean_st_ref_get(v___y_3255_);
v_toCold_3258_ = lean_ctor_get(v___y_3254_, 0);
v_env_3259_ = lean_ctor_get(v___x_3257_, 0);
lean_inc_ref(v_env_3259_);
lean_dec(v___x_3257_);
v_currNamespace_3260_ = lean_ctor_get(v_toCold_3258_, 4);
v_openDecls_3261_ = lean_ctor_get(v_toCold_3258_, 5);
v___x_3262_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3254_);
lean_inc(v_openDecls_3261_);
lean_inc(v_currNamespace_3260_);
v_res_3263_ = l_Lean_ResolveName_resolveGlobalName(v_env_3259_, v___x_3262_, v_currNamespace_3260_, v_openDecls_3261_, v_id_3248_);
lean_dec_ref(v___x_3262_);
v___x_3264_ = lean_st_ref_get(v___y_3255_);
if (v_enableLog_3249_ == 0)
{
lean_object* v___x_3265_; 
lean_dec(v___x_3264_);
v___x_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3265_, 0, v_res_3263_);
return v___x_3265_;
}
else
{
lean_object* v_env_3266_; uint8_t v_isExporting_3267_; 
v_env_3266_ = lean_ctor_get(v___x_3264_, 0);
lean_inc_ref(v_env_3266_);
lean_dec(v___x_3264_);
v_isExporting_3267_ = lean_ctor_get_uint8(v_env_3266_, sizeof(void*)*13);
lean_dec_ref(v_env_3266_);
if (v_isExporting_3267_ == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v_res_3263_);
return v___x_3268_;
}
else
{
lean_object* v___x_3269_; 
v___x_3269_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3263_);
if (lean_obj_tag(v___x_3269_) == 1)
{
lean_object* v_val_3270_; lean_object* v_fst_3271_; lean_object* v___x_3272_; 
v_val_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_val_3270_);
lean_dec_ref_known(v___x_3269_, 1);
v_fst_3271_ = lean_ctor_get(v_val_3270_, 0);
lean_inc(v_fst_3271_);
lean_dec(v_val_3270_);
v___x_3272_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3271_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; 
v_unused_3280_ = lean_ctor_get(v___x_3272_, 0);
lean_dec(v_unused_3280_);
v___x_3274_ = v___x_3272_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_dec(v___x_3272_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v_res_3263_);
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_res_3263_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec(v_res_3263_);
v_a_3281_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3272_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3272_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
else
{
lean_object* v___x_3289_; 
lean_dec(v___x_3269_);
v___x_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3289_, 0, v_res_3263_);
return v___x_3289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3290_, lean_object* v_enableLog_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
uint8_t v_enableLog_boxed_3299_; lean_object* v_res_3300_; 
v_enableLog_boxed_3299_ = lean_unbox(v_enableLog_3291_);
v_res_3300_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3290_, v_enableLog_boxed_3299_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3301_, lean_object* v_a_3302_){
_start:
{
if (lean_obj_tag(v_a_3301_) == 0)
{
lean_object* v___x_3303_; 
v___x_3303_ = l_List_reverse___redArg(v_a_3302_);
return v___x_3303_;
}
else
{
lean_object* v_head_3304_; lean_object* v_tail_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3316_; 
v_head_3304_ = lean_ctor_get(v_a_3301_, 0);
v_tail_3305_ = lean_ctor_get(v_a_3301_, 1);
v_isSharedCheck_3316_ = !lean_is_exclusive(v_a_3301_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3307_ = v_a_3301_;
v_isShared_3308_ = v_isSharedCheck_3316_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_tail_3305_);
lean_inc(v_head_3304_);
lean_dec(v_a_3301_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3316_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v_snd_3309_; uint8_t v___x_3310_; 
v_snd_3309_ = lean_ctor_get(v_head_3304_, 1);
v___x_3310_ = l_List_isEmpty___redArg(v_snd_3309_);
if (v___x_3310_ == 0)
{
lean_del_object(v___x_3307_);
lean_dec(v_head_3304_);
v_a_3301_ = v_tail_3305_;
goto _start;
}
else
{
lean_object* v___x_3313_; 
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 1, v_a_3302_);
v___x_3313_ = v___x_3307_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_head_3304_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_a_3302_);
v___x_3313_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
v_a_3301_ = v_tail_3305_;
v_a_3302_ = v___x_3313_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3317_, lean_object* v_findLocalDecl_x3f_3318_, lean_object* v_n_3319_, lean_object* v_projs_3320_, uint8_t v_globalDeclFound_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v___y_3330_; lean_object* v___y_3331_; uint8_t v_globalDeclFoundNext_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v_imported_3341_; lean_object* v_ctx_3342_; lean_object* v_scopes_3343_; lean_object* v_givenNameView_3344_; uint8_t v___y_3346_; 
v_imported_3341_ = lean_ctor_get(v_view_3317_, 1);
v_ctx_3342_ = lean_ctor_get(v_view_3317_, 2);
v_scopes_3343_ = lean_ctor_get(v_view_3317_, 3);
lean_inc(v_scopes_3343_);
lean_inc(v_ctx_3342_);
lean_inc(v_imported_3341_);
lean_inc(v_n_3319_);
v_givenNameView_3344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3344_, 0, v_n_3319_);
lean_ctor_set(v_givenNameView_3344_, 1, v_imported_3341_);
lean_ctor_set(v_givenNameView_3344_, 2, v_ctx_3342_);
lean_ctor_set(v_givenNameView_3344_, 3, v_scopes_3343_);
if (v_globalDeclFound_3321_ == 0)
{
v___y_3346_ = v_globalDeclFound_3321_;
goto v___jp_3345_;
}
else
{
uint8_t v___x_3381_; 
v___x_3381_ = l_List_isEmpty___redArg(v_projs_3320_);
if (v___x_3381_ == 0)
{
v___y_3346_ = v_globalDeclFound_3321_;
goto v___jp_3345_;
}
else
{
uint8_t v___x_3382_; 
v___x_3382_ = 0;
v___y_3346_ = v___x_3382_;
goto v___jp_3345_;
}
}
v___jp_3329_:
{
lean_object* v___x_3339_; 
v___x_3339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___y_3330_);
lean_ctor_set(v___x_3339_, 1, v_projs_3320_);
v_n_3319_ = v___y_3331_;
v_projs_3320_ = v___x_3339_;
v_globalDeclFound_3321_ = v_globalDeclFoundNext_3332_;
v___y_3322_ = v___y_3333_;
v___y_3323_ = v___y_3334_;
v___y_3324_ = v___y_3335_;
v___y_3325_ = v___y_3336_;
v___y_3326_ = v___y_3337_;
v___y_3327_ = v___y_3338_;
goto _start;
}
v___jp_3345_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = lean_box(v___y_3346_);
lean_inc_ref(v_findLocalDecl_x3f_3318_);
lean_inc_ref(v_givenNameView_3344_);
v___x_3348_ = lean_apply_2(v_findLocalDecl_x3f_3318_, v_givenNameView_3344_, v___x_3347_);
if (lean_obj_tag(v___x_3348_) == 0)
{
if (lean_obj_tag(v_n_3319_) == 1)
{
if (v_globalDeclFound_3321_ == 0)
{
lean_object* v_pre_3349_; lean_object* v_str_3350_; uint8_t v_globalDeclFoundNext_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v_pre_3349_ = lean_ctor_get(v_n_3319_, 0);
lean_inc(v_pre_3349_);
v_str_3350_ = lean_ctor_get(v_n_3319_, 1);
lean_inc_ref(v_str_3350_);
lean_dec_ref_known(v_n_3319_, 2);
v_globalDeclFoundNext_3351_ = 1;
v___x_3352_ = l_Lean_MacroScopesView_review(v_givenNameView_3344_);
v___x_3353_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3352_, v_globalDeclFound_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3355_; lean_object* v_r_3356_; uint8_t v___x_3357_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3353_, 1);
v___x_3355_ = lean_box(0);
v_r_3356_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3354_, v___x_3355_);
v___x_3357_ = l_List_isEmpty___redArg(v_r_3356_);
lean_dec(v_r_3356_);
if (v___x_3357_ == 0)
{
v___y_3330_ = v_str_3350_;
v___y_3331_ = v_pre_3349_;
v_globalDeclFoundNext_3332_ = v_globalDeclFoundNext_3351_;
v___y_3333_ = v___y_3322_;
v___y_3334_ = v___y_3323_;
v___y_3335_ = v___y_3324_;
v___y_3336_ = v___y_3325_;
v___y_3337_ = v___y_3326_;
v___y_3338_ = v___y_3327_;
goto v___jp_3329_;
}
else
{
v___y_3330_ = v_str_3350_;
v___y_3331_ = v_pre_3349_;
v_globalDeclFoundNext_3332_ = v_globalDeclFound_3321_;
v___y_3333_ = v___y_3322_;
v___y_3334_ = v___y_3323_;
v___y_3335_ = v___y_3324_;
v___y_3336_ = v___y_3325_;
v___y_3337_ = v___y_3326_;
v___y_3338_ = v___y_3327_;
goto v___jp_3329_;
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec_ref(v_str_3350_);
lean_dec(v_pre_3349_);
lean_dec(v_projs_3320_);
lean_dec_ref(v_findLocalDecl_x3f_3318_);
v_a_3358_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3353_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3353_);
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
else
{
lean_object* v_pre_3366_; lean_object* v_str_3367_; 
lean_dec_ref_known(v_givenNameView_3344_, 4);
v_pre_3366_ = lean_ctor_get(v_n_3319_, 0);
lean_inc(v_pre_3366_);
v_str_3367_ = lean_ctor_get(v_n_3319_, 1);
lean_inc_ref(v_str_3367_);
lean_dec_ref_known(v_n_3319_, 2);
v___y_3330_ = v_str_3367_;
v___y_3331_ = v_pre_3366_;
v_globalDeclFoundNext_3332_ = v_globalDeclFound_3321_;
v___y_3333_ = v___y_3322_;
v___y_3334_ = v___y_3323_;
v___y_3335_ = v___y_3324_;
v___y_3336_ = v___y_3325_;
v___y_3337_ = v___y_3326_;
v___y_3338_ = v___y_3327_;
goto v___jp_3329_;
}
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_dec_ref_known(v_givenNameView_3344_, 4);
lean_dec(v_projs_3320_);
lean_dec(v_n_3319_);
lean_dec_ref(v_findLocalDecl_x3f_3318_);
v___x_3368_ = lean_box(0);
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
return v___x_3369_;
}
}
else
{
lean_object* v_val_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3380_; 
lean_dec_ref_known(v_givenNameView_3344_, 4);
lean_dec(v_n_3319_);
lean_dec_ref(v_findLocalDecl_x3f_3318_);
v_val_3370_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3372_ = v___x_3348_;
v_isShared_3373_ = v_isSharedCheck_3380_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_val_3370_);
lean_dec(v___x_3348_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3380_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3374_ = l_Lean_LocalDecl_toExpr(v_val_3370_);
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
lean_ctor_set(v___x_3375_, 1, v_projs_3320_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3375_);
v___x_3377_ = v___x_3372_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
return v___x_3378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3383_, lean_object* v_findLocalDecl_x3f_3384_, lean_object* v_n_3385_, lean_object* v_projs_3386_, lean_object* v_globalDeclFound_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
uint8_t v_globalDeclFound_boxed_3395_; lean_object* v_res_3396_; 
v_globalDeclFound_boxed_3395_ = lean_unbox(v_globalDeclFound_3387_);
v_res_3396_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3383_, v_findLocalDecl_x3f_3384_, v_n_3385_, v_projs_3386_, v_globalDeclFound_boxed_3395_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec_ref(v_view_3383_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3397_, lean_object* v_givenName_3398_, lean_object* v_as_3399_, lean_object* v_i_3400_){
_start:
{
lean_object* v_zero_3401_; uint8_t v_isZero_3402_; 
v_zero_3401_ = lean_unsigned_to_nat(0u);
v_isZero_3402_ = lean_nat_dec_eq(v_i_3400_, v_zero_3401_);
if (v_isZero_3402_ == 1)
{
lean_object* v___x_3403_; 
lean_dec(v_i_3400_);
v___x_3403_ = lean_box(0);
return v___x_3403_;
}
else
{
lean_object* v_one_3404_; lean_object* v_n_3405_; lean_object* v___y_3407_; lean_object* v___x_3409_; 
v_one_3404_ = lean_unsigned_to_nat(1u);
v_n_3405_ = lean_nat_sub(v_i_3400_, v_one_3404_);
lean_dec(v_i_3400_);
v___x_3409_ = lean_array_fget_borrowed(v_as_3399_, v_n_3405_);
if (lean_obj_tag(v___x_3409_) == 0)
{
v___y_3407_ = v___x_3409_;
goto v___jp_3406_;
}
else
{
lean_object* v_val_3410_; uint8_t v___x_3411_; 
v_val_3410_ = lean_ctor_get(v___x_3409_, 0);
v___x_3411_ = l_Lean_LocalDecl_isAuxDecl(v_val_3410_);
if (v___x_3411_ == 0)
{
v___y_3407_ = v_localDecl_x3f_3397_;
goto v___jp_3406_;
}
else
{
lean_object* v___x_3412_; uint8_t v___x_3413_; 
v___x_3412_ = l_Lean_LocalDecl_userName(v_val_3410_);
v___x_3413_ = lean_name_eq(v___x_3412_, v_givenName_3398_);
lean_dec(v___x_3412_);
if (v___x_3413_ == 0)
{
v_i_3400_ = v_n_3405_;
goto _start;
}
else
{
v___y_3407_ = v___x_3409_;
goto v___jp_3406_;
}
}
}
v___jp_3406_:
{
if (lean_obj_tag(v___y_3407_) == 0)
{
v_i_3400_ = v_n_3405_;
goto _start;
}
else
{
lean_dec(v_n_3405_);
lean_inc_ref(v___y_3407_);
return v___y_3407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3415_, lean_object* v_givenName_3416_, lean_object* v_as_3417_, lean_object* v_i_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3415_, v_givenName_3416_, v_as_3417_, v_i_3418_);
lean_dec_ref(v_as_3417_);
lean_dec(v_givenName_3416_);
lean_dec(v_localDecl_x3f_3415_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3420_, lean_object* v_givenName_3421_, lean_object* v_as_3422_, lean_object* v_i_3423_){
_start:
{
lean_object* v_zero_3424_; uint8_t v_isZero_3425_; 
v_zero_3424_ = lean_unsigned_to_nat(0u);
v_isZero_3425_ = lean_nat_dec_eq(v_i_3423_, v_zero_3424_);
if (v_isZero_3425_ == 1)
{
lean_object* v___x_3426_; 
lean_dec(v_i_3423_);
v___x_3426_ = lean_box(0);
return v___x_3426_;
}
else
{
lean_object* v_one_3427_; lean_object* v_n_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_one_3427_ = lean_unsigned_to_nat(1u);
v_n_3428_ = lean_nat_sub(v_i_3423_, v_one_3427_);
lean_dec(v_i_3423_);
v___x_3429_ = lean_array_fget_borrowed(v_as_3422_, v_n_3428_);
v___x_3430_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3420_, v_givenName_3421_, v___x_3429_);
if (lean_obj_tag(v___x_3430_) == 0)
{
v_i_3423_ = v_n_3428_;
goto _start;
}
else
{
lean_dec(v_n_3428_);
return v___x_3430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3432_, lean_object* v_givenName_3433_, lean_object* v_x_3434_){
_start:
{
if (lean_obj_tag(v_x_3434_) == 0)
{
lean_object* v_cs_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v_cs_3435_ = lean_ctor_get(v_x_3434_, 0);
v___x_3436_ = lean_array_get_size(v_cs_3435_);
v___x_3437_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3432_, v_givenName_3433_, v_cs_3435_, v___x_3436_);
return v___x_3437_;
}
else
{
lean_object* v_vs_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v_vs_3438_ = lean_ctor_get(v_x_3434_, 0);
v___x_3439_ = lean_array_get_size(v_vs_3438_);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3432_, v_givenName_3433_, v_vs_3438_, v___x_3439_);
return v___x_3440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3441_, lean_object* v_givenName_3442_, lean_object* v_x_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3441_, v_givenName_3442_, v_x_3443_);
lean_dec_ref(v_x_3443_);
lean_dec(v_givenName_3442_);
lean_dec(v_localDecl_x3f_3441_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3445_, lean_object* v_givenName_3446_, lean_object* v_as_3447_, lean_object* v_i_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3445_, v_givenName_3446_, v_as_3447_, v_i_3448_);
lean_dec_ref(v_as_3447_);
lean_dec(v_givenName_3446_);
lean_dec(v_localDecl_x3f_3445_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3450_, lean_object* v_givenName_3451_, lean_object* v_t_3452_){
_start:
{
lean_object* v_root_3453_; lean_object* v_tail_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_root_3453_ = lean_ctor_get(v_t_3452_, 0);
v_tail_3454_ = lean_ctor_get(v_t_3452_, 1);
v___x_3455_ = lean_array_get_size(v_tail_3454_);
v___x_3456_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3450_, v_givenName_3451_, v_tail_3454_, v___x_3455_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3450_, v_givenName_3451_, v_root_3453_);
return v___x_3457_;
}
else
{
return v___x_3456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3458_, lean_object* v_givenName_3459_, lean_object* v_t_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3458_, v_givenName_3459_, v_t_3460_);
lean_dec_ref(v_t_3460_);
lean_dec(v_givenName_3459_);
lean_dec(v_localDecl_x3f_3458_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3462_, lean_object* v_k_3463_){
_start:
{
if (lean_obj_tag(v_t_3462_) == 0)
{
lean_object* v_k_3464_; lean_object* v_v_3465_; lean_object* v_l_3466_; lean_object* v_r_3467_; uint8_t v___x_3468_; 
v_k_3464_ = lean_ctor_get(v_t_3462_, 1);
v_v_3465_ = lean_ctor_get(v_t_3462_, 2);
v_l_3466_ = lean_ctor_get(v_t_3462_, 3);
v_r_3467_ = lean_ctor_get(v_t_3462_, 4);
v___x_3468_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3463_, v_k_3464_);
switch(v___x_3468_)
{
case 0:
{
v_t_3462_ = v_l_3466_;
goto _start;
}
case 1:
{
lean_object* v___x_3470_; 
lean_inc(v_v_3465_);
v___x_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3470_, 0, v_v_3465_);
return v___x_3470_;
}
default: 
{
v_t_3462_ = v_r_3467_;
goto _start;
}
}
}
else
{
lean_object* v___x_3472_; 
v___x_3472_ = lean_box(0);
return v___x_3472_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3473_, lean_object* v_k_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3473_, v_k_3474_);
lean_dec(v_k_3474_);
lean_dec(v_t_3473_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3476_, lean_object* v_givenName_3477_){
_start:
{
lean_object* v___x_3478_; uint8_t v___x_3479_; 
v___x_3478_ = l_Lean_LocalDecl_userName(v_localDecl_3476_);
v___x_3479_ = lean_name_eq(v___x_3478_, v_givenName_3477_);
lean_dec(v___x_3478_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; 
lean_dec_ref(v_localDecl_3476_);
v___x_3480_ = lean_box(0);
return v___x_3480_;
}
else
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3481_, 0, v_localDecl_3476_);
return v___x_3481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3482_, lean_object* v_givenName_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3482_, v_givenName_3483_);
lean_dec(v_givenName_3483_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3485_, uint8_t v_skipAuxDecl_3486_, lean_object* v_auxDeclToFullName_3487_, lean_object* v___x_3488_, lean_object* v_givenNameView_3489_, lean_object* v_as_3490_, lean_object* v_i_3491_){
_start:
{
lean_object* v_zero_3492_; uint8_t v_isZero_3493_; 
v_zero_3492_ = lean_unsigned_to_nat(0u);
v_isZero_3493_ = lean_nat_dec_eq(v_i_3491_, v_zero_3492_);
if (v_isZero_3493_ == 1)
{
lean_object* v___x_3494_; 
lean_dec(v_i_3491_);
lean_dec_ref(v_givenNameView_3489_);
lean_dec(v___x_3488_);
v___x_3494_ = lean_box(0);
return v___x_3494_;
}
else
{
lean_object* v_one_3495_; lean_object* v_n_3496_; lean_object* v___y_3498_; lean_object* v___x_3500_; 
v_one_3495_ = lean_unsigned_to_nat(1u);
v_n_3496_ = lean_nat_sub(v_i_3491_, v_one_3495_);
lean_dec(v_i_3491_);
v___x_3500_ = lean_array_fget_borrowed(v_as_3490_, v_n_3496_);
if (lean_obj_tag(v___x_3500_) == 0)
{
v___y_3498_ = v___x_3500_;
goto v___jp_3497_;
}
else
{
lean_object* v_val_3501_; uint8_t v___x_3502_; 
v_val_3501_ = lean_ctor_get(v___x_3500_, 0);
v___x_3502_ = l_Lean_LocalDecl_isAuxDecl(v_val_3501_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; 
lean_inc(v_val_3501_);
v___x_3503_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3501_, v_givenName_3485_);
v___y_3498_ = v___x_3503_;
goto v___jp_3497_;
}
else
{
if (v_skipAuxDecl_3486_ == 0)
{
if (v___x_3502_ == 0)
{
v_i_3491_ = v_n_3496_;
goto _start;
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = l_Lean_LocalDecl_fvarId(v_val_3501_);
v___x_3506_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3487_, v___x_3505_);
lean_dec(v___x_3505_);
if (lean_obj_tag(v___x_3506_) == 1)
{
lean_object* v_val_3507_; lean_object* v_fullDeclView_3508_; lean_object* v___y_3510_; lean_object* v_name_3531_; lean_object* v___x_3532_; 
v_val_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_val_3507_);
lean_dec_ref_known(v___x_3506_, 1);
v_fullDeclView_3508_ = l_Lean_extractMacroScopes(v_val_3507_);
v_name_3531_ = lean_ctor_get(v_fullDeclView_3508_, 0);
lean_inc(v_name_3531_);
v___x_3532_ = l_Lean_privateToUserName_x3f(v_name_3531_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_inc(v_name_3531_);
v___y_3510_ = v_name_3531_;
goto v___jp_3509_;
}
else
{
lean_object* v_val_3533_; 
v_val_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_val_3533_);
lean_dec_ref_known(v___x_3532_, 1);
v___y_3510_ = v_val_3533_;
goto v___jp_3509_;
}
v___jp_3509_:
{
lean_object* v_imported_3511_; lean_object* v_ctx_3512_; lean_object* v_scopes_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3529_; 
v_imported_3511_ = lean_ctor_get(v_fullDeclView_3508_, 1);
v_ctx_3512_ = lean_ctor_get(v_fullDeclView_3508_, 2);
v_scopes_3513_ = lean_ctor_get(v_fullDeclView_3508_, 3);
v_isSharedCheck_3529_ = !lean_is_exclusive(v_fullDeclView_3508_);
if (v_isSharedCheck_3529_ == 0)
{
lean_object* v_unused_3530_; 
v_unused_3530_ = lean_ctor_get(v_fullDeclView_3508_, 0);
lean_dec(v_unused_3530_);
v___x_3515_ = v_fullDeclView_3508_;
v_isShared_3516_ = v_isSharedCheck_3529_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_scopes_3513_);
lean_inc(v_ctx_3512_);
lean_inc(v_imported_3511_);
lean_dec(v_fullDeclView_3508_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3529_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v_fullDeclView_3518_; 
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___y_3510_);
v_fullDeclView_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___y_3510_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_imported_3511_);
lean_ctor_set(v_reuseFailAlloc_3528_, 2, v_ctx_3512_);
lean_ctor_set(v_reuseFailAlloc_3528_, 3, v_scopes_3513_);
v_fullDeclView_3518_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v_fullDeclName_3519_; uint8_t v___x_3520_; 
lean_inc_ref(v_fullDeclView_3518_);
v_fullDeclName_3519_ = l_Lean_MacroScopesView_review(v_fullDeclView_3518_);
v___x_3520_ = l_Lean_Name_isPrefixOf(v___x_3488_, v_fullDeclName_3519_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; 
lean_dec_ref(v_fullDeclView_3518_);
lean_inc(v___x_3488_);
lean_inc_ref(v_givenNameView_3489_);
lean_inc(v_val_3501_);
v___x_3521_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3501_, v_givenNameView_3489_, v_fullDeclName_3519_, v___x_3488_);
lean_dec(v_fullDeclName_3519_);
v___y_3498_ = v___x_3521_;
goto v___jp_3497_;
}
else
{
lean_object* v___x_3522_; lean_object* v_localDeclNameView_3523_; uint8_t v___x_3524_; 
lean_dec(v_fullDeclName_3519_);
v___x_3522_ = l_Lean_LocalDecl_userName(v_val_3501_);
v_localDeclNameView_3523_ = l_Lean_extractMacroScopes(v___x_3522_);
v___x_3524_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3523_, v_givenNameView_3489_);
lean_dec_ref(v_localDeclNameView_3523_);
if (v___x_3524_ == 0)
{
lean_dec_ref(v_fullDeclView_3518_);
v_i_3491_ = v_n_3496_;
goto _start;
}
else
{
uint8_t v___x_3526_; 
v___x_3526_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3489_, v_fullDeclView_3518_);
lean_dec_ref(v_fullDeclView_3518_);
if (v___x_3526_ == 0)
{
v_i_3491_ = v_n_3496_;
goto _start;
}
else
{
lean_inc_ref(v___x_3500_);
v___y_3498_ = v___x_3500_;
goto v___jp_3497_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3534_; 
lean_dec(v___x_3506_);
lean_inc(v_val_3501_);
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3501_, v_givenName_3485_);
v___y_3498_ = v___x_3534_;
goto v___jp_3497_;
}
}
}
else
{
v_i_3491_ = v_n_3496_;
goto _start;
}
}
}
v___jp_3497_:
{
if (lean_obj_tag(v___y_3498_) == 0)
{
v_i_3491_ = v_n_3496_;
goto _start;
}
else
{
lean_dec(v_n_3496_);
lean_dec_ref(v_givenNameView_3489_);
lean_dec(v___x_3488_);
return v___y_3498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3536_, lean_object* v_skipAuxDecl_3537_, lean_object* v_auxDeclToFullName_3538_, lean_object* v___x_3539_, lean_object* v_givenNameView_3540_, lean_object* v_as_3541_, lean_object* v_i_3542_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3543_; lean_object* v_res_3544_; 
v_skipAuxDecl_boxed_3543_ = lean_unbox(v_skipAuxDecl_3537_);
v_res_3544_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3536_, v_skipAuxDecl_boxed_3543_, v_auxDeclToFullName_3538_, v___x_3539_, v_givenNameView_3540_, v_as_3541_, v_i_3542_);
lean_dec_ref(v_as_3541_);
lean_dec(v_auxDeclToFullName_3538_);
lean_dec(v_givenName_3536_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3545_, uint8_t v_skipAuxDecl_3546_, lean_object* v_auxDeclToFullName_3547_, lean_object* v___x_3548_, lean_object* v_givenNameView_3549_, lean_object* v_as_3550_, lean_object* v_i_3551_){
_start:
{
lean_object* v_zero_3552_; uint8_t v_isZero_3553_; 
v_zero_3552_ = lean_unsigned_to_nat(0u);
v_isZero_3553_ = lean_nat_dec_eq(v_i_3551_, v_zero_3552_);
if (v_isZero_3553_ == 1)
{
lean_object* v___x_3554_; 
lean_dec(v_i_3551_);
lean_dec_ref(v_givenNameView_3549_);
lean_dec(v___x_3548_);
v___x_3554_ = lean_box(0);
return v___x_3554_;
}
else
{
lean_object* v_one_3555_; lean_object* v_n_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_one_3555_ = lean_unsigned_to_nat(1u);
v_n_3556_ = lean_nat_sub(v_i_3551_, v_one_3555_);
lean_dec(v_i_3551_);
v___x_3557_ = lean_array_fget_borrowed(v_as_3550_, v_n_3556_);
lean_inc_ref(v_givenNameView_3549_);
lean_inc(v___x_3548_);
v___x_3558_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3545_, v_skipAuxDecl_3546_, v_auxDeclToFullName_3547_, v___x_3548_, v_givenNameView_3549_, v___x_3557_);
if (lean_obj_tag(v___x_3558_) == 0)
{
v_i_3551_ = v_n_3556_;
goto _start;
}
else
{
lean_dec(v_n_3556_);
lean_dec_ref(v_givenNameView_3549_);
lean_dec(v___x_3548_);
return v___x_3558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3560_, uint8_t v_skipAuxDecl_3561_, lean_object* v_auxDeclToFullName_3562_, lean_object* v___x_3563_, lean_object* v_givenNameView_3564_, lean_object* v_x_3565_){
_start:
{
if (lean_obj_tag(v_x_3565_) == 0)
{
lean_object* v_cs_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v_cs_3566_ = lean_ctor_get(v_x_3565_, 0);
v___x_3567_ = lean_array_get_size(v_cs_3566_);
v___x_3568_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3560_, v_skipAuxDecl_3561_, v_auxDeclToFullName_3562_, v___x_3563_, v_givenNameView_3564_, v_cs_3566_, v___x_3567_);
return v___x_3568_;
}
else
{
lean_object* v_vs_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v_vs_3569_ = lean_ctor_get(v_x_3565_, 0);
v___x_3570_ = lean_array_get_size(v_vs_3569_);
v___x_3571_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3560_, v_skipAuxDecl_3561_, v_auxDeclToFullName_3562_, v___x_3563_, v_givenNameView_3564_, v_vs_3569_, v___x_3570_);
return v___x_3571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3572_, lean_object* v_skipAuxDecl_3573_, lean_object* v_auxDeclToFullName_3574_, lean_object* v___x_3575_, lean_object* v_givenNameView_3576_, lean_object* v_x_3577_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3578_; lean_object* v_res_3579_; 
v_skipAuxDecl_boxed_3578_ = lean_unbox(v_skipAuxDecl_3573_);
v_res_3579_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3572_, v_skipAuxDecl_boxed_3578_, v_auxDeclToFullName_3574_, v___x_3575_, v_givenNameView_3576_, v_x_3577_);
lean_dec_ref(v_x_3577_);
lean_dec(v_auxDeclToFullName_3574_);
lean_dec(v_givenName_3572_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3580_, lean_object* v_skipAuxDecl_3581_, lean_object* v_auxDeclToFullName_3582_, lean_object* v___x_3583_, lean_object* v_givenNameView_3584_, lean_object* v_as_3585_, lean_object* v_i_3586_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3587_; lean_object* v_res_3588_; 
v_skipAuxDecl_boxed_3587_ = lean_unbox(v_skipAuxDecl_3581_);
v_res_3588_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3580_, v_skipAuxDecl_boxed_3587_, v_auxDeclToFullName_3582_, v___x_3583_, v_givenNameView_3584_, v_as_3585_, v_i_3586_);
lean_dec_ref(v_as_3585_);
lean_dec(v_auxDeclToFullName_3582_);
lean_dec(v_givenName_3580_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3589_, uint8_t v_skipAuxDecl_3590_, lean_object* v_auxDeclToFullName_3591_, lean_object* v___x_3592_, lean_object* v_givenNameView_3593_, lean_object* v_t_3594_){
_start:
{
lean_object* v_root_3595_; lean_object* v_tail_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v_root_3595_ = lean_ctor_get(v_t_3594_, 0);
v_tail_3596_ = lean_ctor_get(v_t_3594_, 1);
v___x_3597_ = lean_array_get_size(v_tail_3596_);
lean_inc_ref(v_givenNameView_3593_);
lean_inc(v___x_3592_);
v___x_3598_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3589_, v_skipAuxDecl_3590_, v_auxDeclToFullName_3591_, v___x_3592_, v_givenNameView_3593_, v_tail_3596_, v___x_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v___x_3599_; 
v___x_3599_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3589_, v_skipAuxDecl_3590_, v_auxDeclToFullName_3591_, v___x_3592_, v_givenNameView_3593_, v_root_3595_);
return v___x_3599_;
}
else
{
lean_dec_ref(v_givenNameView_3593_);
lean_dec(v___x_3592_);
return v___x_3598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3600_, lean_object* v_skipAuxDecl_3601_, lean_object* v_auxDeclToFullName_3602_, lean_object* v___x_3603_, lean_object* v_givenNameView_3604_, lean_object* v_t_3605_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3606_; lean_object* v_res_3607_; 
v_skipAuxDecl_boxed_3606_ = lean_unbox(v_skipAuxDecl_3601_);
v_res_3607_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3600_, v_skipAuxDecl_boxed_3606_, v_auxDeclToFullName_3602_, v___x_3603_, v_givenNameView_3604_, v_t_3605_);
lean_dec_ref(v_t_3605_);
lean_dec(v_auxDeclToFullName_3602_);
lean_dec(v_givenName_3600_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3608_, lean_object* v_currNamespace_3609_, lean_object* v_decls_3610_, lean_object* v_givenNameView_3611_, uint8_t v_skipAuxDecl_3612_){
_start:
{
lean_object* v_givenName_3613_; lean_object* v_localDecl_x3f_3614_; 
lean_inc_ref(v_givenNameView_3611_);
v_givenName_3613_ = l_Lean_MacroScopesView_review(v_givenNameView_3611_);
v_localDecl_x3f_3614_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3613_, v_skipAuxDecl_3612_, v_auxDeclToFullName_3608_, v_currNamespace_3609_, v_givenNameView_3611_, v_decls_3610_);
if (lean_obj_tag(v_localDecl_x3f_3614_) == 0)
{
if (v_skipAuxDecl_3612_ == 0)
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3614_, v_givenName_3613_, v_decls_3610_);
lean_dec(v_givenName_3613_);
return v___x_3615_;
}
else
{
lean_dec(v_givenName_3613_);
return v_localDecl_x3f_3614_;
}
}
else
{
lean_dec(v_givenName_3613_);
return v_localDecl_x3f_3614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3616_, lean_object* v_currNamespace_3617_, lean_object* v_decls_3618_, lean_object* v_givenNameView_3619_, lean_object* v_skipAuxDecl_3620_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3621_; lean_object* v_res_3622_; 
v_skipAuxDecl_boxed_3621_ = lean_unbox(v_skipAuxDecl_3620_);
v_res_3622_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3616_, v_currNamespace_3617_, v_decls_3618_, v_givenNameView_3619_, v_skipAuxDecl_boxed_3621_);
lean_dec_ref(v_decls_3618_);
lean_dec(v_auxDeclToFullName_3616_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v_lctx_3631_; lean_object* v_toCold_3632_; lean_object* v_decls_3633_; lean_object* v_auxDeclToFullName_3634_; lean_object* v_currNamespace_3635_; lean_object* v_view_3636_; lean_object* v_name_3637_; lean_object* v_findLocalDecl_x3f_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; lean_object* v___x_3641_; 
v_lctx_3631_ = lean_ctor_get(v___y_3626_, 2);
v_toCold_3632_ = lean_ctor_get(v___y_3628_, 0);
v_decls_3633_ = lean_ctor_get(v_lctx_3631_, 1);
v_auxDeclToFullName_3634_ = lean_ctor_get(v_lctx_3631_, 2);
v_currNamespace_3635_ = lean_ctor_get(v_toCold_3632_, 4);
v_view_3636_ = l_Lean_extractMacroScopes(v_n_3623_);
v_name_3637_ = lean_ctor_get(v_view_3636_, 0);
lean_inc(v_name_3637_);
lean_inc_ref(v_decls_3633_);
lean_inc(v_currNamespace_3635_);
lean_inc(v_auxDeclToFullName_3634_);
v_findLocalDecl_x3f_3638_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3638_, 0, v_auxDeclToFullName_3634_);
lean_closure_set(v_findLocalDecl_x3f_3638_, 1, v_currNamespace_3635_);
lean_closure_set(v_findLocalDecl_x3f_3638_, 2, v_decls_3633_);
v___x_3639_ = lean_box(0);
v___x_3640_ = 0;
v___x_3641_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3636_, v_findLocalDecl_x3f_3638_, v_name_3637_, v___x_3639_, v___x_3640_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec_ref(v_view_3636_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3651_, lean_object* v_b_3652_){
_start:
{
if (lean_obj_tag(v_as_x27_3651_) == 0)
{
lean_object* v___x_3654_; 
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v_b_3652_);
return v___x_3654_;
}
else
{
lean_object* v_head_3655_; lean_object* v_tail_3656_; lean_object* v_config_3657_; lean_object* v_extensions_3658_; lean_object* v_extra_3659_; lean_object* v_extraInj_3660_; lean_object* v_extraFacts_3661_; lean_object* v_symPrios_3662_; lean_object* v_norm_3663_; lean_object* v_normProcs_3664_; lean_object* v_anchorRefs_x3f_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3674_; 
v_head_3655_ = lean_ctor_get(v_as_x27_3651_, 0);
v_tail_3656_ = lean_ctor_get(v_as_x27_3651_, 1);
v_config_3657_ = lean_ctor_get(v_b_3652_, 0);
v_extensions_3658_ = lean_ctor_get(v_b_3652_, 1);
v_extra_3659_ = lean_ctor_get(v_b_3652_, 2);
v_extraInj_3660_ = lean_ctor_get(v_b_3652_, 3);
v_extraFacts_3661_ = lean_ctor_get(v_b_3652_, 4);
v_symPrios_3662_ = lean_ctor_get(v_b_3652_, 5);
v_norm_3663_ = lean_ctor_get(v_b_3652_, 6);
v_normProcs_3664_ = lean_ctor_get(v_b_3652_, 7);
v_anchorRefs_x3f_3665_ = lean_ctor_get(v_b_3652_, 8);
v_isSharedCheck_3674_ = !lean_is_exclusive(v_b_3652_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3667_ = v_b_3652_;
v_isShared_3668_ = v_isSharedCheck_3674_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_anchorRefs_x3f_3665_);
lean_inc(v_normProcs_3664_);
lean_inc(v_norm_3663_);
lean_inc(v_symPrios_3662_);
lean_inc(v_extraFacts_3661_);
lean_inc(v_extraInj_3660_);
lean_inc(v_extra_3659_);
lean_inc(v_extensions_3658_);
lean_inc(v_config_3657_);
lean_dec(v_b_3652_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3674_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3669_; lean_object* v___x_3671_; 
lean_inc(v_head_3655_);
v___x_3669_ = l_Lean_PersistentArray_push___redArg(v_extra_3659_, v_head_3655_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 2, v___x_3669_);
v___x_3671_ = v___x_3667_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_config_3657_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_extensions_3658_);
lean_ctor_set(v_reuseFailAlloc_3673_, 2, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3673_, 3, v_extraInj_3660_);
lean_ctor_set(v_reuseFailAlloc_3673_, 4, v_extraFacts_3661_);
lean_ctor_set(v_reuseFailAlloc_3673_, 5, v_symPrios_3662_);
lean_ctor_set(v_reuseFailAlloc_3673_, 6, v_norm_3663_);
lean_ctor_set(v_reuseFailAlloc_3673_, 7, v_normProcs_3664_);
lean_ctor_set(v_reuseFailAlloc_3673_, 8, v_anchorRefs_x3f_3665_);
v___x_3671_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
v_as_x27_3651_ = v_tail_3656_;
v_b_3652_ = v___x_3671_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3675_, lean_object* v_b_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3675_, v_b_3676_);
lean_dec(v_as_x27_3675_);
return v_res_3678_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3681_ = l_Lean_stringToMessageData(v___x_3680_);
return v___x_3681_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3683_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3684_ = l_Lean_stringToMessageData(v___x_3683_);
return v___x_3684_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3686_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3687_ = l_Lean_stringToMessageData(v___x_3686_);
return v___x_3687_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3690_ = l_Lean_stringToMessageData(v___x_3689_);
return v___x_3690_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3693_ = l_Lean_stringToMessageData(v___x_3692_);
return v___x_3693_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3696_ = l_Lean_stringToMessageData(v___x_3695_);
return v___x_3696_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3699_ = l_Lean_stringToMessageData(v___x_3698_);
return v___x_3699_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3702_ = l_Lean_stringToMessageData(v___x_3701_);
return v___x_3702_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3705_ = l_Lean_stringToMessageData(v___x_3704_);
return v___x_3705_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3708_ = l_Lean_stringToMessageData(v___x_3707_);
return v___x_3708_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3711_ = l_Lean_stringToMessageData(v___x_3710_);
return v___x_3711_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23(void){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3713_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22));
v___x_3714_ = l_Lean_stringToMessageData(v___x_3713_);
return v___x_3714_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25(void){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24));
v___x_3717_ = l_Lean_stringToMessageData(v___x_3716_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3718_, lean_object* v_p_3719_, lean_object* v_mod_x3f_3720_, lean_object* v_id_3721_, uint8_t v_minIndexable_3722_, uint8_t v_only_3723_, uint8_t v_incremental_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
uint8_t v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; uint8_t v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v_a_3887_; lean_object* v___y_4112_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4123_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4124_ = lean_box(0);
lean_inc(v_id_3721_);
v___x_4125_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3721_, v___x_4124_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4126_);
lean_dec_ref_known(v___x_4125_, 1);
v_a_3887_ = v_a_4126_;
goto v___jp_3886_;
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4201_; 
v_a_4127_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4129_ = v___x_4125_;
v_isShared_4130_ = v_isSharedCheck_4201_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4125_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4201_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
uint8_t v___y_4132_; uint8_t v___x_4199_; 
v___x_4199_ = l_Lean_Exception_isInterrupt(v_a_4127_);
if (v___x_4199_ == 0)
{
uint8_t v___x_4200_; 
lean_inc(v_a_4127_);
v___x_4200_ = l_Lean_Exception_isRuntime(v_a_4127_);
v___y_4132_ = v___x_4200_;
goto v___jp_4131_;
}
else
{
v___y_4132_ = v___x_4199_;
goto v___jp_4131_;
}
v___jp_4131_:
{
if (v___y_4132_ == 0)
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
lean_del_object(v___x_4129_);
v___x_4133_ = l_Lean_TSyntax_getId(v_id_3721_);
lean_inc(v___x_4133_);
v___x_4134_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4133_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v___x_4134_, 1);
if (lean_obj_tag(v_a_4135_) == 0)
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_4133_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4165_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4139_ = v___x_4136_;
v_isShared_4140_ = v_isSharedCheck_4165_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4136_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4165_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
if (lean_obj_tag(v_a_4137_) == 1)
{
lean_del_object(v___x_4139_);
lean_dec(v_a_4127_);
if (lean_obj_tag(v_mod_x3f_3720_) == 1)
{
lean_object* v_val_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec_ref_known(v_a_4137_, 1);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v_val_4141_ = lean_ctor_get(v_mod_x3f_3720_, 0);
lean_inc(v_val_4141_);
lean_dec_ref_known(v_mod_x3f_3720_, 1);
v___x_4142_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4143_ = l_Lean_MessageData_ofName(v___x_4133_);
v___x_4144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4142_);
lean_ctor_set(v___x_4144_, 1, v___x_4143_);
v___x_4145_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4144_);
lean_ctor_set(v___x_4146_, 1, v___x_4145_);
v___x_4147_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4141_, v___x_4146_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
lean_dec(v_val_4141_);
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4147_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4147_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
else
{
lean_object* v_val_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_dec(v___x_4133_);
v_val_4156_ = lean_ctor_get(v_a_4137_, 0);
lean_inc(v_val_4156_);
lean_dec_ref_known(v_a_4137_, 1);
v___x_4157_ = lean_box(0);
lean_inc_ref(v_params_3718_);
v___x_4158_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3718_, v_val_4156_, v___x_4123_, v___y_4132_, v___x_4157_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
lean_dec(v_val_4156_);
v___y_4112_ = v___x_4158_;
goto v___jp_4111_;
}
}
else
{
lean_object* v___x_4159_; uint8_t v___x_4160_; 
lean_dec(v_a_4137_);
v___x_4159_ = l_Lean_Name_getPrefix(v___x_4133_);
lean_dec(v___x_4133_);
v___x_4160_ = l_Lean_Name_isAnonymous(v___x_4159_);
lean_dec(v___x_4159_);
if (v___x_4160_ == 0)
{
lean_object* v___x_4161_; 
lean_del_object(v___x_4139_);
lean_dec(v_a_4127_);
v___x_4161_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3718_, v_p_3719_, v_mod_x3f_3720_, v_id_3721_, v_minIndexable_3722_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
return v___x_4161_;
}
else
{
lean_object* v___x_4163_; 
lean_dec(v_id_3721_);
lean_dec(v_mod_x3f_3720_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set_tag(v___x_4139_, 1);
lean_ctor_set(v___x_4139_, 0, v_a_4127_);
v___x_4163_ = v___x_4139_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4127_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec(v___x_4133_);
lean_dec(v_a_4127_);
lean_dec(v_id_3721_);
lean_dec(v_mod_x3f_3720_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v_a_4166_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4136_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4136_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
else
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_dec_ref_known(v_a_4135_, 1);
lean_dec(v___x_4133_);
lean_dec(v_a_4127_);
lean_dec(v_mod_x3f_3720_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v___x_4174_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23);
lean_inc(v_id_3721_);
v___x_4175_ = l_Lean_MessageData_ofSyntax(v_id_3721_);
v___x_4176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4174_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25);
v___x_4178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4176_);
lean_ctor_set(v___x_4178_, 1, v___x_4177_);
v___x_4179_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3721_, v___x_4178_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
lean_dec(v_id_3721_);
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4179_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
lean_dec(v___x_4133_);
lean_dec(v_a_4127_);
lean_dec(v_id_3721_);
lean_dec(v_mod_x3f_3720_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v_a_4188_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v___x_4134_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4134_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
else
{
lean_object* v___x_4197_; 
lean_dec(v_id_3721_);
lean_dec(v_mod_x3f_3720_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
if (v_isShared_4130_ == 0)
{
v___x_4197_ = v___x_4129_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4127_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
}
v___jp_3732_:
{
uint8_t v___x_3741_; lean_object* v___x_3742_; 
v___x_3741_ = 0;
lean_inc(v___y_3734_);
v___x_3742_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3734_, v___x_3741_, v___y_3739_, v___y_3740_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
if (lean_obj_tag(v_a_3743_) == 1)
{
lean_object* v_val_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_dec(v___y_3734_);
v_val_3744_ = lean_ctor_get(v_a_3743_, 0);
lean_inc_n(v_val_3744_, 2);
lean_dec_ref_known(v_a_3743_, 1);
v___x_3745_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3718_, v_val_3744_, v___x_3741_);
v___x_3746_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3744_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3757_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3749_ = v___x_3746_;
v_isShared_3750_ = v_isSharedCheck_3757_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3746_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3757_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
if (lean_obj_tag(v_a_3747_) == 1)
{
lean_object* v_val_3751_; lean_object* v_ctors_3752_; lean_object* v___x_3753_; 
lean_del_object(v___x_3749_);
v_val_3751_ = lean_ctor_get(v_a_3747_, 0);
lean_inc(v_val_3751_);
lean_dec_ref_known(v_a_3747_, 1);
v_ctors_3752_ = lean_ctor_get(v_val_3751_, 4);
lean_inc(v_ctors_3752_);
lean_dec(v_val_3751_);
v___x_3753_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3719_, v_id_3721_, v_minIndexable_3722_, v_ctors_3752_, v___x_3745_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v_ctors_3752_);
lean_dec(v_p_3719_);
return v___x_3753_;
}
else
{
lean_object* v___x_3755_; 
lean_dec(v_a_3747_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v___x_3745_);
v___x_3755_ = v___x_3749_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3745_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
else
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
lean_dec_ref(v___x_3745_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
v_a_3758_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3760_ = v___x_3746_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3746_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3758_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
else
{
lean_object* v_toCold_3766_; lean_object* v_currRecDepth_3767_; lean_object* v_ref_3768_; uint16_t v_optionFlags_3769_; uint8_t v_suppressElabErrors_3770_; uint8_t v_isRecordingDeps_3771_; lean_object* v___x_3772_; lean_object* v_ref_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
lean_dec(v_a_3743_);
v_toCold_3766_ = lean_ctor_get(v___y_3739_, 0);
v_currRecDepth_3767_ = lean_ctor_get(v___y_3739_, 1);
v_ref_3768_ = lean_ctor_get(v___y_3739_, 2);
v_optionFlags_3769_ = lean_ctor_get_uint16(v___y_3739_, sizeof(void*)*3);
v_suppressElabErrors_3770_ = lean_ctor_get_uint8(v___y_3739_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3771_ = lean_ctor_get_uint8(v___y_3739_, sizeof(void*)*3 + 3);
v___x_3772_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_ref_3773_ = l_Lean_replaceRef(v_p_3719_, v_ref_3768_);
lean_dec(v_p_3719_);
lean_inc(v_currRecDepth_3767_);
lean_inc_ref(v_toCold_3766_);
v___x_3774_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3774_, 0, v_toCold_3766_);
lean_ctor_set(v___x_3774_, 1, v_currRecDepth_3767_);
lean_ctor_set(v___x_3774_, 2, v_ref_3773_);
lean_ctor_set_uint16(v___x_3774_, sizeof(void*)*3, v_optionFlags_3769_);
lean_ctor_set_uint8(v___x_3774_, sizeof(void*)*3 + 2, v_suppressElabErrors_3770_);
lean_ctor_set_uint8(v___x_3774_, sizeof(void*)*3 + 3, v_isRecordingDeps_3771_);
v___x_3775_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3718_, v_id_3721_, v___y_3734_, v___x_3772_, v_minIndexable_3722_, v___y_3733_, v___y_3733_, v___y_3737_, v___y_3738_, v___x_3774_, v___y_3740_);
lean_dec_ref_known(v___x_3774_, 3);
return v___x_3775_;
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec(v___y_3734_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v_a_3776_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3742_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3742_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
v___jp_3784_:
{
lean_object* v___x_3793_; 
v___x_3793_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3722_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
lean_dec_ref_known(v___x_3793_, 1);
v___x_3794_ = l_Lean_Meta_Grind_grindExt;
v___x_3795_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3794_, v___y_3792_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3795_, 1);
lean_inc(v___y_3785_);
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___y_3785_);
v___x_3798_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3796_, v___x_3797_);
lean_dec_ref_known(v___x_3797_, 1);
lean_dec(v_a_3796_);
v___x_3799_ = lean_box(0);
v___x_3800_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3786_, v___x_3798_, v___x_3799_);
lean_dec(v___y_3786_);
v___x_3801_ = l_List_isEmpty___redArg(v___x_3800_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; 
lean_dec(v___y_3785_);
lean_dec(v_p_3719_);
v___x_3802_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3800_, v_params_3718_);
lean_dec(v___x_3800_);
return v___x_3802_;
}
else
{
lean_object* v___x_3803_; uint8_t v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec(v___x_3800_);
lean_dec_ref(v_params_3718_);
v___x_3803_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3804_ = 0;
v___x_3805_ = l_Lean_MessageData_ofConstName(v___y_3785_, v___x_3804_);
v___x_3806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3803_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3806_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3719_, v___x_3808_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec(v_p_3719_);
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3809_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3809_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v_a_3818_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3795_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3795_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v_a_3826_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3793_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3793_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
v___jp_3834_:
{
lean_object* v___x_3841_; 
v___x_3841_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3722_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_toCold_3842_; lean_object* v_currRecDepth_3843_; lean_object* v_ref_3844_; uint16_t v_optionFlags_3845_; uint8_t v_suppressElabErrors_3846_; uint8_t v_isRecordingDeps_3847_; lean_object* v_ref_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
lean_dec_ref_known(v___x_3841_, 1);
v_toCold_3842_ = lean_ctor_get(v___y_3839_, 0);
v_currRecDepth_3843_ = lean_ctor_get(v___y_3839_, 1);
v_ref_3844_ = lean_ctor_get(v___y_3839_, 2);
v_optionFlags_3845_ = lean_ctor_get_uint16(v___y_3839_, sizeof(void*)*3);
v_suppressElabErrors_3846_ = lean_ctor_get_uint8(v___y_3839_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3847_ = lean_ctor_get_uint8(v___y_3839_, sizeof(void*)*3 + 3);
v_ref_3848_ = l_Lean_replaceRef(v_p_3719_, v_ref_3844_);
lean_dec(v_p_3719_);
lean_inc(v_currRecDepth_3843_);
lean_inc_ref(v_toCold_3842_);
v___x_3849_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3849_, 0, v_toCold_3842_);
lean_ctor_set(v___x_3849_, 1, v_currRecDepth_3843_);
lean_ctor_set(v___x_3849_, 2, v_ref_3848_);
lean_ctor_set_uint16(v___x_3849_, sizeof(void*)*3, v_optionFlags_3845_);
lean_ctor_set_uint8(v___x_3849_, sizeof(void*)*3 + 2, v_suppressElabErrors_3846_);
lean_ctor_set_uint8(v___x_3849_, sizeof(void*)*3 + 3, v_isRecordingDeps_3847_);
lean_inc(v___y_3836_);
v___x_3850_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3836_, v___y_3835_, v___x_3849_, v___y_3840_);
lean_dec_ref_known(v___x_3849_, 3);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3858_; 
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3858_ == 0)
{
lean_object* v_unused_3859_; 
v_unused_3859_ = lean_ctor_get(v___x_3850_, 0);
lean_dec(v_unused_3859_);
v___x_3852_ = v___x_3850_;
v_isShared_3853_ = v_isSharedCheck_3858_;
goto v_resetjp_3851_;
}
else
{
lean_dec(v___x_3850_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3858_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3854_; lean_object* v___x_3856_; 
v___x_3854_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3718_, v___y_3836_, v___y_3835_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 0, v___x_3854_);
v___x_3856_ = v___x_3852_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v___y_3836_);
lean_dec_ref(v_params_3718_);
v_a_3860_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3850_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3850_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec(v___y_3836_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v_a_3868_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3841_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3841_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
v___jp_3876_:
{
lean_object* v_ctors_3884_; lean_object* v___x_3885_; 
v_ctors_3884_ = lean_ctor_get(v___y_3877_, 4);
lean_inc(v_ctors_3884_);
lean_dec_ref(v___y_3877_);
v___x_3885_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3719_, v_id_3721_, v_minIndexable_3722_, v_ctors_3884_, v_params_3718_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
lean_dec(v_ctors_3884_);
lean_dec(v_p_3719_);
return v___x_3885_;
}
v___jp_3886_:
{
uint8_t v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = 1;
lean_inc(v_a_3887_);
v___x_3889_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_3887_, v___x_3888_, v_a_3725_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_dec_ref_known(v___x_3889_, 1);
if (lean_obj_tag(v_mod_x3f_3720_) == 1)
{
lean_object* v_val_3890_; lean_object* v___x_3891_; 
v_val_3890_ = lean_ctor_get(v_mod_x3f_3720_, 0);
lean_inc(v_val_3890_);
lean_dec_ref_known(v_mod_x3f_3720_, 1);
v___x_3891_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_3890_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_4094_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_3894_ = v___x_3891_;
v_isShared_3895_ = v_isSharedCheck_4094_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3891_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_4094_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
switch(lean_obj_tag(v_a_3892_))
{
case 0:
{
lean_object* v_k_3896_; 
lean_del_object(v___x_3894_);
v_k_3896_ = lean_ctor_get(v_a_3892_, 0);
lean_inc(v_k_3896_);
lean_dec_ref_known(v_a_3892_, 1);
if (lean_obj_tag(v_k_3896_) == 9)
{
lean_dec(v_id_3721_);
if (v_only_3723_ == 0)
{
lean_object* v_toCold_3897_; lean_object* v_currRecDepth_3898_; lean_object* v_ref_3899_; uint16_t v_optionFlags_3900_; uint8_t v_suppressElabErrors_3901_; uint8_t v_isRecordingDeps_3902_; lean_object* v_ref_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_toCold_3897_ = lean_ctor_get(v_a_3729_, 0);
v_currRecDepth_3898_ = lean_ctor_get(v_a_3729_, 1);
v_ref_3899_ = lean_ctor_get(v_a_3729_, 2);
v_optionFlags_3900_ = lean_ctor_get_uint16(v_a_3729_, sizeof(void*)*3);
v_suppressElabErrors_3901_ = lean_ctor_get_uint8(v_a_3729_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3902_ = lean_ctor_get_uint8(v_a_3729_, sizeof(void*)*3 + 3);
v_ref_3903_ = l_Lean_replaceRef(v_p_3719_, v_ref_3899_);
lean_inc(v_currRecDepth_3898_);
lean_inc_ref(v_toCold_3897_);
v___x_3904_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3904_, 0, v_toCold_3897_);
lean_ctor_set(v___x_3904_, 1, v_currRecDepth_3898_);
lean_ctor_set(v___x_3904_, 2, v_ref_3903_);
lean_ctor_set_uint16(v___x_3904_, sizeof(void*)*3, v_optionFlags_3900_);
lean_ctor_set_uint8(v___x_3904_, sizeof(void*)*3 + 2, v_suppressElabErrors_3901_);
lean_ctor_set_uint8(v___x_3904_, sizeof(void*)*3 + 3, v_isRecordingDeps_3902_);
v___x_3905_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_3904_, v_a_3730_);
lean_dec_ref_known(v___x_3904_, 3);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_dec_ref_known(v___x_3905_, 1);
v___y_3785_ = v_a_3887_;
v___y_3786_ = v_k_3896_;
v___y_3787_ = v_a_3725_;
v___y_3788_ = v_a_3726_;
v___y_3789_ = v_a_3727_;
v___y_3790_ = v_a_3728_;
v___y_3791_ = v_a_3729_;
v___y_3792_ = v_a_3730_;
goto v___jp_3784_;
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec(v_a_3887_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3905_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3905_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
v___y_3785_ = v_a_3887_;
v___y_3786_ = v_k_3896_;
v___y_3787_ = v_a_3725_;
v___y_3788_ = v_a_3726_;
v___y_3789_ = v_a_3727_;
v___y_3790_ = v_a_3728_;
v___y_3791_ = v_a_3729_;
v___y_3792_ = v_a_3730_;
goto v___jp_3784_;
}
}
else
{
lean_object* v_toCold_3914_; lean_object* v_currRecDepth_3915_; lean_object* v_ref_3916_; uint16_t v_optionFlags_3917_; uint8_t v_suppressElabErrors_3918_; uint8_t v_isRecordingDeps_3919_; uint8_t v___x_3920_; lean_object* v_ref_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v_toCold_3914_ = lean_ctor_get(v_a_3729_, 0);
v_currRecDepth_3915_ = lean_ctor_get(v_a_3729_, 1);
v_ref_3916_ = lean_ctor_get(v_a_3729_, 2);
v_optionFlags_3917_ = lean_ctor_get_uint16(v_a_3729_, sizeof(void*)*3);
v_suppressElabErrors_3918_ = lean_ctor_get_uint8(v_a_3729_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3919_ = lean_ctor_get_uint8(v_a_3729_, sizeof(void*)*3 + 3);
v___x_3920_ = 0;
v_ref_3921_ = l_Lean_replaceRef(v_p_3719_, v_ref_3916_);
lean_dec(v_p_3719_);
lean_inc(v_currRecDepth_3915_);
lean_inc_ref(v_toCold_3914_);
v___x_3922_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3922_, 0, v_toCold_3914_);
lean_ctor_set(v___x_3922_, 1, v_currRecDepth_3915_);
lean_ctor_set(v___x_3922_, 2, v_ref_3921_);
lean_ctor_set_uint16(v___x_3922_, sizeof(void*)*3, v_optionFlags_3917_);
lean_ctor_set_uint8(v___x_3922_, sizeof(void*)*3 + 2, v_suppressElabErrors_3918_);
lean_ctor_set_uint8(v___x_3922_, sizeof(void*)*3 + 3, v_isRecordingDeps_3919_);
v___x_3923_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3718_, v_id_3721_, v_a_3887_, v_k_3896_, v_minIndexable_3722_, v___x_3920_, v___x_3888_, v_a_3727_, v_a_3728_, v___x_3922_, v_a_3730_);
lean_dec_ref_known(v___x_3922_, 3);
return v___x_3923_;
}
}
case 1:
{
lean_del_object(v___x_3894_);
lean_dec(v_id_3721_);
if (v_incremental_3724_ == 0)
{
uint8_t v_eager_3924_; 
v_eager_3924_ = lean_ctor_get_uint8(v_a_3892_, 0);
lean_dec_ref_known(v_a_3892_, 0);
v___y_3835_ = v_eager_3924_;
v___y_3836_ = v_a_3887_;
v___y_3837_ = v_a_3727_;
v___y_3838_ = v_a_3728_;
v___y_3839_ = v_a_3729_;
v___y_3840_ = v_a_3730_;
goto v___jp_3834_;
}
else
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec_ref_known(v_a_3892_, 0);
lean_dec(v_a_3887_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v___x_3925_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3926_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_3925_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
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
}
case 2:
{
uint8_t v___x_3935_; lean_object* v___x_3936_; 
lean_del_object(v___x_3894_);
v___x_3935_ = 0;
lean_inc(v_a_3887_);
v___x_3936_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3887_, v___x_3935_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_3937_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3937_);
lean_dec_ref_known(v___x_3936_, 1);
if (lean_obj_tag(v_a_3937_) == 1)
{
lean_dec(v_a_3887_);
if (v_incremental_3724_ == 0)
{
lean_object* v_val_3938_; 
v_val_3938_ = lean_ctor_get(v_a_3937_, 0);
lean_inc(v_val_3938_);
lean_dec_ref_known(v_a_3937_, 1);
v___y_3877_ = v_val_3938_;
v___y_3878_ = v_a_3725_;
v___y_3879_ = v_a_3726_;
v___y_3880_ = v_a_3727_;
v___y_3881_ = v_a_3728_;
v___y_3882_ = v_a_3729_;
v___y_3883_ = v_a_3730_;
goto v___jp_3876_;
}
else
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
lean_dec_ref_known(v_a_3937_, 1);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v___x_3939_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3940_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_3939_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3940_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3940_);
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
else
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v_a_3937_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v___x_3949_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_3950_ = l_Lean_MessageData_ofConstName(v_a_3887_, v___x_3935_);
v___x_3951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3949_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
v___x_3952_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_3953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3951_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___x_3954_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_3953_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3954_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3954_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec(v_a_3887_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v_a_3963_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3936_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3936_);
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
}
case 3:
{
lean_del_object(v___x_3894_);
v___y_3733_ = v___x_3888_;
v___y_3734_ = v_a_3887_;
v___y_3735_ = v_a_3725_;
v___y_3736_ = v_a_3726_;
v___y_3737_ = v_a_3727_;
v___y_3738_ = v_a_3728_;
v___y_3739_ = v_a_3729_;
v___y_3740_ = v_a_3730_;
goto v___jp_3732_;
}
case 4:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_del_object(v___x_3894_);
lean_dec(v_a_3887_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v___x_3971_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_3972_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_3971_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
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
case 5:
{
lean_object* v_prio_3981_; lean_object* v___x_3982_; 
lean_del_object(v___x_3894_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
v_prio_3981_ = lean_ctor_get(v_a_3892_, 0);
lean_inc(v_prio_3981_);
lean_dec_ref_known(v_a_3892_, 1);
v___x_3982_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3722_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4006_; 
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4006_ == 0)
{
lean_object* v_unused_4007_; 
v_unused_4007_ = lean_ctor_get(v___x_3982_, 0);
lean_dec(v_unused_4007_);
v___x_3984_ = v___x_3982_;
v_isShared_3985_ = v_isSharedCheck_4006_;
goto v_resetjp_3983_;
}
else
{
lean_dec(v___x_3982_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4006_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v_config_3986_; lean_object* v_extensions_3987_; lean_object* v_extra_3988_; lean_object* v_extraInj_3989_; lean_object* v_extraFacts_3990_; lean_object* v_symPrios_3991_; lean_object* v_norm_3992_; lean_object* v_normProcs_3993_; lean_object* v_anchorRefs_x3f_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4005_; 
v_config_3986_ = lean_ctor_get(v_params_3718_, 0);
v_extensions_3987_ = lean_ctor_get(v_params_3718_, 1);
v_extra_3988_ = lean_ctor_get(v_params_3718_, 2);
v_extraInj_3989_ = lean_ctor_get(v_params_3718_, 3);
v_extraFacts_3990_ = lean_ctor_get(v_params_3718_, 4);
v_symPrios_3991_ = lean_ctor_get(v_params_3718_, 5);
v_norm_3992_ = lean_ctor_get(v_params_3718_, 6);
v_normProcs_3993_ = lean_ctor_get(v_params_3718_, 7);
v_anchorRefs_x3f_3994_ = lean_ctor_get(v_params_3718_, 8);
v_isSharedCheck_4005_ = !lean_is_exclusive(v_params_3718_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3996_ = v_params_3718_;
v_isShared_3997_ = v_isSharedCheck_4005_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_anchorRefs_x3f_3994_);
lean_inc(v_normProcs_3993_);
lean_inc(v_norm_3992_);
lean_inc(v_symPrios_3991_);
lean_inc(v_extraFacts_3990_);
lean_inc(v_extraInj_3989_);
lean_inc(v_extra_3988_);
lean_inc(v_extensions_3987_);
lean_inc(v_config_3986_);
lean_dec(v_params_3718_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4005_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3998_; lean_object* v___x_4000_; 
v___x_3998_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_3991_, v_a_3887_, v_prio_3981_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 5, v___x_3998_);
v___x_4000_ = v___x_3996_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_config_3986_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_extensions_3987_);
lean_ctor_set(v_reuseFailAlloc_4004_, 2, v_extra_3988_);
lean_ctor_set(v_reuseFailAlloc_4004_, 3, v_extraInj_3989_);
lean_ctor_set(v_reuseFailAlloc_4004_, 4, v_extraFacts_3990_);
lean_ctor_set(v_reuseFailAlloc_4004_, 5, v___x_3998_);
lean_ctor_set(v_reuseFailAlloc_4004_, 6, v_norm_3992_);
lean_ctor_set(v_reuseFailAlloc_4004_, 7, v_normProcs_3993_);
lean_ctor_set(v_reuseFailAlloc_4004_, 8, v_anchorRefs_x3f_3994_);
v___x_4000_ = v_reuseFailAlloc_4004_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
lean_object* v___x_4002_; 
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_4000_);
v___x_4002_ = v___x_3984_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_4000_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec(v_prio_3981_);
lean_dec(v_a_3887_);
lean_dec_ref(v_params_3718_);
v_a_4008_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3982_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3982_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
case 6:
{
lean_object* v___x_4016_; 
lean_del_object(v___x_3894_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
v___x_4016_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3887_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4041_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4019_ = v___x_4016_;
v_isShared_4020_ = v_isSharedCheck_4041_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4016_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4041_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v_config_4021_; lean_object* v_extensions_4022_; lean_object* v_extra_4023_; lean_object* v_extraInj_4024_; lean_object* v_extraFacts_4025_; lean_object* v_symPrios_4026_; lean_object* v_norm_4027_; lean_object* v_normProcs_4028_; lean_object* v_anchorRefs_x3f_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4040_; 
v_config_4021_ = lean_ctor_get(v_params_3718_, 0);
v_extensions_4022_ = lean_ctor_get(v_params_3718_, 1);
v_extra_4023_ = lean_ctor_get(v_params_3718_, 2);
v_extraInj_4024_ = lean_ctor_get(v_params_3718_, 3);
v_extraFacts_4025_ = lean_ctor_get(v_params_3718_, 4);
v_symPrios_4026_ = lean_ctor_get(v_params_3718_, 5);
v_norm_4027_ = lean_ctor_get(v_params_3718_, 6);
v_normProcs_4028_ = lean_ctor_get(v_params_3718_, 7);
v_anchorRefs_x3f_4029_ = lean_ctor_get(v_params_3718_, 8);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_params_3718_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4031_ = v_params_3718_;
v_isShared_4032_ = v_isSharedCheck_4040_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_anchorRefs_x3f_4029_);
lean_inc(v_normProcs_4028_);
lean_inc(v_norm_4027_);
lean_inc(v_symPrios_4026_);
lean_inc(v_extraFacts_4025_);
lean_inc(v_extraInj_4024_);
lean_inc(v_extra_4023_);
lean_inc(v_extensions_4022_);
lean_inc(v_config_4021_);
lean_dec(v_params_3718_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4040_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4033_; lean_object* v___x_4035_; 
v___x_4033_ = l_Lean_PersistentArray_push___redArg(v_extraInj_4024_, v_a_4017_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 3, v___x_4033_);
v___x_4035_ = v___x_4031_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_config_4021_);
lean_ctor_set(v_reuseFailAlloc_4039_, 1, v_extensions_4022_);
lean_ctor_set(v_reuseFailAlloc_4039_, 2, v_extra_4023_);
lean_ctor_set(v_reuseFailAlloc_4039_, 3, v___x_4033_);
lean_ctor_set(v_reuseFailAlloc_4039_, 4, v_extraFacts_4025_);
lean_ctor_set(v_reuseFailAlloc_4039_, 5, v_symPrios_4026_);
lean_ctor_set(v_reuseFailAlloc_4039_, 6, v_norm_4027_);
lean_ctor_set(v_reuseFailAlloc_4039_, 7, v_normProcs_4028_);
lean_ctor_set(v_reuseFailAlloc_4039_, 8, v_anchorRefs_x3f_4029_);
v___x_4035_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
lean_object* v___x_4037_; 
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4035_);
v___x_4037_ = v___x_4019_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4035_);
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
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_dec_ref(v_params_3718_);
v_a_4042_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4016_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4016_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
case 7:
{
lean_object* v___x_4050_; lean_object* v___x_4052_; 
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
v___x_4050_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3718_, v_a_3887_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v___x_4050_);
v___x_4052_ = v___x_3894_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
case 8:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec_ref_known(v_a_3892_, 0);
lean_del_object(v___x_3894_);
lean_dec(v_a_3887_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v___x_4054_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_4055_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4054_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4055_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4055_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
case 9:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4073_; 
lean_del_object(v___x_3894_);
lean_dec(v_a_3887_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v___x_4064_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_4065_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4064_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
v_a_4066_ = lean_ctor_get(v___x_4065_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4068_ = v___x_4065_;
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_4065_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
case 10:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
lean_dec_ref_known(v_a_3892_, 0);
lean_del_object(v___x_3894_);
lean_dec(v_a_3887_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v___x_4074_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_4075_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4074_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4075_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4075_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
default: 
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_del_object(v___x_3894_);
lean_dec(v_a_3887_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v___x_4084_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
v___x_4085_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4084_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4085_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4085_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_dec(v_a_3887_);
lean_dec(v_id_3721_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v_a_4095_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_3891_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_3891_);
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
lean_dec(v_mod_x3f_3720_);
v___y_3733_ = v___x_3888_;
v___y_3734_ = v_a_3887_;
v___y_3735_ = v_a_3725_;
v___y_3736_ = v_a_3726_;
v___y_3737_ = v_a_3727_;
v___y_3738_ = v_a_3728_;
v___y_3739_ = v_a_3729_;
v___y_3740_ = v_a_3730_;
goto v___jp_3732_;
}
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec(v_a_3887_);
lean_dec(v_id_3721_);
lean_dec(v_mod_x3f_3720_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v_a_4103_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_3889_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_3889_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
v___jp_4111_:
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4122_; 
v_a_4113_ = lean_ctor_get(v___y_4112_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___y_4112_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4115_ = v___y_4112_;
v_isShared_4116_ = v_isSharedCheck_4122_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___y_4112_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4122_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
if (lean_obj_tag(v_a_4113_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4119_; 
lean_dec(v_id_3721_);
lean_dec(v_mod_x3f_3720_);
lean_dec(v_p_3719_);
lean_dec_ref(v_params_3718_);
v_a_4117_ = lean_ctor_get(v_a_4113_, 0);
lean_inc(v_a_4117_);
lean_dec_ref_known(v_a_4113_, 1);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v_a_4117_);
v___x_4119_ = v___x_4115_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4117_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
else
{
lean_object* v_a_4121_; 
lean_del_object(v___x_4115_);
v_a_4121_ = lean_ctor_get(v_a_4113_, 0);
lean_inc(v_a_4121_);
lean_dec_ref_known(v_a_4113_, 1);
v_a_3887_ = v_a_4121_;
goto v___jp_3886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4202_, lean_object* v_p_4203_, lean_object* v_mod_x3f_4204_, lean_object* v_id_4205_, lean_object* v_minIndexable_4206_, lean_object* v_only_4207_, lean_object* v_incremental_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_){
_start:
{
uint8_t v_minIndexable_boxed_4216_; uint8_t v_only_boxed_4217_; uint8_t v_incremental_boxed_4218_; lean_object* v_res_4219_; 
v_minIndexable_boxed_4216_ = lean_unbox(v_minIndexable_4206_);
v_only_boxed_4217_ = lean_unbox(v_only_4207_);
v_incremental_boxed_4218_ = lean_unbox(v_incremental_4208_);
v_res_4219_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4202_, v_p_4203_, v_mod_x3f_4204_, v_id_4205_, v_minIndexable_boxed_4216_, v_only_boxed_4217_, v_incremental_boxed_4218_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
lean_dec(v_a_4210_);
lean_dec_ref(v_a_4209_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4220_, lean_object* v_id_4221_, uint8_t v_minIndexable_4222_, lean_object* v_as_4223_, lean_object* v_as_x27_4224_, lean_object* v_b_4225_, lean_object* v_a_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4220_, v_id_4221_, v_minIndexable_4222_, v_as_x27_4224_, v_b_4225_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4235_, lean_object* v_id_4236_, lean_object* v_minIndexable_4237_, lean_object* v_as_4238_, lean_object* v_as_x27_4239_, lean_object* v_b_4240_, lean_object* v_a_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
uint8_t v_minIndexable_boxed_4249_; lean_object* v_res_4250_; 
v_minIndexable_boxed_4249_ = lean_unbox(v_minIndexable_4237_);
v_res_4250_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4235_, v_id_4236_, v_minIndexable_boxed_4249_, v_as_4238_, v_as_x27_4239_, v_b_4240_, v_a_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v_as_x27_4239_);
lean_dec(v_as_4238_);
lean_dec(v_p_4235_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4251_, lean_object* v_as_x27_4252_, lean_object* v_b_4253_, lean_object* v_a_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v___x_4262_; 
v___x_4262_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4252_, v_b_4253_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4263_, lean_object* v_as_x27_4264_, lean_object* v_b_4265_, lean_object* v_a_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4263_, v_as_x27_4264_, v_b_4265_, v_a_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v_as_x27_4264_);
lean_dec(v_as_4263_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4275_, lean_object* v_ref_4276_, lean_object* v_msg_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
lean_object* v___x_4285_; 
v___x_4285_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4276_, v_msg_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4286_, lean_object* v_ref_4287_, lean_object* v_msg_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4286_, v_ref_4287_, v_msg_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v_ref_4287_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4297_, lean_object* v_id_4298_, uint8_t v_minIndexable_4299_, lean_object* v_as_4300_, lean_object* v_as_x27_4301_, lean_object* v_b_4302_, lean_object* v_a_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v___x_4311_; 
v___x_4311_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4297_, v_id_4298_, v_minIndexable_4299_, v_as_x27_4301_, v_b_4302_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4312_, lean_object* v_id_4313_, lean_object* v_minIndexable_4314_, lean_object* v_as_4315_, lean_object* v_as_x27_4316_, lean_object* v_b_4317_, lean_object* v_a_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
uint8_t v_minIndexable_boxed_4326_; lean_object* v_res_4327_; 
v_minIndexable_boxed_4326_ = lean_unbox(v_minIndexable_4314_);
v_res_4327_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4312_, v_id_4313_, v_minIndexable_boxed_4326_, v_as_4315_, v_as_x27_4316_, v_b_4317_, v_a_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec(v_as_x27_4316_);
lean_dec(v_as_4315_);
lean_dec(v_p_4312_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4328_, lean_object* v_t_4329_, lean_object* v_k_4330_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4329_, v_k_4330_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4332_, lean_object* v_t_4333_, lean_object* v_k_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4332_, v_t_4333_, v_k_4334_);
lean_dec(v_k_4334_);
lean_dec(v_t_4333_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4336_, uint8_t v_skipAuxDecl_4337_, lean_object* v_auxDeclToFullName_4338_, lean_object* v___x_4339_, lean_object* v_givenNameView_4340_, lean_object* v_as_4341_, lean_object* v_i_4342_, lean_object* v_a_4343_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4336_, v_skipAuxDecl_4337_, v_auxDeclToFullName_4338_, v___x_4339_, v_givenNameView_4340_, v_as_4341_, v_i_4342_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4345_, lean_object* v_skipAuxDecl_4346_, lean_object* v_auxDeclToFullName_4347_, lean_object* v___x_4348_, lean_object* v_givenNameView_4349_, lean_object* v_as_4350_, lean_object* v_i_4351_, lean_object* v_a_4352_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4353_; lean_object* v_res_4354_; 
v_skipAuxDecl_boxed_4353_ = lean_unbox(v_skipAuxDecl_4346_);
v_res_4354_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4345_, v_skipAuxDecl_boxed_4353_, v_auxDeclToFullName_4347_, v___x_4348_, v_givenNameView_4349_, v_as_4350_, v_i_4351_, v_a_4352_);
lean_dec_ref(v_as_4350_);
lean_dec(v_auxDeclToFullName_4347_);
lean_dec(v_givenName_4345_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4355_, lean_object* v_givenName_4356_, lean_object* v_as_4357_, lean_object* v_i_4358_, lean_object* v_a_4359_){
_start:
{
lean_object* v___x_4360_; 
v___x_4360_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4355_, v_givenName_4356_, v_as_4357_, v_i_4358_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4361_, lean_object* v_givenName_4362_, lean_object* v_as_4363_, lean_object* v_i_4364_, lean_object* v_a_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4361_, v_givenName_4362_, v_as_4363_, v_i_4364_, v_a_4365_);
lean_dec_ref(v_as_4363_);
lean_dec(v_givenName_4362_);
lean_dec(v_localDecl_x3f_4361_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4367_, uint8_t v_skipAuxDecl_4368_, lean_object* v_auxDeclToFullName_4369_, lean_object* v___x_4370_, lean_object* v_givenNameView_4371_, lean_object* v_as_4372_, lean_object* v_i_4373_, lean_object* v_a_4374_){
_start:
{
lean_object* v___x_4375_; 
v___x_4375_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4367_, v_skipAuxDecl_4368_, v_auxDeclToFullName_4369_, v___x_4370_, v_givenNameView_4371_, v_as_4372_, v_i_4373_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4376_, lean_object* v_skipAuxDecl_4377_, lean_object* v_auxDeclToFullName_4378_, lean_object* v___x_4379_, lean_object* v_givenNameView_4380_, lean_object* v_as_4381_, lean_object* v_i_4382_, lean_object* v_a_4383_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4384_; lean_object* v_res_4385_; 
v_skipAuxDecl_boxed_4384_ = lean_unbox(v_skipAuxDecl_4377_);
v_res_4385_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4376_, v_skipAuxDecl_boxed_4384_, v_auxDeclToFullName_4378_, v___x_4379_, v_givenNameView_4380_, v_as_4381_, v_i_4382_, v_a_4383_);
lean_dec_ref(v_as_4381_);
lean_dec(v_auxDeclToFullName_4378_);
lean_dec(v_givenName_4376_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4386_, lean_object* v_givenName_4387_, lean_object* v_as_4388_, lean_object* v_i_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4386_, v_givenName_4387_, v_as_4388_, v_i_4389_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4392_, lean_object* v_givenName_4393_, lean_object* v_as_4394_, lean_object* v_i_4395_, lean_object* v_a_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4392_, v_givenName_4393_, v_as_4394_, v_i_4395_, v_a_4396_);
lean_dec_ref(v_as_4394_);
lean_dec(v_givenName_4393_);
lean_dec(v_localDecl_x3f_4392_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v___x_4406_; 
v___x_4406_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4398_, v___y_4403_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec_ref(v_opt_4407_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4416_, lean_object* v_msgData_4417_, uint8_t v_severity_4418_, uint8_t v_isSilent_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4416_, v_msgData_4417_, v_severity_4418_, v_isSilent_4419_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4428_, lean_object* v_msgData_4429_, lean_object* v_severity_4430_, lean_object* v_isSilent_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
uint8_t v_severity_boxed_4439_; uint8_t v_isSilent_boxed_4440_; lean_object* v_res_4441_; 
v_severity_boxed_4439_ = lean_unbox(v_severity_4430_);
v_isSilent_boxed_4440_ = lean_unbox(v_isSilent_4431_);
v_res_4441_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4428_, v_msgData_4429_, v_severity_boxed_4439_, v_isSilent_boxed_4440_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v_ref_4428_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4442_, uint8_t v___x_4443_, lean_object* v_b_4444_, lean_object* v_____r_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = lean_box(0);
v___x_4454_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4442_, v___x_4453_, v___y_4450_, v___y_4451_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v___x_4456_; 
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc_n(v_a_4455_, 2);
lean_dec_ref_known(v___x_4454_, 1);
v___x_4456_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4455_, v___x_4443_, v___y_4446_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
if (lean_obj_tag(v___x_4456_) == 0)
{
uint8_t v___x_4457_; lean_object* v___x_4458_; 
lean_dec_ref_known(v___x_4456_, 1);
v___x_4457_ = 0;
lean_inc(v_a_4455_);
v___x_4458_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4455_, v___x_4457_, v___y_4450_, v___y_4451_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4518_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4461_ = v___x_4458_;
v_isShared_4462_ = v_isSharedCheck_4518_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4458_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4518_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
if (lean_obj_tag(v_a_4459_) == 1)
{
lean_object* v_val_4463_; lean_object* v___x_4464_; 
lean_del_object(v___x_4461_);
lean_dec(v_a_4455_);
v_val_4463_ = lean_ctor_get(v_a_4459_, 0);
lean_inc_n(v_val_4463_, 2);
lean_dec_ref_known(v_a_4459_, 1);
v___x_4464_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4463_, v___y_4450_, v___y_4451_);
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_object* v___x_4465_; 
lean_dec_ref_known(v___x_4464_, 1);
v___x_4465_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4444_, v_val_4463_, v___y_4450_, v___y_4451_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4475_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4468_ = v___x_4465_;
v_isShared_4469_ = v_isSharedCheck_4475_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4465_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4475_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4473_; 
v___x_4470_ = lean_box(0);
v___x_4471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
lean_ctor_set(v___x_4471_, 1, v_a_4466_);
if (v_isShared_4469_ == 0)
{
lean_ctor_set(v___x_4468_, 0, v___x_4471_);
v___x_4473_ = v___x_4468_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4471_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
v_a_4476_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4465_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4465_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
else
{
lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4491_; 
lean_dec(v_val_4463_);
lean_dec_ref(v_b_4444_);
v_a_4484_ = lean_ctor_get(v___x_4464_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4464_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4486_ = v___x_4464_;
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_dec(v___x_4464_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4489_; 
if (v_isShared_4487_ == 0)
{
v___x_4489_ = v___x_4486_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4484_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
else
{
uint8_t v___x_4492_; 
lean_dec(v_a_4459_);
lean_inc(v_a_4455_);
v___x_4492_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4444_, v_a_4455_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; 
lean_del_object(v___x_4461_);
v___x_4493_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4444_, v_a_4455_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4503_; 
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4496_ = v___x_4493_;
v_isShared_4497_ = v_isSharedCheck_4503_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4493_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4503_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4501_; 
v___x_4498_ = lean_box(0);
v___x_4499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
lean_ctor_set(v___x_4499_, 1, v_a_4494_);
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v___x_4499_);
v___x_4501_ = v___x_4496_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4499_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
v_a_4504_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4493_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4493_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
else
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4516_; 
v___x_4512_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4444_, v_a_4455_);
v___x_4513_ = lean_box(0);
v___x_4514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4513_);
lean_ctor_set(v___x_4514_, 1, v___x_4512_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v___x_4514_);
v___x_4516_ = v___x_4461_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4514_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec(v_a_4455_);
lean_dec_ref(v_b_4444_);
v_a_4519_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4458_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4458_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
else
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4534_; 
lean_dec(v_a_4455_);
lean_dec_ref(v_b_4444_);
v_a_4527_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4529_ = v___x_4456_;
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___x_4456_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4532_; 
if (v_isShared_4530_ == 0)
{
v___x_4532_ = v___x_4529_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_a_4527_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
else
{
lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4542_; 
lean_dec_ref(v_b_4444_);
v_a_4535_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4537_ = v___x_4454_;
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_dec(v___x_4454_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4543_, lean_object* v___x_4544_, lean_object* v_b_4545_, lean_object* v_____r_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
uint8_t v___x_17514__boxed_4554_; lean_object* v_res_4555_; 
v___x_17514__boxed_4554_ = lean_unbox(v___x_4544_);
v_res_4555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4543_, v___x_17514__boxed_4554_, v_b_4545_, v_____r_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4559_, lean_object* v_b_4560_, lean_object* v_a_4561_, uint8_t v___x_4562_, uint8_t v_only_4563_, uint8_t v_incremental_4564_, lean_object* v_x_4565_, lean_object* v_mod_x3f_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4574_ = lean_unsigned_to_nat(1u);
v___x_4575_ = l_Lean_Syntax_getArg(v___x_4559_, v___x_4574_);
if (v___x_4562_ == 0)
{
lean_object* v___x_4636_; uint8_t v___x_4637_; 
v___x_4636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4575_);
v___x_4637_ = l_Lean_Syntax_isOfKind(v___x_4575_, v___x_4636_);
if (v___x_4637_ == 0)
{
lean_object* v___x_4638_; 
v___x_4638_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4560_, v_a_4561_, v_mod_x3f_4566_, v___x_4575_, v___x_4562_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4648_; 
v_a_4639_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4641_ = v___x_4638_;
v_isShared_4642_ = v_isSharedCheck_4648_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4638_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4648_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4646_; 
v___x_4643_ = lean_box(0);
v___x_4644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4643_);
lean_ctor_set(v___x_4644_, 1, v_a_4639_);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 0, v___x_4644_);
v___x_4646_ = v___x_4641_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4644_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
else
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4656_; 
v_a_4649_ = lean_ctor_get(v___x_4638_, 0);
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4638_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4651_ = v___x_4638_;
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4638_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4656_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4654_; 
if (v_isShared_4652_ == 0)
{
v___x_4654_ = v___x_4651_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v_a_4649_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
return v___x_4654_;
}
}
}
}
else
{
goto v___jp_4596_;
}
}
else
{
goto v___jp_4596_;
}
v___jp_4576_:
{
lean_object* v___x_4577_; 
v___x_4577_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4560_, v_a_4561_, v_mod_x3f_4566_, v___x_4575_, v___x_4562_, v_only_4563_, v_incremental_4564_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
if (lean_obj_tag(v___x_4577_) == 0)
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4587_; 
v_a_4578_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4580_ = v___x_4577_;
v_isShared_4581_ = v_isSharedCheck_4587_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v___x_4577_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4587_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4585_; 
v___x_4582_ = lean_box(0);
v___x_4583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
lean_ctor_set(v___x_4583_, 1, v_a_4578_);
if (v_isShared_4581_ == 0)
{
lean_ctor_set(v___x_4580_, 0, v___x_4583_);
v___x_4585_ = v___x_4580_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4583_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4595_; 
v_a_4588_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v___x_4577_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4577_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4593_; 
if (v_isShared_4591_ == 0)
{
v___x_4593_ = v___x_4590_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
v___jp_4596_:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4597_ = l_Lean_TSyntax_getId(v___x_4575_);
v___x_4598_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4597_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_a_4599_);
lean_dec_ref_known(v___x_4598_, 1);
if (lean_obj_tag(v_a_4599_) == 1)
{
lean_object* v_val_4600_; lean_object* v_snd_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4626_; 
v_val_4600_ = lean_ctor_get(v_a_4599_, 0);
lean_inc(v_val_4600_);
lean_dec_ref_known(v_a_4599_, 1);
v_snd_4601_ = lean_ctor_get(v_val_4600_, 1);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_val_4600_);
if (v_isSharedCheck_4626_ == 0)
{
lean_object* v_unused_4627_; 
v_unused_4627_ = lean_ctor_get(v_val_4600_, 0);
lean_dec(v_unused_4627_);
v___x_4603_ = v_val_4600_;
v_isShared_4604_ = v_isSharedCheck_4626_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_snd_4601_);
lean_dec(v_val_4600_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4626_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
if (lean_obj_tag(v_snd_4601_) == 1)
{
lean_object* v___x_4605_; 
lean_dec_ref_known(v_snd_4601_, 2);
v___x_4605_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4560_, v_a_4561_, v_mod_x3f_4566_, v___x_4575_, v___x_4562_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4617_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4608_ = v___x_4605_;
v_isShared_4609_ = v_isSharedCheck_4617_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4605_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4617_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4610_; lean_object* v___x_4612_; 
v___x_4610_ = lean_box(0);
if (v_isShared_4604_ == 0)
{
lean_ctor_set(v___x_4603_, 1, v_a_4606_);
lean_ctor_set(v___x_4603_, 0, v___x_4610_);
v___x_4612_ = v___x_4603_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4610_);
lean_ctor_set(v_reuseFailAlloc_4616_, 1, v_a_4606_);
v___x_4612_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
lean_object* v___x_4614_; 
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 0, v___x_4612_);
v___x_4614_ = v___x_4608_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4612_);
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
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4625_; 
lean_del_object(v___x_4603_);
v_a_4618_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4620_ = v___x_4605_;
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4605_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
else
{
lean_del_object(v___x_4603_);
lean_dec(v_snd_4601_);
goto v___jp_4576_;
}
}
}
else
{
lean_dec(v_a_4599_);
goto v___jp_4576_;
}
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
lean_dec(v___x_4575_);
lean_dec(v_mod_x3f_4566_);
lean_dec(v_a_4561_);
lean_dec_ref(v_b_4560_);
v_a_4628_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4598_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4598_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4657_, lean_object* v_b_4658_, lean_object* v_a_4659_, lean_object* v___x_4660_, lean_object* v_only_4661_, lean_object* v_incremental_4662_, lean_object* v_x_4663_, lean_object* v_mod_x3f_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
uint8_t v___x_17732__boxed_4672_; uint8_t v_only_boxed_4673_; uint8_t v_incremental_boxed_4674_; lean_object* v_res_4675_; 
v___x_17732__boxed_4672_ = lean_unbox(v___x_4660_);
v_only_boxed_4673_ = lean_unbox(v_only_4661_);
v_incremental_boxed_4674_ = lean_unbox(v_incremental_4662_);
v_res_4675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4657_, v_b_4658_, v_a_4659_, v___x_17732__boxed_4672_, v_only_boxed_4673_, v_incremental_boxed_4674_, v_x_4663_, v_mod_x3f_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
lean_dec(v___x_4657_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4676_, lean_object* v___x_4677_, lean_object* v_____r_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v___x_4686_; 
v___x_4686_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4676_, v___x_4677_, v___y_4683_, v___y_4684_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4696_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4689_ = v___x_4686_;
v_isShared_4690_ = v_isSharedCheck_4696_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4686_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4696_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4694_; 
v___x_4691_ = lean_box(0);
v___x_4692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
lean_ctor_set(v___x_4692_, 1, v_a_4687_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 0, v___x_4692_);
v___x_4694_ = v___x_4689_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4692_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
v_a_4697_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4686_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4686_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4705_, lean_object* v___x_4706_, lean_object* v_____r_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4705_, v___x_4706_, v_____r_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec(v___x_4706_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4716_, lean_object* v_b_4717_, lean_object* v_a_4718_, uint8_t v___x_4719_, uint8_t v_only_4720_, uint8_t v_incremental_4721_, uint8_t v___x_4722_, lean_object* v_x_4723_, lean_object* v_mod_x3f_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_){
_start:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = lean_unsigned_to_nat(2u);
v___x_4733_ = l_Lean_Syntax_getArg(v___x_4716_, v___x_4732_);
if (v___x_4722_ == 0)
{
lean_object* v___x_4794_; uint8_t v___x_4795_; 
v___x_4794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4733_);
v___x_4795_ = l_Lean_Syntax_isOfKind(v___x_4733_, v___x_4794_);
if (v___x_4795_ == 0)
{
lean_object* v___x_4796_; 
v___x_4796_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4717_, v_a_4718_, v_mod_x3f_4724_, v___x_4733_, v___x_4719_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4806_; 
v_a_4797_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4799_ = v___x_4796_;
v_isShared_4800_ = v_isSharedCheck_4806_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v___x_4796_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4806_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4804_; 
v___x_4801_ = lean_box(0);
v___x_4802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
lean_ctor_set(v___x_4802_, 1, v_a_4797_);
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 0, v___x_4802_);
v___x_4804_ = v___x_4799_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v___x_4802_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
v_a_4807_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4809_ = v___x_4796_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4796_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
else
{
goto v___jp_4754_;
}
}
else
{
goto v___jp_4754_;
}
v___jp_4734_:
{
lean_object* v___x_4735_; 
v___x_4735_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4717_, v_a_4718_, v_mod_x3f_4724_, v___x_4733_, v___x_4719_, v_only_4720_, v_incremental_4721_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4745_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4738_ = v___x_4735_;
v_isShared_4739_ = v_isSharedCheck_4745_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4735_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4745_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4743_; 
v___x_4740_ = lean_box(0);
v___x_4741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
lean_ctor_set(v___x_4741_, 1, v_a_4736_);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 0, v___x_4741_);
v___x_4743_ = v___x_4738_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4741_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
else
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
v_a_4746_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4735_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4735_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
v___jp_4754_:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4755_ = l_Lean_TSyntax_getId(v___x_4733_);
v___x_4756_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4755_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; 
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
lean_inc(v_a_4757_);
lean_dec_ref_known(v___x_4756_, 1);
if (lean_obj_tag(v_a_4757_) == 1)
{
lean_object* v_val_4758_; lean_object* v_snd_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4784_; 
v_val_4758_ = lean_ctor_get(v_a_4757_, 0);
lean_inc(v_val_4758_);
lean_dec_ref_known(v_a_4757_, 1);
v_snd_4759_ = lean_ctor_get(v_val_4758_, 1);
v_isSharedCheck_4784_ = !lean_is_exclusive(v_val_4758_);
if (v_isSharedCheck_4784_ == 0)
{
lean_object* v_unused_4785_; 
v_unused_4785_ = lean_ctor_get(v_val_4758_, 0);
lean_dec(v_unused_4785_);
v___x_4761_ = v_val_4758_;
v_isShared_4762_ = v_isSharedCheck_4784_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_snd_4759_);
lean_dec(v_val_4758_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4784_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
if (lean_obj_tag(v_snd_4759_) == 1)
{
lean_object* v___x_4763_; 
lean_dec_ref_known(v_snd_4759_, 2);
v___x_4763_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4717_, v_a_4718_, v_mod_x3f_4724_, v___x_4733_, v___x_4719_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
if (lean_obj_tag(v___x_4763_) == 0)
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4775_; 
v_a_4764_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4766_ = v___x_4763_;
v_isShared_4767_ = v_isSharedCheck_4775_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4763_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4775_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4768_; lean_object* v___x_4770_; 
v___x_4768_ = lean_box(0);
if (v_isShared_4762_ == 0)
{
lean_ctor_set(v___x_4761_, 1, v_a_4764_);
lean_ctor_set(v___x_4761_, 0, v___x_4768_);
v___x_4770_ = v___x_4761_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4768_);
lean_ctor_set(v_reuseFailAlloc_4774_, 1, v_a_4764_);
v___x_4770_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
lean_object* v___x_4772_; 
if (v_isShared_4767_ == 0)
{
lean_ctor_set(v___x_4766_, 0, v___x_4770_);
v___x_4772_ = v___x_4766_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4770_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
}
else
{
lean_object* v_a_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4783_; 
lean_del_object(v___x_4761_);
v_a_4776_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4783_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4783_ == 0)
{
v___x_4778_ = v___x_4763_;
v_isShared_4779_ = v_isSharedCheck_4783_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_a_4776_);
lean_dec(v___x_4763_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4783_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4781_; 
if (v_isShared_4779_ == 0)
{
v___x_4781_ = v___x_4778_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_a_4776_);
v___x_4781_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
return v___x_4781_;
}
}
}
}
else
{
lean_del_object(v___x_4761_);
lean_dec(v_snd_4759_);
goto v___jp_4734_;
}
}
}
else
{
lean_dec(v_a_4757_);
goto v___jp_4734_;
}
}
else
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4793_; 
lean_dec(v___x_4733_);
lean_dec(v_mod_x3f_4724_);
lean_dec(v_a_4718_);
lean_dec_ref(v_b_4717_);
v_a_4786_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4788_ = v___x_4756_;
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4756_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4815_, lean_object* v_b_4816_, lean_object* v_a_4817_, lean_object* v___x_4818_, lean_object* v_only_4819_, lean_object* v_incremental_4820_, lean_object* v___x_4821_, lean_object* v_x_4822_, lean_object* v_mod_x3f_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_){
_start:
{
uint8_t v___x_18001__boxed_4831_; uint8_t v_only_boxed_4832_; uint8_t v_incremental_boxed_4833_; uint8_t v___x_18002__boxed_4834_; lean_object* v_res_4835_; 
v___x_18001__boxed_4831_ = lean_unbox(v___x_4818_);
v_only_boxed_4832_ = lean_unbox(v_only_4819_);
v_incremental_boxed_4833_ = lean_unbox(v_incremental_4820_);
v___x_18002__boxed_4834_ = lean_unbox(v___x_4821_);
v_res_4835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4815_, v_b_4816_, v_a_4817_, v___x_18001__boxed_4831_, v_only_boxed_4832_, v_incremental_boxed_4833_, v___x_18002__boxed_4834_, v_x_4822_, v_mod_x3f_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
lean_dec(v___x_4815_);
return v_res_4835_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4844_ = l_Lean_stringToMessageData(v___x_4843_);
return v___x_4844_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13(void){
_start:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; 
v___x_4870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12));
v___x_4871_ = l_Lean_stringToMessageData(v___x_4870_);
return v___x_4871_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4877_ = l_Lean_stringToMessageData(v___x_4876_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4878_, uint8_t v_only_4879_, uint8_t v_incremental_4880_, lean_object* v_as_4881_, size_t v_sz_4882_, size_t v_i_4883_, lean_object* v_b_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_){
_start:
{
lean_object* v_snd_4893_; lean_object* v___y_4898_; uint8_t v___y_4899_; lean_object* v_a_4903_; lean_object* v___y_4907_; uint8_t v___x_4911_; 
v___x_4911_ = lean_usize_dec_lt(v_i_4883_, v_sz_4882_);
if (v___x_4911_ == 0)
{
lean_object* v___x_4912_; 
v___x_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4912_, 0, v_b_4884_);
return v___x_4912_;
}
else
{
lean_object* v_a_4913_; lean_object* v___x_4914_; uint8_t v___x_4915_; 
v_a_4913_ = lean_array_uget_borrowed(v_as_4881_, v_i_4883_);
v___x_4914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_4913_);
v___x_4915_ = l_Lean_Syntax_isOfKind(v_a_4913_, v___x_4914_);
if (v___x_4915_ == 0)
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4916_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4913_);
v___x_4917_ = l_Lean_MessageData_ofSyntax(v_a_4913_);
v___x_4918_ = l_Lean_indentD(v___x_4917_);
v___x_4919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4916_);
lean_ctor_set(v___x_4919_, 1, v___x_4918_);
v___x_4920_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4919_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_dec_ref_known(v___x_4920_, 1);
v_snd_4893_ = v_b_4884_;
goto v___jp_4892_;
}
else
{
lean_object* v_a_4921_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref_known(v___x_4920_, 1);
v_a_4903_ = v_a_4921_;
goto v___jp_4902_;
}
}
else
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; uint8_t v___x_4925_; 
v___x_4922_ = lean_unsigned_to_nat(0u);
v___x_4923_ = l_Lean_Syntax_getArg(v_a_4913_, v___x_4922_);
v___x_4924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_4923_);
v___x_4925_ = l_Lean_Syntax_isOfKind(v___x_4923_, v___x_4924_);
if (v___x_4925_ == 0)
{
lean_object* v___x_4926_; uint8_t v___x_4927_; 
v___x_4926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_4923_);
v___x_4927_ = l_Lean_Syntax_isOfKind(v___x_4923_, v___x_4926_);
if (v___x_4927_ == 0)
{
lean_object* v___x_4928_; uint8_t v___x_4929_; 
v___x_4928_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_4923_);
v___x_4929_ = l_Lean_Syntax_isOfKind(v___x_4923_, v___x_4928_);
if (v___x_4929_ == 0)
{
lean_object* v___x_4930_; uint8_t v___x_4931_; 
v___x_4930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_4923_);
v___x_4931_ = l_Lean_Syntax_isOfKind(v___x_4923_, v___x_4930_);
if (v___x_4931_ == 0)
{
lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
lean_dec(v___x_4923_);
v___x_4932_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4913_);
v___x_4933_ = l_Lean_MessageData_ofSyntax(v_a_4913_);
v___x_4934_ = l_Lean_indentD(v___x_4933_);
v___x_4935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4932_);
lean_ctor_set(v___x_4935_, 1, v___x_4934_);
v___x_4936_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4935_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_dec_ref_known(v___x_4936_, 1);
v_snd_4893_ = v_b_4884_;
goto v___jp_4892_;
}
else
{
lean_object* v_a_4937_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
lean_inc(v_a_4937_);
lean_dec_ref_known(v___x_4936_, 1);
v_a_4903_ = v_a_4937_;
goto v___jp_4902_;
}
}
else
{
lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4938_ = lean_unsigned_to_nat(1u);
v___x_4939_ = l_Lean_Syntax_getArg(v___x_4923_, v___x_4938_);
lean_dec(v___x_4923_);
if (v___x_4929_ == 0)
{
lean_object* v___x_4948_; uint8_t v___x_4949_; 
v___x_4948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15));
lean_inc(v___x_4939_);
v___x_4949_ = l_Lean_Syntax_isOfKind(v___x_4939_, v___x_4948_);
if (v___x_4949_ == 0)
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
lean_dec(v___x_4939_);
v___x_4950_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4913_);
v___x_4951_ = l_Lean_MessageData_ofSyntax(v_a_4913_);
v___x_4952_ = l_Lean_indentD(v___x_4951_);
v___x_4953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4953_, 0, v___x_4950_);
lean_ctor_set(v___x_4953_, 1, v___x_4952_);
v___x_4954_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4953_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_dec_ref_known(v___x_4954_, 1);
v_snd_4893_ = v_b_4884_;
goto v___jp_4892_;
}
else
{
lean_object* v_a_4955_; 
v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_a_4955_);
lean_dec_ref_known(v___x_4954_, 1);
v_a_4903_ = v_a_4955_;
goto v___jp_4902_;
}
}
else
{
goto v___jp_4940_;
}
}
else
{
goto v___jp_4940_;
}
v___jp_4940_:
{
if (v_only_4879_ == 0)
{
lean_object* v___x_4941_; lean_object* v___x_4942_; 
v___x_4941_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13);
v___x_4942_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_4939_, v___x_4941_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
if (lean_obj_tag(v___x_4942_) == 0)
{
lean_object* v_a_4943_; lean_object* v___x_4944_; 
v_a_4943_ = lean_ctor_get(v___x_4942_, 0);
lean_inc(v_a_4943_);
lean_dec_ref_known(v___x_4942_, 1);
lean_inc_ref(v_b_4884_);
v___x_4944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4884_, v___x_4939_, v_a_4943_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
lean_dec(v___x_4939_);
v___y_4907_ = v___x_4944_;
goto v___jp_4906_;
}
else
{
lean_object* v_a_4945_; 
lean_dec(v___x_4939_);
v_a_4945_ = lean_ctor_get(v___x_4942_, 0);
lean_inc(v_a_4945_);
lean_dec_ref_known(v___x_4942_, 1);
v_a_4903_ = v_a_4945_;
goto v___jp_4902_;
}
}
else
{
lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4946_ = lean_box(0);
lean_inc_ref(v_b_4884_);
v___x_4947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4884_, v___x_4939_, v___x_4946_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
lean_dec(v___x_4939_);
v___y_4907_ = v___x_4947_;
goto v___jp_4906_;
}
}
}
}
else
{
lean_object* v___x_4956_; lean_object* v___x_4957_; uint8_t v___x_4958_; 
v___x_4956_ = lean_unsigned_to_nat(1u);
v___x_4957_ = l_Lean_Syntax_getArg(v___x_4923_, v___x_4956_);
v___x_4958_ = l_Lean_Syntax_isNone(v___x_4957_);
if (v___x_4958_ == 0)
{
uint8_t v___x_4959_; 
lean_inc(v___x_4957_);
v___x_4959_ = l_Lean_Syntax_matchesNull(v___x_4957_, v___x_4956_);
if (v___x_4959_ == 0)
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
lean_dec(v___x_4957_);
lean_dec(v___x_4923_);
v___x_4960_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4913_);
v___x_4961_ = l_Lean_MessageData_ofSyntax(v_a_4913_);
v___x_4962_ = l_Lean_indentD(v___x_4961_);
v___x_4963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4963_, 0, v___x_4960_);
lean_ctor_set(v___x_4963_, 1, v___x_4962_);
v___x_4964_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4963_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_dec_ref_known(v___x_4964_, 1);
v_snd_4893_ = v_b_4884_;
goto v___jp_4892_;
}
else
{
lean_object* v_a_4965_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_a_4965_);
lean_dec_ref_known(v___x_4964_, 1);
v_a_4903_ = v_a_4965_;
goto v___jp_4902_;
}
}
else
{
lean_object* v___x_4966_; 
v___x_4966_ = l_Lean_Syntax_getArg(v___x_4957_, v___x_4922_);
lean_dec(v___x_4957_);
if (v___x_4958_ == 0)
{
lean_object* v___x_4971_; uint8_t v___x_4972_; 
v___x_4971_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4966_);
v___x_4972_ = l_Lean_Syntax_isOfKind(v___x_4966_, v___x_4971_);
if (v___x_4972_ == 0)
{
lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
lean_dec(v___x_4966_);
lean_dec(v___x_4923_);
v___x_4973_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4913_);
v___x_4974_ = l_Lean_MessageData_ofSyntax(v_a_4913_);
v___x_4975_ = l_Lean_indentD(v___x_4974_);
v___x_4976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4973_);
lean_ctor_set(v___x_4976_, 1, v___x_4975_);
v___x_4977_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4976_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_dec_ref_known(v___x_4977_, 1);
v_snd_4893_ = v_b_4884_;
goto v___jp_4892_;
}
else
{
lean_object* v_a_4978_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_a_4978_);
lean_dec_ref_known(v___x_4977_, 1);
v_a_4903_ = v_a_4978_;
goto v___jp_4902_;
}
}
else
{
goto v___jp_4967_;
}
}
else
{
goto v___jp_4967_;
}
v___jp_4967_:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4968_ = lean_box(0);
v___x_4969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4966_);
lean_inc(v_a_4913_);
lean_inc_ref(v_b_4884_);
v___x_4970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4923_, v_b_4884_, v_a_4913_, v___x_4915_, v_only_4879_, v_incremental_4880_, v___x_4927_, v___x_4968_, v___x_4969_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
lean_dec(v___x_4923_);
v___y_4907_ = v___x_4970_;
goto v___jp_4906_;
}
}
}
else
{
lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
lean_dec(v___x_4957_);
v___x_4979_ = lean_box(0);
v___x_4980_ = lean_box(0);
lean_inc(v_a_4913_);
lean_inc_ref(v_b_4884_);
v___x_4981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4923_, v_b_4884_, v_a_4913_, v___x_4915_, v_only_4879_, v_incremental_4880_, v___x_4927_, v___x_4979_, v___x_4980_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
lean_dec(v___x_4923_);
v___y_4907_ = v___x_4981_;
goto v___jp_4906_;
}
}
}
else
{
lean_object* v___x_4982_; uint8_t v___x_4983_; 
v___x_4982_ = l_Lean_Syntax_getArg(v___x_4923_, v___x_4922_);
v___x_4983_ = l_Lean_Syntax_isNone(v___x_4982_);
if (v___x_4983_ == 0)
{
lean_object* v___x_4984_; uint8_t v___x_4985_; 
v___x_4984_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4982_);
v___x_4985_ = l_Lean_Syntax_matchesNull(v___x_4982_, v___x_4984_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
lean_dec(v___x_4982_);
lean_dec(v___x_4923_);
v___x_4986_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4913_);
v___x_4987_ = l_Lean_MessageData_ofSyntax(v_a_4913_);
v___x_4988_ = l_Lean_indentD(v___x_4987_);
v___x_4989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4989_, 0, v___x_4986_);
lean_ctor_set(v___x_4989_, 1, v___x_4988_);
v___x_4990_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4989_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_dec_ref_known(v___x_4990_, 1);
v_snd_4893_ = v_b_4884_;
goto v___jp_4892_;
}
else
{
lean_object* v_a_4991_; 
v_a_4991_ = lean_ctor_get(v___x_4990_, 0);
lean_inc(v_a_4991_);
lean_dec_ref_known(v___x_4990_, 1);
v_a_4903_ = v_a_4991_;
goto v___jp_4902_;
}
}
else
{
lean_object* v___x_4992_; 
v___x_4992_ = l_Lean_Syntax_getArg(v___x_4982_, v___x_4922_);
lean_dec(v___x_4982_);
if (v___x_4983_ == 0)
{
lean_object* v___x_4997_; uint8_t v___x_4998_; 
v___x_4997_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4992_);
v___x_4998_ = l_Lean_Syntax_isOfKind(v___x_4992_, v___x_4997_);
if (v___x_4998_ == 0)
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
lean_dec(v___x_4992_);
lean_dec(v___x_4923_);
v___x_4999_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4913_);
v___x_5000_ = l_Lean_MessageData_ofSyntax(v_a_4913_);
v___x_5001_ = l_Lean_indentD(v___x_5000_);
v___x_5002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5002_, 0, v___x_4999_);
lean_ctor_set(v___x_5002_, 1, v___x_5001_);
v___x_5003_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5002_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_dec_ref_known(v___x_5003_, 1);
v_snd_4893_ = v_b_4884_;
goto v___jp_4892_;
}
else
{
lean_object* v_a_5004_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc(v_a_5004_);
lean_dec_ref_known(v___x_5003_, 1);
v_a_4903_ = v_a_5004_;
goto v___jp_4902_;
}
}
else
{
goto v___jp_4993_;
}
}
else
{
goto v___jp_4993_;
}
v___jp_4993_:
{
lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4994_ = lean_box(0);
v___x_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4992_);
lean_inc(v_a_4913_);
lean_inc_ref(v_b_4884_);
v___x_4996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4923_, v_b_4884_, v_a_4913_, v___x_4925_, v_only_4879_, v_incremental_4880_, v___x_4994_, v___x_4995_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
lean_dec(v___x_4923_);
v___y_4907_ = v___x_4996_;
goto v___jp_4906_;
}
}
}
else
{
lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; 
lean_dec(v___x_4982_);
v___x_5005_ = lean_box(0);
v___x_5006_ = lean_box(0);
lean_inc(v_a_4913_);
lean_inc_ref(v_b_4884_);
v___x_5007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4923_, v_b_4884_, v_a_4913_, v___x_4925_, v_only_4879_, v_incremental_4880_, v___x_5005_, v___x_5006_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
lean_dec(v___x_4923_);
v___y_4907_ = v___x_5007_;
goto v___jp_4906_;
}
}
}
else
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; uint8_t v___x_5011_; 
v___x_5008_ = lean_unsigned_to_nat(1u);
v___x_5009_ = l_Lean_Syntax_getArg(v___x_4923_, v___x_5008_);
lean_dec(v___x_4923_);
v___x_5010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_5009_);
v___x_5011_ = l_Lean_Syntax_isOfKind(v___x_5009_, v___x_5010_);
if (v___x_5011_ == 0)
{
lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
lean_dec(v___x_5009_);
v___x_5012_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4913_);
v___x_5013_ = l_Lean_MessageData_ofSyntax(v_a_4913_);
v___x_5014_ = l_Lean_indentD(v___x_5013_);
v___x_5015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5015_, 0, v___x_5012_);
lean_ctor_set(v___x_5015_, 1, v___x_5014_);
v___x_5016_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5015_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_dec_ref_known(v___x_5016_, 1);
v_snd_4893_ = v_b_4884_;
goto v___jp_4892_;
}
else
{
lean_object* v_a_5017_; 
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_a_5017_);
lean_dec_ref_known(v___x_5016_, 1);
v_a_4903_ = v_a_5017_;
goto v___jp_4902_;
}
}
else
{
if (v_incremental_4880_ == 0)
{
lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5018_ = lean_box(0);
lean_inc_ref(v_b_4884_);
v___x_5019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_5009_, v___x_4915_, v_b_4884_, v___x_5018_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
v___y_4907_ = v___x_5019_;
goto v___jp_4906_;
}
else
{
lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5020_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_5021_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_4913_, v___x_5020_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_a_5022_; lean_object* v___x_5023_; 
v_a_5022_ = lean_ctor_get(v___x_5021_, 0);
lean_inc(v_a_5022_);
lean_dec_ref_known(v___x_5021_, 1);
lean_inc_ref(v_b_4884_);
v___x_5023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_5009_, v___x_4915_, v_b_4884_, v_a_5022_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
v___y_4907_ = v___x_5023_;
goto v___jp_4906_;
}
else
{
lean_object* v_a_5024_; 
lean_dec(v___x_5009_);
v_a_5024_ = lean_ctor_get(v___x_5021_, 0);
lean_inc(v_a_5024_);
lean_dec_ref_known(v___x_5021_, 1);
v_a_4903_ = v_a_5024_;
goto v___jp_4902_;
}
}
}
}
}
}
v___jp_4892_:
{
size_t v___x_4894_; size_t v___x_4895_; 
v___x_4894_ = ((size_t)1ULL);
v___x_4895_ = lean_usize_add(v_i_4883_, v___x_4894_);
v_i_4883_ = v___x_4895_;
v_b_4884_ = v_snd_4893_;
goto _start;
}
v___jp_4897_:
{
if (v___y_4899_ == 0)
{
if (v_lax_4878_ == 0)
{
lean_object* v___x_4900_; 
lean_dec_ref(v_b_4884_);
v___x_4900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4900_, 0, v___y_4898_);
return v___x_4900_;
}
else
{
lean_dec_ref(v___y_4898_);
v_snd_4893_ = v_b_4884_;
goto v___jp_4892_;
}
}
else
{
lean_object* v___x_4901_; 
lean_dec_ref(v_b_4884_);
v___x_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4901_, 0, v___y_4898_);
return v___x_4901_;
}
}
v___jp_4902_:
{
uint8_t v___x_4904_; 
v___x_4904_ = l_Lean_Exception_isInterrupt(v_a_4903_);
if (v___x_4904_ == 0)
{
uint8_t v___x_4905_; 
lean_inc_ref(v_a_4903_);
v___x_4905_ = l_Lean_Exception_isRuntime(v_a_4903_);
v___y_4898_ = v_a_4903_;
v___y_4899_ = v___x_4905_;
goto v___jp_4897_;
}
else
{
v___y_4898_ = v_a_4903_;
v___y_4899_ = v___x_4904_;
goto v___jp_4897_;
}
}
v___jp_4906_:
{
if (lean_obj_tag(v___y_4907_) == 0)
{
lean_object* v_a_4908_; lean_object* v_snd_4909_; 
lean_dec_ref(v_b_4884_);
v_a_4908_ = lean_ctor_get(v___y_4907_, 0);
lean_inc(v_a_4908_);
lean_dec_ref_known(v___y_4907_, 1);
v_snd_4909_ = lean_ctor_get(v_a_4908_, 1);
lean_inc(v_snd_4909_);
lean_dec(v_a_4908_);
v_snd_4893_ = v_snd_4909_;
goto v___jp_4892_;
}
else
{
lean_object* v_a_4910_; 
v_a_4910_ = lean_ctor_get(v___y_4907_, 0);
lean_inc(v_a_4910_);
lean_dec_ref_known(v___y_4907_, 1);
v_a_4903_ = v_a_4910_;
goto v___jp_4902_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_5025_, lean_object* v_only_5026_, lean_object* v_incremental_5027_, lean_object* v_as_5028_, lean_object* v_sz_5029_, lean_object* v_i_5030_, lean_object* v_b_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_){
_start:
{
uint8_t v_lax_boxed_5039_; uint8_t v_only_boxed_5040_; uint8_t v_incremental_boxed_5041_; size_t v_sz_boxed_5042_; size_t v_i_boxed_5043_; lean_object* v_res_5044_; 
v_lax_boxed_5039_ = lean_unbox(v_lax_5025_);
v_only_boxed_5040_ = lean_unbox(v_only_5026_);
v_incremental_boxed_5041_ = lean_unbox(v_incremental_5027_);
v_sz_boxed_5042_ = lean_unbox_usize(v_sz_5029_);
lean_dec(v_sz_5029_);
v_i_boxed_5043_ = lean_unbox_usize(v_i_5030_);
lean_dec(v_i_5030_);
v_res_5044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_5039_, v_only_boxed_5040_, v_incremental_boxed_5041_, v_as_5028_, v_sz_boxed_5042_, v_i_boxed_5043_, v_b_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_);
lean_dec(v___y_5037_);
lean_dec_ref(v___y_5036_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec_ref(v_as_5028_);
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_5045_, lean_object* v_ps_5046_, uint8_t v_only_5047_, uint8_t v_lax_5048_, uint8_t v_incremental_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_){
_start:
{
size_t v_sz_5057_; size_t v___x_5058_; lean_object* v___x_5059_; 
v_sz_5057_ = lean_array_size(v_ps_5046_);
v___x_5058_ = ((size_t)0ULL);
v___x_5059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_5048_, v_only_5047_, v_incremental_5049_, v_ps_5046_, v_sz_5057_, v___x_5058_, v_params_5045_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_5060_, lean_object* v_ps_5061_, lean_object* v_only_5062_, lean_object* v_lax_5063_, lean_object* v_incremental_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_){
_start:
{
uint8_t v_only_boxed_5072_; uint8_t v_lax_boxed_5073_; uint8_t v_incremental_boxed_5074_; lean_object* v_res_5075_; 
v_only_boxed_5072_ = lean_unbox(v_only_5062_);
v_lax_boxed_5073_ = lean_unbox(v_lax_5063_);
v_incremental_boxed_5074_ = lean_unbox(v_incremental_5064_);
v_res_5075_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5060_, v_ps_5061_, v_only_boxed_5072_, v_lax_boxed_5073_, v_incremental_boxed_5074_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
lean_dec(v_a_5070_);
lean_dec_ref(v_a_5069_);
lean_dec(v_a_5068_);
lean_dec_ref(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
lean_dec_ref(v_ps_5061_);
return v_res_5075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_){
_start:
{
lean_object* v_origin_5087_; 
v_origin_5087_ = lean_ctor_get(v_thm_5076_, 5);
if (lean_obj_tag(v_origin_5087_) == 0)
{
lean_object* v_declName_5088_; lean_object* v___x_5089_; 
lean_inc_ref(v_origin_5087_);
lean_dec_ref(v_thm_5076_);
v_declName_5088_ = lean_ctor_get(v_origin_5087_, 0);
lean_inc(v_declName_5088_);
lean_dec_ref_known(v_origin_5087_, 1);
v___x_5089_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_5088_, v_a_5084_, v_a_5085_);
return v___x_5089_;
}
else
{
lean_object* v_proof_5090_; lean_object* v___x_5091_; 
v_proof_5090_ = lean_ctor_get(v_thm_5076_, 1);
lean_inc_ref(v_proof_5090_);
lean_dec_ref(v_thm_5076_);
v___x_5091_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_5090_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_);
return v___x_5091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_){
_start:
{
lean_object* v_res_5103_; 
v_res_5103_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_5092_, v_a_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec_ref(v_a_5094_);
lean_dec(v_a_5093_);
return v_res_5103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_5104_, size_t v_sz_5105_, size_t v_i_5106_, lean_object* v_b_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
uint8_t v___x_5118_; 
v___x_5118_ = lean_usize_dec_lt(v_i_5106_, v_sz_5105_);
if (v___x_5118_ == 0)
{
lean_object* v___x_5119_; 
v___x_5119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5119_, 0, v_b_5107_);
return v___x_5119_;
}
else
{
lean_object* v_snd_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5146_; 
v_snd_5120_ = lean_ctor_get(v_b_5107_, 1);
v_isSharedCheck_5146_ = !lean_is_exclusive(v_b_5107_);
if (v_isSharedCheck_5146_ == 0)
{
lean_object* v_unused_5147_; 
v_unused_5147_ = lean_ctor_get(v_b_5107_, 0);
lean_dec(v_unused_5147_);
v___x_5122_ = v_b_5107_;
v_isShared_5123_ = v_isSharedCheck_5146_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_snd_5120_);
lean_dec(v_b_5107_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5146_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v___x_5124_; lean_object* v_a_5126_; lean_object* v_a_5133_; lean_object* v___x_5134_; 
v___x_5124_ = lean_box(0);
v_a_5133_ = lean_array_uget_borrowed(v_as_5104_, v_i_5106_);
lean_inc(v_a_5133_);
v___x_5134_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5133_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; uint8_t v___x_5136_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5134_, 1);
v___x_5136_ = lean_unbox(v_a_5135_);
lean_dec(v_a_5135_);
if (v___x_5136_ == 0)
{
v_a_5126_ = v_snd_5120_;
goto v___jp_5125_;
}
else
{
lean_object* v___x_5137_; 
lean_inc(v_a_5133_);
v___x_5137_ = l_Lean_PersistentArray_push___redArg(v_snd_5120_, v_a_5133_);
v_a_5126_ = v___x_5137_;
goto v___jp_5125_;
}
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5145_; 
lean_del_object(v___x_5122_);
lean_dec(v_snd_5120_);
v_a_5138_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5140_ = v___x_5134_;
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v___x_5134_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5143_; 
if (v_isShared_5141_ == 0)
{
v___x_5143_ = v___x_5140_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
v___jp_5125_:
{
lean_object* v___x_5128_; 
if (v_isShared_5123_ == 0)
{
lean_ctor_set(v___x_5122_, 1, v_a_5126_);
lean_ctor_set(v___x_5122_, 0, v___x_5124_);
v___x_5128_ = v___x_5122_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v___x_5124_);
lean_ctor_set(v_reuseFailAlloc_5132_, 1, v_a_5126_);
v___x_5128_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
size_t v___x_5129_; size_t v___x_5130_; 
v___x_5129_ = ((size_t)1ULL);
v___x_5130_ = lean_usize_add(v_i_5106_, v___x_5129_);
v_i_5106_ = v___x_5130_;
v_b_5107_ = v___x_5128_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5148_, lean_object* v_sz_5149_, lean_object* v_i_5150_, lean_object* v_b_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_){
_start:
{
size_t v_sz_boxed_5162_; size_t v_i_boxed_5163_; lean_object* v_res_5164_; 
v_sz_boxed_5162_ = lean_unbox_usize(v_sz_5149_);
lean_dec(v_sz_5149_);
v_i_boxed_5163_ = lean_unbox_usize(v_i_5150_);
lean_dec(v_i_5150_);
v_res_5164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5148_, v_sz_boxed_5162_, v_i_boxed_5163_, v_b_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
lean_dec(v___y_5160_);
lean_dec_ref(v___y_5159_);
lean_dec(v___y_5158_);
lean_dec_ref(v___y_5157_);
lean_dec(v___y_5156_);
lean_dec_ref(v___y_5155_);
lean_dec(v___y_5154_);
lean_dec_ref(v___y_5153_);
lean_dec(v___y_5152_);
lean_dec_ref(v_as_5148_);
return v_res_5164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5165_, size_t v_sz_5166_, size_t v_i_5167_, lean_object* v_b_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_){
_start:
{
uint8_t v___x_5179_; 
v___x_5179_ = lean_usize_dec_lt(v_i_5167_, v_sz_5166_);
if (v___x_5179_ == 0)
{
lean_object* v___x_5180_; 
v___x_5180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5180_, 0, v_b_5168_);
return v___x_5180_;
}
else
{
lean_object* v_snd_5181_; lean_object* v___x_5183_; uint8_t v_isShared_5184_; uint8_t v_isSharedCheck_5207_; 
v_snd_5181_ = lean_ctor_get(v_b_5168_, 1);
v_isSharedCheck_5207_ = !lean_is_exclusive(v_b_5168_);
if (v_isSharedCheck_5207_ == 0)
{
lean_object* v_unused_5208_; 
v_unused_5208_ = lean_ctor_get(v_b_5168_, 0);
lean_dec(v_unused_5208_);
v___x_5183_ = v_b_5168_;
v_isShared_5184_ = v_isSharedCheck_5207_;
goto v_resetjp_5182_;
}
else
{
lean_inc(v_snd_5181_);
lean_dec(v_b_5168_);
v___x_5183_ = lean_box(0);
v_isShared_5184_ = v_isSharedCheck_5207_;
goto v_resetjp_5182_;
}
v_resetjp_5182_:
{
lean_object* v___x_5185_; lean_object* v_a_5187_; lean_object* v_a_5194_; lean_object* v___x_5195_; 
v___x_5185_ = lean_box(0);
v_a_5194_ = lean_array_uget_borrowed(v_as_5165_, v_i_5167_);
lean_inc(v_a_5194_);
v___x_5195_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5194_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
if (lean_obj_tag(v___x_5195_) == 0)
{
lean_object* v_a_5196_; uint8_t v___x_5197_; 
v_a_5196_ = lean_ctor_get(v___x_5195_, 0);
lean_inc(v_a_5196_);
lean_dec_ref_known(v___x_5195_, 1);
v___x_5197_ = lean_unbox(v_a_5196_);
lean_dec(v_a_5196_);
if (v___x_5197_ == 0)
{
v_a_5187_ = v_snd_5181_;
goto v___jp_5186_;
}
else
{
lean_object* v___x_5198_; 
lean_inc(v_a_5194_);
v___x_5198_ = l_Lean_PersistentArray_push___redArg(v_snd_5181_, v_a_5194_);
v_a_5187_ = v___x_5198_;
goto v___jp_5186_;
}
}
else
{
lean_object* v_a_5199_; lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5206_; 
lean_del_object(v___x_5183_);
lean_dec(v_snd_5181_);
v_a_5199_ = lean_ctor_get(v___x_5195_, 0);
v_isSharedCheck_5206_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5206_ == 0)
{
v___x_5201_ = v___x_5195_;
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
else
{
lean_inc(v_a_5199_);
lean_dec(v___x_5195_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
lean_object* v___x_5204_; 
if (v_isShared_5202_ == 0)
{
v___x_5204_ = v___x_5201_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_a_5199_);
v___x_5204_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
return v___x_5204_;
}
}
}
v___jp_5186_:
{
lean_object* v___x_5189_; 
if (v_isShared_5184_ == 0)
{
lean_ctor_set(v___x_5183_, 1, v_a_5187_);
lean_ctor_set(v___x_5183_, 0, v___x_5185_);
v___x_5189_ = v___x_5183_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v___x_5185_);
lean_ctor_set(v_reuseFailAlloc_5193_, 1, v_a_5187_);
v___x_5189_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
size_t v___x_5190_; size_t v___x_5191_; lean_object* v___x_5192_; 
v___x_5190_ = ((size_t)1ULL);
v___x_5191_ = lean_usize_add(v_i_5167_, v___x_5190_);
v___x_5192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5165_, v_sz_5166_, v___x_5191_, v___x_5189_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
return v___x_5192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5209_, lean_object* v_sz_5210_, lean_object* v_i_5211_, lean_object* v_b_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
size_t v_sz_boxed_5223_; size_t v_i_boxed_5224_; lean_object* v_res_5225_; 
v_sz_boxed_5223_ = lean_unbox_usize(v_sz_5210_);
lean_dec(v_sz_5210_);
v_i_boxed_5224_ = lean_unbox_usize(v_i_5211_);
lean_dec(v_i_5211_);
v_res_5225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5209_, v_sz_boxed_5223_, v_i_boxed_5224_, v_b_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_, v___y_5220_, v___y_5221_);
lean_dec(v___y_5221_);
lean_dec_ref(v___y_5220_);
lean_dec(v___y_5219_);
lean_dec_ref(v___y_5218_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v_as_5209_);
return v_res_5225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5226_, size_t v_sz_5227_, size_t v_i_5228_, lean_object* v_b_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_){
_start:
{
uint8_t v___x_5240_; 
v___x_5240_ = lean_usize_dec_lt(v_i_5228_, v_sz_5227_);
if (v___x_5240_ == 0)
{
lean_object* v___x_5241_; 
v___x_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5241_, 0, v_b_5229_);
return v___x_5241_;
}
else
{
lean_object* v_snd_5242_; lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5268_; 
v_snd_5242_ = lean_ctor_get(v_b_5229_, 1);
v_isSharedCheck_5268_ = !lean_is_exclusive(v_b_5229_);
if (v_isSharedCheck_5268_ == 0)
{
lean_object* v_unused_5269_; 
v_unused_5269_ = lean_ctor_get(v_b_5229_, 0);
lean_dec(v_unused_5269_);
v___x_5244_ = v_b_5229_;
v_isShared_5245_ = v_isSharedCheck_5268_;
goto v_resetjp_5243_;
}
else
{
lean_inc(v_snd_5242_);
lean_dec(v_b_5229_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5268_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5246_; lean_object* v_a_5248_; lean_object* v_a_5255_; lean_object* v___x_5256_; 
v___x_5246_ = lean_box(0);
v_a_5255_ = lean_array_uget_borrowed(v_as_5226_, v_i_5228_);
lean_inc(v_a_5255_);
v___x_5256_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5255_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_);
if (lean_obj_tag(v___x_5256_) == 0)
{
lean_object* v_a_5257_; uint8_t v___x_5258_; 
v_a_5257_ = lean_ctor_get(v___x_5256_, 0);
lean_inc(v_a_5257_);
lean_dec_ref_known(v___x_5256_, 1);
v___x_5258_ = lean_unbox(v_a_5257_);
lean_dec(v_a_5257_);
if (v___x_5258_ == 0)
{
v_a_5248_ = v_snd_5242_;
goto v___jp_5247_;
}
else
{
lean_object* v___x_5259_; 
lean_inc(v_a_5255_);
v___x_5259_ = l_Lean_PersistentArray_push___redArg(v_snd_5242_, v_a_5255_);
v_a_5248_ = v___x_5259_;
goto v___jp_5247_;
}
}
else
{
lean_object* v_a_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5267_; 
lean_del_object(v___x_5244_);
lean_dec(v_snd_5242_);
v_a_5260_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5262_ = v___x_5256_;
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_a_5260_);
lean_dec(v___x_5256_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5265_; 
if (v_isShared_5263_ == 0)
{
v___x_5265_ = v___x_5262_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
}
v___jp_5247_:
{
lean_object* v___x_5250_; 
if (v_isShared_5245_ == 0)
{
lean_ctor_set(v___x_5244_, 1, v_a_5248_);
lean_ctor_set(v___x_5244_, 0, v___x_5246_);
v___x_5250_ = v___x_5244_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5246_);
lean_ctor_set(v_reuseFailAlloc_5254_, 1, v_a_5248_);
v___x_5250_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
size_t v___x_5251_; size_t v___x_5252_; 
v___x_5251_ = ((size_t)1ULL);
v___x_5252_ = lean_usize_add(v_i_5228_, v___x_5251_);
v_i_5228_ = v___x_5252_;
v_b_5229_ = v___x_5250_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5270_, lean_object* v_sz_5271_, lean_object* v_i_5272_, lean_object* v_b_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_){
_start:
{
size_t v_sz_boxed_5284_; size_t v_i_boxed_5285_; lean_object* v_res_5286_; 
v_sz_boxed_5284_ = lean_unbox_usize(v_sz_5271_);
lean_dec(v_sz_5271_);
v_i_boxed_5285_ = lean_unbox_usize(v_i_5272_);
lean_dec(v_i_5272_);
v_res_5286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5270_, v_sz_boxed_5284_, v_i_boxed_5285_, v_b_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_);
lean_dec(v___y_5282_);
lean_dec_ref(v___y_5281_);
lean_dec(v___y_5280_);
lean_dec_ref(v___y_5279_);
lean_dec(v___y_5278_);
lean_dec_ref(v___y_5277_);
lean_dec(v___y_5276_);
lean_dec_ref(v___y_5275_);
lean_dec(v___y_5274_);
lean_dec_ref(v_as_5270_);
return v_res_5286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5287_, size_t v_sz_5288_, size_t v_i_5289_, lean_object* v_b_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_){
_start:
{
uint8_t v___x_5301_; 
v___x_5301_ = lean_usize_dec_lt(v_i_5289_, v_sz_5288_);
if (v___x_5301_ == 0)
{
lean_object* v___x_5302_; 
v___x_5302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5302_, 0, v_b_5290_);
return v___x_5302_;
}
else
{
lean_object* v_snd_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5329_; 
v_snd_5303_ = lean_ctor_get(v_b_5290_, 1);
v_isSharedCheck_5329_ = !lean_is_exclusive(v_b_5290_);
if (v_isSharedCheck_5329_ == 0)
{
lean_object* v_unused_5330_; 
v_unused_5330_ = lean_ctor_get(v_b_5290_, 0);
lean_dec(v_unused_5330_);
v___x_5305_ = v_b_5290_;
v_isShared_5306_ = v_isSharedCheck_5329_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_snd_5303_);
lean_dec(v_b_5290_);
v___x_5305_ = lean_box(0);
v_isShared_5306_ = v_isSharedCheck_5329_;
goto v_resetjp_5304_;
}
v_resetjp_5304_:
{
lean_object* v___x_5307_; lean_object* v_a_5309_; lean_object* v_a_5316_; lean_object* v___x_5317_; 
v___x_5307_ = lean_box(0);
v_a_5316_ = lean_array_uget_borrowed(v_as_5287_, v_i_5289_);
lean_inc(v_a_5316_);
v___x_5317_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5316_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_);
if (lean_obj_tag(v___x_5317_) == 0)
{
lean_object* v_a_5318_; uint8_t v___x_5319_; 
v_a_5318_ = lean_ctor_get(v___x_5317_, 0);
lean_inc(v_a_5318_);
lean_dec_ref_known(v___x_5317_, 1);
v___x_5319_ = lean_unbox(v_a_5318_);
lean_dec(v_a_5318_);
if (v___x_5319_ == 0)
{
v_a_5309_ = v_snd_5303_;
goto v___jp_5308_;
}
else
{
lean_object* v___x_5320_; 
lean_inc(v_a_5316_);
v___x_5320_ = l_Lean_PersistentArray_push___redArg(v_snd_5303_, v_a_5316_);
v_a_5309_ = v___x_5320_;
goto v___jp_5308_;
}
}
else
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5328_; 
lean_del_object(v___x_5305_);
lean_dec(v_snd_5303_);
v_a_5321_ = lean_ctor_get(v___x_5317_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5323_ = v___x_5317_;
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5317_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5326_; 
if (v_isShared_5324_ == 0)
{
v___x_5326_ = v___x_5323_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5321_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
v___jp_5308_:
{
lean_object* v___x_5311_; 
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 1, v_a_5309_);
lean_ctor_set(v___x_5305_, 0, v___x_5307_);
v___x_5311_ = v___x_5305_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5315_; 
v_reuseFailAlloc_5315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5307_);
lean_ctor_set(v_reuseFailAlloc_5315_, 1, v_a_5309_);
v___x_5311_ = v_reuseFailAlloc_5315_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
size_t v___x_5312_; size_t v___x_5313_; lean_object* v___x_5314_; 
v___x_5312_ = ((size_t)1ULL);
v___x_5313_ = lean_usize_add(v_i_5289_, v___x_5312_);
v___x_5314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5287_, v_sz_5288_, v___x_5313_, v___x_5311_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_);
return v___x_5314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5331_, lean_object* v_sz_5332_, lean_object* v_i_5333_, lean_object* v_b_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_){
_start:
{
size_t v_sz_boxed_5345_; size_t v_i_boxed_5346_; lean_object* v_res_5347_; 
v_sz_boxed_5345_ = lean_unbox_usize(v_sz_5332_);
lean_dec(v_sz_5332_);
v_i_boxed_5346_ = lean_unbox_usize(v_i_5333_);
lean_dec(v_i_5333_);
v_res_5347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5331_, v_sz_boxed_5345_, v_i_boxed_5346_, v_b_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_);
lean_dec(v___y_5343_);
lean_dec_ref(v___y_5342_);
lean_dec(v___y_5341_);
lean_dec_ref(v___y_5340_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
lean_dec(v___y_5335_);
lean_dec_ref(v_as_5331_);
return v_res_5347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5348_, lean_object* v_n_5349_, lean_object* v_b_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_){
_start:
{
if (lean_obj_tag(v_n_5349_) == 0)
{
lean_object* v_cs_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; size_t v_sz_5364_; size_t v___x_5365_; lean_object* v___x_5366_; 
v_cs_5361_ = lean_ctor_get(v_n_5349_, 0);
v___x_5362_ = lean_box(0);
v___x_5363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5363_, 0, v___x_5362_);
lean_ctor_set(v___x_5363_, 1, v_b_5350_);
v_sz_5364_ = lean_array_size(v_cs_5361_);
v___x_5365_ = ((size_t)0ULL);
v___x_5366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5348_, v_cs_5361_, v_sz_5364_, v___x_5365_, v___x_5363_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
if (lean_obj_tag(v___x_5366_) == 0)
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5381_; 
v_a_5367_ = lean_ctor_get(v___x_5366_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5366_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5369_ = v___x_5366_;
v_isShared_5370_ = v_isSharedCheck_5381_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5366_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5381_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v_fst_5371_; 
v_fst_5371_ = lean_ctor_get(v_a_5367_, 0);
if (lean_obj_tag(v_fst_5371_) == 0)
{
lean_object* v_snd_5372_; lean_object* v___x_5373_; lean_object* v___x_5375_; 
v_snd_5372_ = lean_ctor_get(v_a_5367_, 1);
lean_inc(v_snd_5372_);
lean_dec(v_a_5367_);
v___x_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5373_, 0, v_snd_5372_);
if (v_isShared_5370_ == 0)
{
lean_ctor_set(v___x_5369_, 0, v___x_5373_);
v___x_5375_ = v___x_5369_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v___x_5373_);
v___x_5375_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5374_;
}
v_reusejp_5374_:
{
return v___x_5375_;
}
}
else
{
lean_object* v_val_5377_; lean_object* v___x_5379_; 
lean_inc_ref(v_fst_5371_);
lean_dec(v_a_5367_);
v_val_5377_ = lean_ctor_get(v_fst_5371_, 0);
lean_inc(v_val_5377_);
lean_dec_ref_known(v_fst_5371_, 1);
if (v_isShared_5370_ == 0)
{
lean_ctor_set(v___x_5369_, 0, v_val_5377_);
v___x_5379_ = v___x_5369_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_val_5377_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
}
else
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
v_a_5382_ = lean_ctor_get(v___x_5366_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5366_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v___x_5366_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5366_);
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
else
{
lean_object* v_vs_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; size_t v_sz_5393_; size_t v___x_5394_; lean_object* v___x_5395_; 
v_vs_5390_ = lean_ctor_get(v_n_5349_, 0);
v___x_5391_ = lean_box(0);
v___x_5392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5392_, 0, v___x_5391_);
lean_ctor_set(v___x_5392_, 1, v_b_5350_);
v_sz_5393_ = lean_array_size(v_vs_5390_);
v___x_5394_ = ((size_t)0ULL);
v___x_5395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5390_, v_sz_5393_, v___x_5394_, v___x_5392_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
if (lean_obj_tag(v___x_5395_) == 0)
{
lean_object* v_a_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5410_; 
v_a_5396_ = lean_ctor_get(v___x_5395_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5395_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5398_ = v___x_5395_;
v_isShared_5399_ = v_isSharedCheck_5410_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_a_5396_);
lean_dec(v___x_5395_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5410_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
lean_object* v_fst_5400_; 
v_fst_5400_ = lean_ctor_get(v_a_5396_, 0);
if (lean_obj_tag(v_fst_5400_) == 0)
{
lean_object* v_snd_5401_; lean_object* v___x_5402_; lean_object* v___x_5404_; 
v_snd_5401_ = lean_ctor_get(v_a_5396_, 1);
lean_inc(v_snd_5401_);
lean_dec(v_a_5396_);
v___x_5402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5402_, 0, v_snd_5401_);
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 0, v___x_5402_);
v___x_5404_ = v___x_5398_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v___x_5402_);
v___x_5404_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
return v___x_5404_;
}
}
else
{
lean_object* v_val_5406_; lean_object* v___x_5408_; 
lean_inc_ref(v_fst_5400_);
lean_dec(v_a_5396_);
v_val_5406_ = lean_ctor_get(v_fst_5400_, 0);
lean_inc(v_val_5406_);
lean_dec_ref_known(v_fst_5400_, 1);
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 0, v_val_5406_);
v___x_5408_ = v___x_5398_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_val_5406_);
v___x_5408_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
return v___x_5408_;
}
}
}
}
else
{
lean_object* v_a_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5418_; 
v_a_5411_ = lean_ctor_get(v___x_5395_, 0);
v_isSharedCheck_5418_ = !lean_is_exclusive(v___x_5395_);
if (v_isSharedCheck_5418_ == 0)
{
v___x_5413_ = v___x_5395_;
v_isShared_5414_ = v_isSharedCheck_5418_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_a_5411_);
lean_dec(v___x_5395_);
v___x_5413_ = lean_box(0);
v_isShared_5414_ = v_isSharedCheck_5418_;
goto v_resetjp_5412_;
}
v_resetjp_5412_:
{
lean_object* v___x_5416_; 
if (v_isShared_5414_ == 0)
{
v___x_5416_ = v___x_5413_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v_a_5411_);
v___x_5416_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
return v___x_5416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5419_, lean_object* v_as_5420_, size_t v_sz_5421_, size_t v_i_5422_, lean_object* v_b_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_){
_start:
{
uint8_t v___x_5434_; 
v___x_5434_ = lean_usize_dec_lt(v_i_5422_, v_sz_5421_);
if (v___x_5434_ == 0)
{
lean_object* v___x_5435_; 
v___x_5435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5435_, 0, v_b_5423_);
return v___x_5435_;
}
else
{
lean_object* v_snd_5436_; lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5470_; 
v_snd_5436_ = lean_ctor_get(v_b_5423_, 1);
v_isSharedCheck_5470_ = !lean_is_exclusive(v_b_5423_);
if (v_isSharedCheck_5470_ == 0)
{
lean_object* v_unused_5471_; 
v_unused_5471_ = lean_ctor_get(v_b_5423_, 0);
lean_dec(v_unused_5471_);
v___x_5438_ = v_b_5423_;
v_isShared_5439_ = v_isSharedCheck_5470_;
goto v_resetjp_5437_;
}
else
{
lean_inc(v_snd_5436_);
lean_dec(v_b_5423_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5470_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v___x_5440_; lean_object* v_a_5441_; lean_object* v___x_5442_; 
v___x_5440_ = lean_box(0);
v_a_5441_ = lean_array_uget_borrowed(v_as_5420_, v_i_5422_);
lean_inc(v_snd_5436_);
v___x_5442_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5419_, v_a_5441_, v_snd_5436_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_object* v_a_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5461_; 
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5461_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5461_ == 0)
{
v___x_5445_ = v___x_5442_;
v_isShared_5446_ = v_isSharedCheck_5461_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_a_5443_);
lean_dec(v___x_5442_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5461_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
if (lean_obj_tag(v_a_5443_) == 0)
{
lean_object* v___x_5447_; lean_object* v___x_5449_; 
v___x_5447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5447_, 0, v_a_5443_);
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 0, v___x_5447_);
v___x_5449_ = v___x_5438_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v___x_5447_);
lean_ctor_set(v_reuseFailAlloc_5453_, 1, v_snd_5436_);
v___x_5449_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
lean_object* v___x_5451_; 
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 0, v___x_5449_);
v___x_5451_ = v___x_5445_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v___x_5449_);
v___x_5451_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
return v___x_5451_;
}
}
}
else
{
lean_object* v_a_5454_; lean_object* v___x_5456_; 
lean_del_object(v___x_5445_);
lean_dec(v_snd_5436_);
v_a_5454_ = lean_ctor_get(v_a_5443_, 0);
lean_inc(v_a_5454_);
lean_dec_ref_known(v_a_5443_, 1);
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 1, v_a_5454_);
lean_ctor_set(v___x_5438_, 0, v___x_5440_);
v___x_5456_ = v___x_5438_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v___x_5440_);
lean_ctor_set(v_reuseFailAlloc_5460_, 1, v_a_5454_);
v___x_5456_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
size_t v___x_5457_; size_t v___x_5458_; 
v___x_5457_ = ((size_t)1ULL);
v___x_5458_ = lean_usize_add(v_i_5422_, v___x_5457_);
v_i_5422_ = v___x_5458_;
v_b_5423_ = v___x_5456_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5469_; 
lean_del_object(v___x_5438_);
lean_dec(v_snd_5436_);
v_a_5462_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5469_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5469_ == 0)
{
v___x_5464_ = v___x_5442_;
v_isShared_5465_ = v_isSharedCheck_5469_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_a_5462_);
lean_dec(v___x_5442_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5469_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5467_; 
if (v_isShared_5465_ == 0)
{
v___x_5467_ = v___x_5464_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5468_; 
v_reuseFailAlloc_5468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_a_5462_);
v___x_5467_ = v_reuseFailAlloc_5468_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
return v___x_5467_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5472_, lean_object* v_as_5473_, lean_object* v_sz_5474_, lean_object* v_i_5475_, lean_object* v_b_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_){
_start:
{
size_t v_sz_boxed_5487_; size_t v_i_boxed_5488_; lean_object* v_res_5489_; 
v_sz_boxed_5487_ = lean_unbox_usize(v_sz_5474_);
lean_dec(v_sz_5474_);
v_i_boxed_5488_ = lean_unbox_usize(v_i_5475_);
lean_dec(v_i_5475_);
v_res_5489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5472_, v_as_5473_, v_sz_boxed_5487_, v_i_boxed_5488_, v_b_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_);
lean_dec(v___y_5485_);
lean_dec_ref(v___y_5484_);
lean_dec(v___y_5483_);
lean_dec_ref(v___y_5482_);
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
lean_dec(v___y_5477_);
lean_dec_ref(v_as_5473_);
lean_dec_ref(v_init_5472_);
return v_res_5489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5490_, lean_object* v_n_5491_, lean_object* v_b_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_){
_start:
{
lean_object* v_res_5503_; 
v_res_5503_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5490_, v_n_5491_, v_b_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_);
lean_dec(v___y_5501_);
lean_dec_ref(v___y_5500_);
lean_dec(v___y_5499_);
lean_dec_ref(v___y_5498_);
lean_dec(v___y_5497_);
lean_dec_ref(v___y_5496_);
lean_dec(v___y_5495_);
lean_dec_ref(v___y_5494_);
lean_dec(v___y_5493_);
lean_dec_ref(v_n_5491_);
lean_dec_ref(v_init_5490_);
return v_res_5503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5504_, lean_object* v_init_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_){
_start:
{
lean_object* v_root_5516_; lean_object* v_tail_5517_; lean_object* v___x_5518_; 
v_root_5516_ = lean_ctor_get(v_t_5504_, 0);
v_tail_5517_ = lean_ctor_get(v_t_5504_, 1);
lean_inc_ref(v_init_5505_);
v___x_5518_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5505_, v_root_5516_, v_init_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_);
lean_dec_ref(v_init_5505_);
if (lean_obj_tag(v___x_5518_) == 0)
{
lean_object* v_a_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5555_; 
v_a_5519_ = lean_ctor_get(v___x_5518_, 0);
v_isSharedCheck_5555_ = !lean_is_exclusive(v___x_5518_);
if (v_isSharedCheck_5555_ == 0)
{
v___x_5521_ = v___x_5518_;
v_isShared_5522_ = v_isSharedCheck_5555_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_a_5519_);
lean_dec(v___x_5518_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5555_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
if (lean_obj_tag(v_a_5519_) == 0)
{
lean_object* v_a_5523_; lean_object* v___x_5525_; 
v_a_5523_ = lean_ctor_get(v_a_5519_, 0);
lean_inc(v_a_5523_);
lean_dec_ref_known(v_a_5519_, 1);
if (v_isShared_5522_ == 0)
{
lean_ctor_set(v___x_5521_, 0, v_a_5523_);
v___x_5525_ = v___x_5521_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5526_; 
v_reuseFailAlloc_5526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5526_, 0, v_a_5523_);
v___x_5525_ = v_reuseFailAlloc_5526_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
return v___x_5525_;
}
}
else
{
lean_object* v_a_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; size_t v_sz_5530_; size_t v___x_5531_; lean_object* v___x_5532_; 
lean_del_object(v___x_5521_);
v_a_5527_ = lean_ctor_get(v_a_5519_, 0);
lean_inc(v_a_5527_);
lean_dec_ref_known(v_a_5519_, 1);
v___x_5528_ = lean_box(0);
v___x_5529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5529_, 0, v___x_5528_);
lean_ctor_set(v___x_5529_, 1, v_a_5527_);
v_sz_5530_ = lean_array_size(v_tail_5517_);
v___x_5531_ = ((size_t)0ULL);
v___x_5532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5517_, v_sz_5530_, v___x_5531_, v___x_5529_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_);
if (lean_obj_tag(v___x_5532_) == 0)
{
lean_object* v_a_5533_; lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5546_; 
v_a_5533_ = lean_ctor_get(v___x_5532_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5532_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5535_ = v___x_5532_;
v_isShared_5536_ = v_isSharedCheck_5546_;
goto v_resetjp_5534_;
}
else
{
lean_inc(v_a_5533_);
lean_dec(v___x_5532_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5546_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v_fst_5537_; 
v_fst_5537_ = lean_ctor_get(v_a_5533_, 0);
if (lean_obj_tag(v_fst_5537_) == 0)
{
lean_object* v_snd_5538_; lean_object* v___x_5540_; 
v_snd_5538_ = lean_ctor_get(v_a_5533_, 1);
lean_inc(v_snd_5538_);
lean_dec(v_a_5533_);
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 0, v_snd_5538_);
v___x_5540_ = v___x_5535_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_snd_5538_);
v___x_5540_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
return v___x_5540_;
}
}
else
{
lean_object* v_val_5542_; lean_object* v___x_5544_; 
lean_inc_ref(v_fst_5537_);
lean_dec(v_a_5533_);
v_val_5542_ = lean_ctor_get(v_fst_5537_, 0);
lean_inc(v_val_5542_);
lean_dec_ref_known(v_fst_5537_, 1);
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 0, v_val_5542_);
v___x_5544_ = v___x_5535_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_val_5542_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
return v___x_5544_;
}
}
}
}
else
{
lean_object* v_a_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5554_; 
v_a_5547_ = lean_ctor_get(v___x_5532_, 0);
v_isSharedCheck_5554_ = !lean_is_exclusive(v___x_5532_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5549_ = v___x_5532_;
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_a_5547_);
lean_dec(v___x_5532_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5552_; 
if (v_isShared_5550_ == 0)
{
v___x_5552_ = v___x_5549_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5547_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
}
}
}
}
else
{
lean_object* v_a_5556_; lean_object* v___x_5558_; uint8_t v_isShared_5559_; uint8_t v_isSharedCheck_5563_; 
v_a_5556_ = lean_ctor_get(v___x_5518_, 0);
v_isSharedCheck_5563_ = !lean_is_exclusive(v___x_5518_);
if (v_isSharedCheck_5563_ == 0)
{
v___x_5558_ = v___x_5518_;
v_isShared_5559_ = v_isSharedCheck_5563_;
goto v_resetjp_5557_;
}
else
{
lean_inc(v_a_5556_);
lean_dec(v___x_5518_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5564_, lean_object* v_init_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_){
_start:
{
lean_object* v_res_5576_; 
v_res_5576_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5564_, v_init_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_);
lean_dec(v___y_5574_);
lean_dec_ref(v___y_5573_);
lean_dec(v___y_5572_);
lean_dec_ref(v___y_5571_);
lean_dec(v___y_5570_);
lean_dec_ref(v___y_5569_);
lean_dec(v___y_5568_);
lean_dec_ref(v___y_5567_);
lean_dec(v___y_5566_);
lean_dec_ref(v_t_5564_);
return v_res_5576_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; 
v___x_5577_ = lean_unsigned_to_nat(32u);
v___x_5578_ = lean_mk_empty_array_with_capacity(v___x_5577_);
v___x_5579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5579_, 0, v___x_5578_);
return v___x_5579_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v_result_5585_; 
v___x_5580_ = ((size_t)5ULL);
v___x_5581_ = lean_unsigned_to_nat(0u);
v___x_5582_ = lean_unsigned_to_nat(32u);
v___x_5583_ = lean_mk_empty_array_with_capacity(v___x_5582_);
v___x_5584_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5585_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5585_, 0, v___x_5584_);
lean_ctor_set(v_result_5585_, 1, v___x_5583_);
lean_ctor_set(v_result_5585_, 2, v___x_5581_);
lean_ctor_set(v_result_5585_, 3, v___x_5581_);
lean_ctor_set_usize(v_result_5585_, 4, v___x_5580_);
return v_result_5585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_, lean_object* v_a_5590_, lean_object* v_a_5591_, lean_object* v_a_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_){
_start:
{
lean_object* v_result_5597_; lean_object* v___x_5598_; 
v_result_5597_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5598_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5586_, v_result_5597_, v_a_5587_, v_a_5588_, v_a_5589_, v_a_5590_, v_a_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
return v___x_5598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_, lean_object* v_a_5602_, lean_object* v_a_5603_, lean_object* v_a_5604_, lean_object* v_a_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_){
_start:
{
lean_object* v_res_5610_; 
v_res_5610_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5599_, v_a_5600_, v_a_5601_, v_a_5602_, v_a_5603_, v_a_5604_, v_a_5605_, v_a_5606_, v_a_5607_, v_a_5608_);
lean_dec(v_a_5608_);
lean_dec_ref(v_a_5607_);
lean_dec(v_a_5606_);
lean_dec_ref(v_a_5605_);
lean_dec(v_a_5604_);
lean_dec_ref(v_a_5603_);
lean_dec(v_a_5602_);
lean_dec_ref(v_a_5601_);
lean_dec(v_a_5600_);
lean_dec_ref(v_thms_5599_);
return v_res_5610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_5613_, lean_object* v_newThms_5614_, lean_object* v_gmt_5615_, lean_object* v_numInstances_5616_, lean_object* v_numDelayedInstances_5617_, lean_object* v_num_5618_, lean_object* v_preInstances_5619_, lean_object* v_nextThmIdx_5620_, lean_object* v_matchEqNames_5621_, lean_object* v_delayedThmInsts_5622_, lean_object* v_nextDeclIdx_5623_, lean_object* v_enodeMap_5624_, lean_object* v_exprs_5625_, lean_object* v_parents_5626_, lean_object* v_congrTable_5627_, lean_object* v_appMap_5628_, lean_object* v_indicesFound_5629_, lean_object* v_toProcess_5630_, uint8_t v_inconsistent_5631_, lean_object* v_nextIdx_5632_, lean_object* v_newRawFacts_5633_, lean_object* v_facts_5634_, lean_object* v_extThms_5635_, lean_object* v_inj_5636_, lean_object* v_split_5637_, lean_object* v_clean_5638_, lean_object* v_sstates_5639_, lean_object* v_mvarId_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_){
_start:
{
lean_object* v___x_5651_; 
v___x_5651_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5613_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
if (lean_obj_tag(v___x_5651_) == 0)
{
lean_object* v_a_5652_; lean_object* v___x_5653_; 
v_a_5652_ = lean_ctor_get(v___x_5651_, 0);
lean_inc(v_a_5652_);
lean_dec_ref_known(v___x_5651_, 1);
v___x_5653_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_5614_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
if (lean_obj_tag(v___x_5653_) == 0)
{
lean_object* v_a_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5665_; 
v_a_5654_ = lean_ctor_get(v___x_5653_, 0);
v_isSharedCheck_5665_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5656_ = v___x_5653_;
v_isShared_5657_ = v_isSharedCheck_5665_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_a_5654_);
lean_dec(v___x_5653_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5665_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v___x_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5663_; 
v___x_5658_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_5659_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5658_);
lean_ctor_set(v___x_5659_, 1, v_gmt_5615_);
lean_ctor_set(v___x_5659_, 2, v_a_5652_);
lean_ctor_set(v___x_5659_, 3, v_a_5654_);
lean_ctor_set(v___x_5659_, 4, v_numInstances_5616_);
lean_ctor_set(v___x_5659_, 5, v_numDelayedInstances_5617_);
lean_ctor_set(v___x_5659_, 6, v_num_5618_);
lean_ctor_set(v___x_5659_, 7, v_preInstances_5619_);
lean_ctor_set(v___x_5659_, 8, v_nextThmIdx_5620_);
lean_ctor_set(v___x_5659_, 9, v_matchEqNames_5621_);
lean_ctor_set(v___x_5659_, 10, v_delayedThmInsts_5622_);
v___x_5660_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_5660_, 0, v_nextDeclIdx_5623_);
lean_ctor_set(v___x_5660_, 1, v_enodeMap_5624_);
lean_ctor_set(v___x_5660_, 2, v_exprs_5625_);
lean_ctor_set(v___x_5660_, 3, v_parents_5626_);
lean_ctor_set(v___x_5660_, 4, v_congrTable_5627_);
lean_ctor_set(v___x_5660_, 5, v_appMap_5628_);
lean_ctor_set(v___x_5660_, 6, v_indicesFound_5629_);
lean_ctor_set(v___x_5660_, 7, v_toProcess_5630_);
lean_ctor_set(v___x_5660_, 8, v_nextIdx_5632_);
lean_ctor_set(v___x_5660_, 9, v_newRawFacts_5633_);
lean_ctor_set(v___x_5660_, 10, v_facts_5634_);
lean_ctor_set(v___x_5660_, 11, v_extThms_5635_);
lean_ctor_set(v___x_5660_, 12, v___x_5659_);
lean_ctor_set(v___x_5660_, 13, v_inj_5636_);
lean_ctor_set(v___x_5660_, 14, v_split_5637_);
lean_ctor_set(v___x_5660_, 15, v_clean_5638_);
lean_ctor_set(v___x_5660_, 16, v_sstates_5639_);
lean_ctor_set_uint8(v___x_5660_, sizeof(void*)*17, v_inconsistent_5631_);
v___x_5661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5660_);
lean_ctor_set(v___x_5661_, 1, v_mvarId_5640_);
if (v_isShared_5657_ == 0)
{
lean_ctor_set(v___x_5656_, 0, v___x_5661_);
v___x_5663_ = v___x_5656_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v___x_5661_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
else
{
lean_object* v_a_5666_; lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5673_; 
lean_dec(v_a_5652_);
lean_dec(v_mvarId_5640_);
lean_dec_ref(v_sstates_5639_);
lean_dec_ref(v_clean_5638_);
lean_dec_ref(v_split_5637_);
lean_dec_ref(v_inj_5636_);
lean_dec_ref(v_extThms_5635_);
lean_dec_ref(v_facts_5634_);
lean_dec_ref(v_newRawFacts_5633_);
lean_dec(v_nextIdx_5632_);
lean_dec_ref(v_toProcess_5630_);
lean_dec_ref(v_indicesFound_5629_);
lean_dec_ref(v_appMap_5628_);
lean_dec_ref(v_congrTable_5627_);
lean_dec_ref(v_parents_5626_);
lean_dec_ref(v_exprs_5625_);
lean_dec_ref(v_enodeMap_5624_);
lean_dec(v_nextDeclIdx_5623_);
lean_dec_ref(v_delayedThmInsts_5622_);
lean_dec_ref(v_matchEqNames_5621_);
lean_dec(v_nextThmIdx_5620_);
lean_dec_ref(v_preInstances_5619_);
lean_dec(v_num_5618_);
lean_dec(v_numDelayedInstances_5617_);
lean_dec(v_numInstances_5616_);
lean_dec(v_gmt_5615_);
v_a_5666_ = lean_ctor_get(v___x_5653_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5673_ == 0)
{
v___x_5668_ = v___x_5653_;
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
else
{
lean_inc(v_a_5666_);
lean_dec(v___x_5653_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5671_; 
if (v_isShared_5669_ == 0)
{
v___x_5671_ = v___x_5668_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_a_5666_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
return v___x_5671_;
}
}
}
}
else
{
lean_object* v_a_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5681_; 
lean_dec(v_mvarId_5640_);
lean_dec_ref(v_sstates_5639_);
lean_dec_ref(v_clean_5638_);
lean_dec_ref(v_split_5637_);
lean_dec_ref(v_inj_5636_);
lean_dec_ref(v_extThms_5635_);
lean_dec_ref(v_facts_5634_);
lean_dec_ref(v_newRawFacts_5633_);
lean_dec(v_nextIdx_5632_);
lean_dec_ref(v_toProcess_5630_);
lean_dec_ref(v_indicesFound_5629_);
lean_dec_ref(v_appMap_5628_);
lean_dec_ref(v_congrTable_5627_);
lean_dec_ref(v_parents_5626_);
lean_dec_ref(v_exprs_5625_);
lean_dec_ref(v_enodeMap_5624_);
lean_dec(v_nextDeclIdx_5623_);
lean_dec_ref(v_delayedThmInsts_5622_);
lean_dec_ref(v_matchEqNames_5621_);
lean_dec(v_nextThmIdx_5620_);
lean_dec_ref(v_preInstances_5619_);
lean_dec(v_num_5618_);
lean_dec(v_numDelayedInstances_5617_);
lean_dec(v_numInstances_5616_);
lean_dec(v_gmt_5615_);
v_a_5674_ = lean_ctor_get(v___x_5651_, 0);
v_isSharedCheck_5681_ = !lean_is_exclusive(v___x_5651_);
if (v_isSharedCheck_5681_ == 0)
{
v___x_5676_ = v___x_5651_;
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_a_5674_);
lean_dec(v___x_5651_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5679_; 
if (v_isShared_5677_ == 0)
{
v___x_5679_ = v___x_5676_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_a_5674_);
v___x_5679_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
return v___x_5679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_5682_ = _args[0];
lean_object* v_newThms_5683_ = _args[1];
lean_object* v_gmt_5684_ = _args[2];
lean_object* v_numInstances_5685_ = _args[3];
lean_object* v_numDelayedInstances_5686_ = _args[4];
lean_object* v_num_5687_ = _args[5];
lean_object* v_preInstances_5688_ = _args[6];
lean_object* v_nextThmIdx_5689_ = _args[7];
lean_object* v_matchEqNames_5690_ = _args[8];
lean_object* v_delayedThmInsts_5691_ = _args[9];
lean_object* v_nextDeclIdx_5692_ = _args[10];
lean_object* v_enodeMap_5693_ = _args[11];
lean_object* v_exprs_5694_ = _args[12];
lean_object* v_parents_5695_ = _args[13];
lean_object* v_congrTable_5696_ = _args[14];
lean_object* v_appMap_5697_ = _args[15];
lean_object* v_indicesFound_5698_ = _args[16];
lean_object* v_toProcess_5699_ = _args[17];
lean_object* v_inconsistent_5700_ = _args[18];
lean_object* v_nextIdx_5701_ = _args[19];
lean_object* v_newRawFacts_5702_ = _args[20];
lean_object* v_facts_5703_ = _args[21];
lean_object* v_extThms_5704_ = _args[22];
lean_object* v_inj_5705_ = _args[23];
lean_object* v_split_5706_ = _args[24];
lean_object* v_clean_5707_ = _args[25];
lean_object* v_sstates_5708_ = _args[26];
lean_object* v_mvarId_5709_ = _args[27];
lean_object* v___y_5710_ = _args[28];
lean_object* v___y_5711_ = _args[29];
lean_object* v___y_5712_ = _args[30];
lean_object* v___y_5713_ = _args[31];
lean_object* v___y_5714_ = _args[32];
lean_object* v___y_5715_ = _args[33];
lean_object* v___y_5716_ = _args[34];
lean_object* v___y_5717_ = _args[35];
lean_object* v___y_5718_ = _args[36];
lean_object* v___y_5719_ = _args[37];
_start:
{
uint8_t v_inconsistent_boxed_5720_; lean_object* v_res_5721_; 
v_inconsistent_boxed_5720_ = lean_unbox(v_inconsistent_5700_);
v_res_5721_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_5682_, v_newThms_5683_, v_gmt_5684_, v_numInstances_5685_, v_numDelayedInstances_5686_, v_num_5687_, v_preInstances_5688_, v_nextThmIdx_5689_, v_matchEqNames_5690_, v_delayedThmInsts_5691_, v_nextDeclIdx_5692_, v_enodeMap_5693_, v_exprs_5694_, v_parents_5695_, v_congrTable_5696_, v_appMap_5697_, v_indicesFound_5698_, v_toProcess_5699_, v_inconsistent_boxed_5720_, v_nextIdx_5701_, v_newRawFacts_5702_, v_facts_5703_, v_extThms_5704_, v_inj_5705_, v_split_5706_, v_clean_5707_, v_sstates_5708_, v_mvarId_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_, v___y_5717_, v___y_5718_);
lean_dec(v___y_5718_);
lean_dec_ref(v___y_5717_);
lean_dec(v___y_5716_);
lean_dec_ref(v___y_5715_);
lean_dec(v___y_5714_);
lean_dec_ref(v___y_5713_);
lean_dec(v___y_5712_);
lean_dec_ref(v___y_5711_);
lean_dec(v___y_5710_);
lean_dec_ref(v_newThms_5683_);
lean_dec_ref(v_thms_5682_);
return v_res_5721_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5722_; 
v___x_5722_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_5722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_5723_, size_t v_i_5724_, lean_object* v_bs_5725_){
_start:
{
uint8_t v___x_5726_; 
v___x_5726_ = lean_usize_dec_lt(v_i_5724_, v_sz_5723_);
if (v___x_5726_ == 0)
{
return v_bs_5725_;
}
else
{
lean_object* v_v_5727_; lean_object* v_casesTypes_5728_; lean_object* v_extThms_5729_; lean_object* v_funCC_5730_; lean_object* v_inj_5731_; lean_object* v___x_5733_; uint8_t v_isShared_5734_; uint8_t v_isSharedCheck_5745_; 
v_v_5727_ = lean_array_uget(v_bs_5725_, v_i_5724_);
v_casesTypes_5728_ = lean_ctor_get(v_v_5727_, 0);
v_extThms_5729_ = lean_ctor_get(v_v_5727_, 1);
v_funCC_5730_ = lean_ctor_get(v_v_5727_, 2);
v_inj_5731_ = lean_ctor_get(v_v_5727_, 4);
v_isSharedCheck_5745_ = !lean_is_exclusive(v_v_5727_);
if (v_isSharedCheck_5745_ == 0)
{
lean_object* v_unused_5746_; 
v_unused_5746_ = lean_ctor_get(v_v_5727_, 3);
lean_dec(v_unused_5746_);
v___x_5733_ = v_v_5727_;
v_isShared_5734_ = v_isSharedCheck_5745_;
goto v_resetjp_5732_;
}
else
{
lean_inc(v_inj_5731_);
lean_inc(v_funCC_5730_);
lean_inc(v_extThms_5729_);
lean_inc(v_casesTypes_5728_);
lean_dec(v_v_5727_);
v___x_5733_ = lean_box(0);
v_isShared_5734_ = v_isSharedCheck_5745_;
goto v_resetjp_5732_;
}
v_resetjp_5732_:
{
lean_object* v___x_5735_; lean_object* v_bs_x27_5736_; lean_object* v___x_5737_; lean_object* v___x_5739_; 
v___x_5735_ = lean_unsigned_to_nat(0u);
v_bs_x27_5736_ = lean_array_uset(v_bs_5725_, v_i_5724_, v___x_5735_);
v___x_5737_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_5734_ == 0)
{
lean_ctor_set(v___x_5733_, 3, v___x_5737_);
v___x_5739_ = v___x_5733_;
goto v_reusejp_5738_;
}
else
{
lean_object* v_reuseFailAlloc_5744_; 
v_reuseFailAlloc_5744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5744_, 0, v_casesTypes_5728_);
lean_ctor_set(v_reuseFailAlloc_5744_, 1, v_extThms_5729_);
lean_ctor_set(v_reuseFailAlloc_5744_, 2, v_funCC_5730_);
lean_ctor_set(v_reuseFailAlloc_5744_, 3, v___x_5737_);
lean_ctor_set(v_reuseFailAlloc_5744_, 4, v_inj_5731_);
v___x_5739_ = v_reuseFailAlloc_5744_;
goto v_reusejp_5738_;
}
v_reusejp_5738_:
{
size_t v___x_5740_; size_t v___x_5741_; lean_object* v___x_5742_; 
v___x_5740_ = ((size_t)1ULL);
v___x_5741_ = lean_usize_add(v_i_5724_, v___x_5740_);
v___x_5742_ = lean_array_uset(v_bs_x27_5736_, v_i_5724_, v___x_5739_);
v_i_5724_ = v___x_5741_;
v_bs_5725_ = v___x_5742_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_5747_, lean_object* v_i_5748_, lean_object* v_bs_5749_){
_start:
{
size_t v_sz_boxed_5750_; size_t v_i_boxed_5751_; lean_object* v_res_5752_; 
v_sz_boxed_5750_ = lean_unbox_usize(v_sz_5747_);
lean_dec(v_sz_5747_);
v_i_boxed_5751_ = lean_unbox_usize(v_i_5748_);
lean_dec(v_i_5748_);
v_res_5752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_5750_, v_i_boxed_5751_, v_bs_5749_);
return v_res_5752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_5753_, lean_object* v_ps_5754_, uint8_t v_only_5755_, lean_object* v_k_5756_, lean_object* v_a_5757_, lean_object* v_a_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_){
_start:
{
lean_object* v___y_5767_; lean_object* v___y_5768_; lean_object* v___y_5769_; lean_object* v___y_5770_; lean_object* v___y_5771_; lean_object* v___y_5772_; lean_object* v___y_5773_; lean_object* v___y_5774_; lean_object* v___y_5775_; uint8_t v___y_5788_; uint8_t v___y_5789_; lean_object* v_params_5790_; lean_object* v___y_5791_; lean_object* v___y_5792_; lean_object* v___y_5793_; lean_object* v___y_5794_; lean_object* v___y_5795_; lean_object* v___y_5796_; lean_object* v___y_5797_; lean_object* v___y_5798_; uint8_t v___y_5901_; 
if (v_only_5755_ == 0)
{
lean_object* v___x_5923_; lean_object* v___x_5924_; uint8_t v___x_5925_; 
v___x_5923_ = lean_array_get_size(v_ps_5754_);
v___x_5924_ = lean_unsigned_to_nat(0u);
v___x_5925_ = lean_nat_dec_eq(v___x_5923_, v___x_5924_);
if (v___x_5925_ == 0)
{
v___y_5901_ = v___x_5925_;
goto v___jp_5900_;
}
else
{
lean_object* v___x_5926_; 
lean_dec_ref(v_params_5753_);
lean_inc(v_a_5764_);
lean_inc_ref(v_a_5763_);
lean_inc(v_a_5762_);
lean_inc_ref(v_a_5761_);
lean_inc(v_a_5760_);
lean_inc_ref(v_a_5759_);
lean_inc(v_a_5758_);
lean_inc_ref(v_a_5757_);
v___x_5926_ = lean_apply_9(v_k_5756_, v_a_5757_, v_a_5758_, v_a_5759_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_, lean_box(0));
return v___x_5926_;
}
}
else
{
uint8_t v___x_5927_; 
v___x_5927_ = 0;
v___y_5901_ = v___x_5927_;
goto v___jp_5900_;
}
v___jp_5766_:
{
lean_object* v___x_5776_; lean_object* v___x_5777_; 
v___x_5776_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_5776_, 0, v___y_5767_);
v___x_5777_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_5776_, v___y_5768_, v___y_5769_, v___y_5772_, v___y_5773_, v___y_5774_, v___y_5775_);
if (lean_obj_tag(v___x_5777_) == 0)
{
lean_object* v___x_5778_; 
lean_dec_ref_known(v___x_5777_, 1);
lean_inc(v___y_5775_);
lean_inc_ref(v___y_5774_);
lean_inc(v___y_5773_);
lean_inc_ref(v___y_5772_);
lean_inc(v___y_5771_);
lean_inc_ref(v___y_5770_);
lean_inc(v___y_5769_);
v___x_5778_ = lean_apply_9(v_k_5756_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_, v___y_5774_, v___y_5775_, lean_box(0));
return v___x_5778_;
}
else
{
lean_object* v_a_5779_; lean_object* v___x_5781_; uint8_t v_isShared_5782_; uint8_t v_isSharedCheck_5786_; 
lean_dec_ref(v___y_5768_);
lean_dec_ref(v_k_5756_);
v_a_5779_ = lean_ctor_get(v___x_5777_, 0);
v_isSharedCheck_5786_ = !lean_is_exclusive(v___x_5777_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5781_ = v___x_5777_;
v_isShared_5782_ = v_isSharedCheck_5786_;
goto v_resetjp_5780_;
}
else
{
lean_inc(v_a_5779_);
lean_dec(v___x_5777_);
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
v___jp_5787_:
{
lean_object* v___x_5799_; 
v___x_5799_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5790_, v_ps_5754_, v_only_5755_, v___y_5789_, v___y_5788_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
if (lean_obj_tag(v___x_5799_) == 0)
{
lean_object* v_a_5800_; lean_object* v_ctx_5801_; lean_object* v_anchorRefs_x3f_5802_; lean_object* v_toContext_5803_; lean_object* v_sctx_5804_; lean_object* v_methods_5805_; uint8_t v_sym_5806_; lean_object* v_simp_5807_; lean_object* v_simpMethods_5808_; lean_object* v_symSimpMethods_5809_; lean_object* v_symDSimpMethods_5810_; lean_object* v_config_5811_; uint8_t v_cheapCases_5812_; uint8_t v_reportMVarIssue_5813_; lean_object* v_splitSource_5814_; lean_object* v_ematchDiagSource_5815_; lean_object* v_symPrios_5816_; lean_object* v_extensions_5817_; uint8_t v_debug_5818_; uint8_t v_ematchDiag_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; 
v_a_5800_ = lean_ctor_get(v___x_5799_, 0);
lean_inc_n(v_a_5800_, 2);
lean_dec_ref_known(v___x_5799_, 1);
v_ctx_5801_ = lean_ctor_get(v___y_5791_, 1);
v_anchorRefs_x3f_5802_ = lean_ctor_get(v_a_5800_, 8);
v_toContext_5803_ = lean_ctor_get(v___y_5791_, 0);
v_sctx_5804_ = lean_ctor_get(v___y_5791_, 2);
v_methods_5805_ = lean_ctor_get(v___y_5791_, 3);
v_sym_5806_ = lean_ctor_get_uint8(v___y_5791_, sizeof(void*)*5);
v_simp_5807_ = lean_ctor_get(v_ctx_5801_, 0);
v_simpMethods_5808_ = lean_ctor_get(v_ctx_5801_, 1);
v_symSimpMethods_5809_ = lean_ctor_get(v_ctx_5801_, 2);
v_symDSimpMethods_5810_ = lean_ctor_get(v_ctx_5801_, 3);
v_config_5811_ = lean_ctor_get(v_ctx_5801_, 4);
v_cheapCases_5812_ = lean_ctor_get_uint8(v_ctx_5801_, sizeof(void*)*10);
v_reportMVarIssue_5813_ = lean_ctor_get_uint8(v_ctx_5801_, sizeof(void*)*10 + 1);
v_splitSource_5814_ = lean_ctor_get(v_ctx_5801_, 6);
v_ematchDiagSource_5815_ = lean_ctor_get(v_ctx_5801_, 7);
v_symPrios_5816_ = lean_ctor_get(v_ctx_5801_, 8);
v_extensions_5817_ = lean_ctor_get(v_ctx_5801_, 9);
v_debug_5818_ = lean_ctor_get_uint8(v_ctx_5801_, sizeof(void*)*10 + 2);
v_ematchDiag_5819_ = lean_ctor_get_uint8(v_ctx_5801_, sizeof(void*)*10 + 3);
lean_inc_ref(v_extensions_5817_);
lean_inc_ref(v_symPrios_5816_);
lean_inc(v_ematchDiagSource_5815_);
lean_inc(v_splitSource_5814_);
lean_inc(v_anchorRefs_x3f_5802_);
lean_inc_ref(v_config_5811_);
lean_inc_ref(v_symDSimpMethods_5810_);
lean_inc_ref(v_symSimpMethods_5809_);
lean_inc_ref(v_simpMethods_5808_);
lean_inc_ref(v_simp_5807_);
v___x_5820_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_5820_, 0, v_simp_5807_);
lean_ctor_set(v___x_5820_, 1, v_simpMethods_5808_);
lean_ctor_set(v___x_5820_, 2, v_symSimpMethods_5809_);
lean_ctor_set(v___x_5820_, 3, v_symDSimpMethods_5810_);
lean_ctor_set(v___x_5820_, 4, v_config_5811_);
lean_ctor_set(v___x_5820_, 5, v_anchorRefs_x3f_5802_);
lean_ctor_set(v___x_5820_, 6, v_splitSource_5814_);
lean_ctor_set(v___x_5820_, 7, v_ematchDiagSource_5815_);
lean_ctor_set(v___x_5820_, 8, v_symPrios_5816_);
lean_ctor_set(v___x_5820_, 9, v_extensions_5817_);
lean_ctor_set_uint8(v___x_5820_, sizeof(void*)*10, v_cheapCases_5812_);
lean_ctor_set_uint8(v___x_5820_, sizeof(void*)*10 + 1, v_reportMVarIssue_5813_);
lean_ctor_set_uint8(v___x_5820_, sizeof(void*)*10 + 2, v_debug_5818_);
lean_ctor_set_uint8(v___x_5820_, sizeof(void*)*10 + 3, v_ematchDiag_5819_);
lean_inc_ref(v_methods_5805_);
lean_inc_ref(v_sctx_5804_);
lean_inc_ref(v_toContext_5803_);
v___x_5821_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_5821_, 0, v_toContext_5803_);
lean_ctor_set(v___x_5821_, 1, v___x_5820_);
lean_ctor_set(v___x_5821_, 2, v_sctx_5804_);
lean_ctor_set(v___x_5821_, 3, v_methods_5805_);
lean_ctor_set(v___x_5821_, 4, v_a_5800_);
lean_ctor_set_uint8(v___x_5821_, sizeof(void*)*5, v_sym_5806_);
if (v_only_5755_ == 0)
{
v___y_5767_ = v_a_5800_;
v___y_5768_ = v___x_5821_;
v___y_5769_ = v___y_5792_;
v___y_5770_ = v___y_5793_;
v___y_5771_ = v___y_5794_;
v___y_5772_ = v___y_5795_;
v___y_5773_ = v___y_5796_;
v___y_5774_ = v___y_5797_;
v___y_5775_ = v___y_5798_;
goto v___jp_5766_;
}
else
{
lean_object* v___x_5822_; 
v___x_5822_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_5792_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
if (lean_obj_tag(v___x_5822_) == 0)
{
lean_object* v_a_5823_; lean_object* v_toGoalState_5824_; lean_object* v_ematch_5825_; lean_object* v_mvarId_5826_; lean_object* v___x_5828_; uint8_t v_isShared_5829_; uint8_t v_isSharedCheck_5882_; 
v_a_5823_ = lean_ctor_get(v___x_5822_, 0);
lean_inc(v_a_5823_);
lean_dec_ref_known(v___x_5822_, 1);
v_toGoalState_5824_ = lean_ctor_get(v_a_5823_, 0);
lean_inc_ref(v_toGoalState_5824_);
v_ematch_5825_ = lean_ctor_get(v_toGoalState_5824_, 12);
lean_inc_ref(v_ematch_5825_);
v_mvarId_5826_ = lean_ctor_get(v_a_5823_, 1);
v_isSharedCheck_5882_ = !lean_is_exclusive(v_a_5823_);
if (v_isSharedCheck_5882_ == 0)
{
lean_object* v_unused_5883_; 
v_unused_5883_ = lean_ctor_get(v_a_5823_, 0);
lean_dec(v_unused_5883_);
v___x_5828_ = v_a_5823_;
v_isShared_5829_ = v_isSharedCheck_5882_;
goto v_resetjp_5827_;
}
else
{
lean_inc(v_mvarId_5826_);
lean_dec(v_a_5823_);
v___x_5828_ = lean_box(0);
v_isShared_5829_ = v_isSharedCheck_5882_;
goto v_resetjp_5827_;
}
v_resetjp_5827_:
{
lean_object* v_nextDeclIdx_5830_; lean_object* v_enodeMap_5831_; lean_object* v_exprs_5832_; lean_object* v_parents_5833_; lean_object* v_congrTable_5834_; lean_object* v_appMap_5835_; lean_object* v_indicesFound_5836_; lean_object* v_toProcess_5837_; uint8_t v_inconsistent_5838_; lean_object* v_nextIdx_5839_; lean_object* v_newRawFacts_5840_; lean_object* v_facts_5841_; lean_object* v_extThms_5842_; lean_object* v_inj_5843_; lean_object* v_split_5844_; lean_object* v_clean_5845_; lean_object* v_sstates_5846_; lean_object* v_gmt_5847_; lean_object* v_thms_5848_; lean_object* v_newThms_5849_; lean_object* v_numInstances_5850_; lean_object* v_numDelayedInstances_5851_; lean_object* v_num_5852_; lean_object* v_preInstances_5853_; lean_object* v_nextThmIdx_5854_; lean_object* v_matchEqNames_5855_; lean_object* v_delayedThmInsts_5856_; lean_object* v___x_5857_; lean_object* v___f_5858_; lean_object* v___x_5859_; 
v_nextDeclIdx_5830_ = lean_ctor_get(v_toGoalState_5824_, 0);
lean_inc(v_nextDeclIdx_5830_);
v_enodeMap_5831_ = lean_ctor_get(v_toGoalState_5824_, 1);
lean_inc_ref(v_enodeMap_5831_);
v_exprs_5832_ = lean_ctor_get(v_toGoalState_5824_, 2);
lean_inc_ref(v_exprs_5832_);
v_parents_5833_ = lean_ctor_get(v_toGoalState_5824_, 3);
lean_inc_ref(v_parents_5833_);
v_congrTable_5834_ = lean_ctor_get(v_toGoalState_5824_, 4);
lean_inc_ref(v_congrTable_5834_);
v_appMap_5835_ = lean_ctor_get(v_toGoalState_5824_, 5);
lean_inc_ref(v_appMap_5835_);
v_indicesFound_5836_ = lean_ctor_get(v_toGoalState_5824_, 6);
lean_inc_ref(v_indicesFound_5836_);
v_toProcess_5837_ = lean_ctor_get(v_toGoalState_5824_, 7);
lean_inc_ref(v_toProcess_5837_);
v_inconsistent_5838_ = lean_ctor_get_uint8(v_toGoalState_5824_, sizeof(void*)*17);
v_nextIdx_5839_ = lean_ctor_get(v_toGoalState_5824_, 8);
lean_inc(v_nextIdx_5839_);
v_newRawFacts_5840_ = lean_ctor_get(v_toGoalState_5824_, 9);
lean_inc_ref(v_newRawFacts_5840_);
v_facts_5841_ = lean_ctor_get(v_toGoalState_5824_, 10);
lean_inc_ref(v_facts_5841_);
v_extThms_5842_ = lean_ctor_get(v_toGoalState_5824_, 11);
lean_inc_ref(v_extThms_5842_);
v_inj_5843_ = lean_ctor_get(v_toGoalState_5824_, 13);
lean_inc_ref(v_inj_5843_);
v_split_5844_ = lean_ctor_get(v_toGoalState_5824_, 14);
lean_inc_ref(v_split_5844_);
v_clean_5845_ = lean_ctor_get(v_toGoalState_5824_, 15);
lean_inc_ref(v_clean_5845_);
v_sstates_5846_ = lean_ctor_get(v_toGoalState_5824_, 16);
lean_inc_ref(v_sstates_5846_);
lean_dec_ref(v_toGoalState_5824_);
v_gmt_5847_ = lean_ctor_get(v_ematch_5825_, 1);
lean_inc(v_gmt_5847_);
v_thms_5848_ = lean_ctor_get(v_ematch_5825_, 2);
lean_inc_ref(v_thms_5848_);
v_newThms_5849_ = lean_ctor_get(v_ematch_5825_, 3);
lean_inc_ref(v_newThms_5849_);
v_numInstances_5850_ = lean_ctor_get(v_ematch_5825_, 4);
lean_inc(v_numInstances_5850_);
v_numDelayedInstances_5851_ = lean_ctor_get(v_ematch_5825_, 5);
lean_inc(v_numDelayedInstances_5851_);
v_num_5852_ = lean_ctor_get(v_ematch_5825_, 6);
lean_inc(v_num_5852_);
v_preInstances_5853_ = lean_ctor_get(v_ematch_5825_, 7);
lean_inc_ref(v_preInstances_5853_);
v_nextThmIdx_5854_ = lean_ctor_get(v_ematch_5825_, 8);
lean_inc(v_nextThmIdx_5854_);
v_matchEqNames_5855_ = lean_ctor_get(v_ematch_5825_, 9);
lean_inc_ref(v_matchEqNames_5855_);
v_delayedThmInsts_5856_ = lean_ctor_get(v_ematch_5825_, 10);
lean_inc_ref(v_delayedThmInsts_5856_);
lean_dec_ref(v_ematch_5825_);
v___x_5857_ = lean_box(v_inconsistent_5838_);
v___f_5858_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 38, 28);
lean_closure_set(v___f_5858_, 0, v_thms_5848_);
lean_closure_set(v___f_5858_, 1, v_newThms_5849_);
lean_closure_set(v___f_5858_, 2, v_gmt_5847_);
lean_closure_set(v___f_5858_, 3, v_numInstances_5850_);
lean_closure_set(v___f_5858_, 4, v_numDelayedInstances_5851_);
lean_closure_set(v___f_5858_, 5, v_num_5852_);
lean_closure_set(v___f_5858_, 6, v_preInstances_5853_);
lean_closure_set(v___f_5858_, 7, v_nextThmIdx_5854_);
lean_closure_set(v___f_5858_, 8, v_matchEqNames_5855_);
lean_closure_set(v___f_5858_, 9, v_delayedThmInsts_5856_);
lean_closure_set(v___f_5858_, 10, v_nextDeclIdx_5830_);
lean_closure_set(v___f_5858_, 11, v_enodeMap_5831_);
lean_closure_set(v___f_5858_, 12, v_exprs_5832_);
lean_closure_set(v___f_5858_, 13, v_parents_5833_);
lean_closure_set(v___f_5858_, 14, v_congrTable_5834_);
lean_closure_set(v___f_5858_, 15, v_appMap_5835_);
lean_closure_set(v___f_5858_, 16, v_indicesFound_5836_);
lean_closure_set(v___f_5858_, 17, v_toProcess_5837_);
lean_closure_set(v___f_5858_, 18, v___x_5857_);
lean_closure_set(v___f_5858_, 19, v_nextIdx_5839_);
lean_closure_set(v___f_5858_, 20, v_newRawFacts_5840_);
lean_closure_set(v___f_5858_, 21, v_facts_5841_);
lean_closure_set(v___f_5858_, 22, v_extThms_5842_);
lean_closure_set(v___f_5858_, 23, v_inj_5843_);
lean_closure_set(v___f_5858_, 24, v_split_5844_);
lean_closure_set(v___f_5858_, 25, v_clean_5845_);
lean_closure_set(v___f_5858_, 26, v_sstates_5846_);
lean_closure_set(v___f_5858_, 27, v_mvarId_5826_);
v___x_5859_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_5858_, v___x_5821_, v___y_5792_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
if (lean_obj_tag(v___x_5859_) == 0)
{
lean_object* v_a_5860_; lean_object* v___x_5861_; lean_object* v___x_5863_; 
v_a_5860_ = lean_ctor_get(v___x_5859_, 0);
lean_inc(v_a_5860_);
lean_dec_ref_known(v___x_5859_, 1);
v___x_5861_ = lean_box(0);
if (v_isShared_5829_ == 0)
{
lean_ctor_set_tag(v___x_5828_, 1);
lean_ctor_set(v___x_5828_, 1, v___x_5861_);
lean_ctor_set(v___x_5828_, 0, v_a_5860_);
v___x_5863_ = v___x_5828_;
goto v_reusejp_5862_;
}
else
{
lean_object* v_reuseFailAlloc_5873_; 
v_reuseFailAlloc_5873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5860_);
lean_ctor_set(v_reuseFailAlloc_5873_, 1, v___x_5861_);
v___x_5863_ = v_reuseFailAlloc_5873_;
goto v_reusejp_5862_;
}
v_reusejp_5862_:
{
lean_object* v___x_5864_; 
v___x_5864_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_5863_, v___y_5792_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
if (lean_obj_tag(v___x_5864_) == 0)
{
lean_dec_ref_known(v___x_5864_, 1);
v___y_5767_ = v_a_5800_;
v___y_5768_ = v___x_5821_;
v___y_5769_ = v___y_5792_;
v___y_5770_ = v___y_5793_;
v___y_5771_ = v___y_5794_;
v___y_5772_ = v___y_5795_;
v___y_5773_ = v___y_5796_;
v___y_5774_ = v___y_5797_;
v___y_5775_ = v___y_5798_;
goto v___jp_5766_;
}
else
{
lean_object* v_a_5865_; lean_object* v___x_5867_; uint8_t v_isShared_5868_; uint8_t v_isSharedCheck_5872_; 
lean_dec_ref_known(v___x_5821_, 5);
lean_dec(v_a_5800_);
lean_dec_ref(v_k_5756_);
v_a_5865_ = lean_ctor_get(v___x_5864_, 0);
v_isSharedCheck_5872_ = !lean_is_exclusive(v___x_5864_);
if (v_isSharedCheck_5872_ == 0)
{
v___x_5867_ = v___x_5864_;
v_isShared_5868_ = v_isSharedCheck_5872_;
goto v_resetjp_5866_;
}
else
{
lean_inc(v_a_5865_);
lean_dec(v___x_5864_);
v___x_5867_ = lean_box(0);
v_isShared_5868_ = v_isSharedCheck_5872_;
goto v_resetjp_5866_;
}
v_resetjp_5866_:
{
lean_object* v___x_5870_; 
if (v_isShared_5868_ == 0)
{
v___x_5870_ = v___x_5867_;
goto v_reusejp_5869_;
}
else
{
lean_object* v_reuseFailAlloc_5871_; 
v_reuseFailAlloc_5871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5871_, 0, v_a_5865_);
v___x_5870_ = v_reuseFailAlloc_5871_;
goto v_reusejp_5869_;
}
v_reusejp_5869_:
{
return v___x_5870_;
}
}
}
}
}
else
{
lean_object* v_a_5874_; lean_object* v___x_5876_; uint8_t v_isShared_5877_; uint8_t v_isSharedCheck_5881_; 
lean_del_object(v___x_5828_);
lean_dec_ref_known(v___x_5821_, 5);
lean_dec(v_a_5800_);
lean_dec_ref(v_k_5756_);
v_a_5874_ = lean_ctor_get(v___x_5859_, 0);
v_isSharedCheck_5881_ = !lean_is_exclusive(v___x_5859_);
if (v_isSharedCheck_5881_ == 0)
{
v___x_5876_ = v___x_5859_;
v_isShared_5877_ = v_isSharedCheck_5881_;
goto v_resetjp_5875_;
}
else
{
lean_inc(v_a_5874_);
lean_dec(v___x_5859_);
v___x_5876_ = lean_box(0);
v_isShared_5877_ = v_isSharedCheck_5881_;
goto v_resetjp_5875_;
}
v_resetjp_5875_:
{
lean_object* v___x_5879_; 
if (v_isShared_5877_ == 0)
{
v___x_5879_ = v___x_5876_;
goto v_reusejp_5878_;
}
else
{
lean_object* v_reuseFailAlloc_5880_; 
v_reuseFailAlloc_5880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5880_, 0, v_a_5874_);
v___x_5879_ = v_reuseFailAlloc_5880_;
goto v_reusejp_5878_;
}
v_reusejp_5878_:
{
return v___x_5879_;
}
}
}
}
}
else
{
lean_object* v_a_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5891_; 
lean_dec_ref_known(v___x_5821_, 5);
lean_dec(v_a_5800_);
lean_dec_ref(v_k_5756_);
v_a_5884_ = lean_ctor_get(v___x_5822_, 0);
v_isSharedCheck_5891_ = !lean_is_exclusive(v___x_5822_);
if (v_isSharedCheck_5891_ == 0)
{
v___x_5886_ = v___x_5822_;
v_isShared_5887_ = v_isSharedCheck_5891_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_a_5884_);
lean_dec(v___x_5822_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_5891_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
lean_object* v___x_5889_; 
if (v_isShared_5887_ == 0)
{
v___x_5889_ = v___x_5886_;
goto v_reusejp_5888_;
}
else
{
lean_object* v_reuseFailAlloc_5890_; 
v_reuseFailAlloc_5890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5890_, 0, v_a_5884_);
v___x_5889_ = v_reuseFailAlloc_5890_;
goto v_reusejp_5888_;
}
v_reusejp_5888_:
{
return v___x_5889_;
}
}
}
}
}
else
{
lean_object* v_a_5892_; lean_object* v___x_5894_; uint8_t v_isShared_5895_; uint8_t v_isSharedCheck_5899_; 
lean_dec_ref(v_k_5756_);
v_a_5892_ = lean_ctor_get(v___x_5799_, 0);
v_isSharedCheck_5899_ = !lean_is_exclusive(v___x_5799_);
if (v_isSharedCheck_5899_ == 0)
{
v___x_5894_ = v___x_5799_;
v_isShared_5895_ = v_isSharedCheck_5899_;
goto v_resetjp_5893_;
}
else
{
lean_inc(v_a_5892_);
lean_dec(v___x_5799_);
v___x_5894_ = lean_box(0);
v_isShared_5895_ = v_isSharedCheck_5899_;
goto v_resetjp_5893_;
}
v_resetjp_5893_:
{
lean_object* v___x_5897_; 
if (v_isShared_5895_ == 0)
{
v___x_5897_ = v___x_5894_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_5898_; 
v_reuseFailAlloc_5898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5898_, 0, v_a_5892_);
v___x_5897_ = v_reuseFailAlloc_5898_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
return v___x_5897_;
}
}
}
}
v___jp_5900_:
{
uint8_t v___x_5902_; 
v___x_5902_ = 1;
if (v_only_5755_ == 0)
{
v___y_5788_ = v___x_5902_;
v___y_5789_ = v___y_5901_;
v_params_5790_ = v_params_5753_;
v___y_5791_ = v_a_5757_;
v___y_5792_ = v_a_5758_;
v___y_5793_ = v_a_5759_;
v___y_5794_ = v_a_5760_;
v___y_5795_ = v_a_5761_;
v___y_5796_ = v_a_5762_;
v___y_5797_ = v_a_5763_;
v___y_5798_ = v_a_5764_;
goto v___jp_5787_;
}
else
{
lean_object* v_config_5903_; lean_object* v_extensions_5904_; lean_object* v_extra_5905_; lean_object* v_extraInj_5906_; lean_object* v_extraFacts_5907_; lean_object* v_symPrios_5908_; lean_object* v_norm_5909_; lean_object* v_normProcs_5910_; lean_object* v___x_5912_; uint8_t v_isShared_5913_; uint8_t v_isSharedCheck_5921_; 
v_config_5903_ = lean_ctor_get(v_params_5753_, 0);
v_extensions_5904_ = lean_ctor_get(v_params_5753_, 1);
v_extra_5905_ = lean_ctor_get(v_params_5753_, 2);
v_extraInj_5906_ = lean_ctor_get(v_params_5753_, 3);
v_extraFacts_5907_ = lean_ctor_get(v_params_5753_, 4);
v_symPrios_5908_ = lean_ctor_get(v_params_5753_, 5);
v_norm_5909_ = lean_ctor_get(v_params_5753_, 6);
v_normProcs_5910_ = lean_ctor_get(v_params_5753_, 7);
v_isSharedCheck_5921_ = !lean_is_exclusive(v_params_5753_);
if (v_isSharedCheck_5921_ == 0)
{
lean_object* v_unused_5922_; 
v_unused_5922_ = lean_ctor_get(v_params_5753_, 8);
lean_dec(v_unused_5922_);
v___x_5912_ = v_params_5753_;
v_isShared_5913_ = v_isSharedCheck_5921_;
goto v_resetjp_5911_;
}
else
{
lean_inc(v_normProcs_5910_);
lean_inc(v_norm_5909_);
lean_inc(v_symPrios_5908_);
lean_inc(v_extraFacts_5907_);
lean_inc(v_extraInj_5906_);
lean_inc(v_extra_5905_);
lean_inc(v_extensions_5904_);
lean_inc(v_config_5903_);
lean_dec(v_params_5753_);
v___x_5912_ = lean_box(0);
v_isShared_5913_ = v_isSharedCheck_5921_;
goto v_resetjp_5911_;
}
v_resetjp_5911_:
{
size_t v_sz_5914_; size_t v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v_params_5919_; 
v_sz_5914_ = lean_array_size(v_extensions_5904_);
v___x_5915_ = ((size_t)0ULL);
v___x_5916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_5914_, v___x_5915_, v_extensions_5904_);
v___x_5917_ = lean_box(0);
if (v_isShared_5913_ == 0)
{
lean_ctor_set(v___x_5912_, 8, v___x_5917_);
lean_ctor_set(v___x_5912_, 1, v___x_5916_);
v_params_5919_ = v___x_5912_;
goto v_reusejp_5918_;
}
else
{
lean_object* v_reuseFailAlloc_5920_; 
v_reuseFailAlloc_5920_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_config_5903_);
lean_ctor_set(v_reuseFailAlloc_5920_, 1, v___x_5916_);
lean_ctor_set(v_reuseFailAlloc_5920_, 2, v_extra_5905_);
lean_ctor_set(v_reuseFailAlloc_5920_, 3, v_extraInj_5906_);
lean_ctor_set(v_reuseFailAlloc_5920_, 4, v_extraFacts_5907_);
lean_ctor_set(v_reuseFailAlloc_5920_, 5, v_symPrios_5908_);
lean_ctor_set(v_reuseFailAlloc_5920_, 6, v_norm_5909_);
lean_ctor_set(v_reuseFailAlloc_5920_, 7, v_normProcs_5910_);
lean_ctor_set(v_reuseFailAlloc_5920_, 8, v___x_5917_);
v_params_5919_ = v_reuseFailAlloc_5920_;
goto v_reusejp_5918_;
}
v_reusejp_5918_:
{
v___y_5788_ = v___x_5902_;
v___y_5789_ = v___y_5901_;
v_params_5790_ = v_params_5919_;
v___y_5791_ = v_a_5757_;
v___y_5792_ = v_a_5758_;
v___y_5793_ = v_a_5759_;
v___y_5794_ = v_a_5760_;
v___y_5795_ = v_a_5761_;
v___y_5796_ = v_a_5762_;
v___y_5797_ = v_a_5763_;
v___y_5798_ = v_a_5764_;
goto v___jp_5787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_5928_, lean_object* v_ps_5929_, lean_object* v_only_5930_, lean_object* v_k_5931_, lean_object* v_a_5932_, lean_object* v_a_5933_, lean_object* v_a_5934_, lean_object* v_a_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_){
_start:
{
uint8_t v_only_boxed_5941_; lean_object* v_res_5942_; 
v_only_boxed_5941_ = lean_unbox(v_only_5930_);
v_res_5942_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5928_, v_ps_5929_, v_only_boxed_5941_, v_k_5931_, v_a_5932_, v_a_5933_, v_a_5934_, v_a_5935_, v_a_5936_, v_a_5937_, v_a_5938_, v_a_5939_);
lean_dec(v_a_5939_);
lean_dec_ref(v_a_5938_);
lean_dec(v_a_5937_);
lean_dec_ref(v_a_5936_);
lean_dec(v_a_5935_);
lean_dec_ref(v_a_5934_);
lean_dec(v_a_5933_);
lean_dec_ref(v_a_5932_);
lean_dec_ref(v_ps_5929_);
return v_res_5942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_5943_, lean_object* v_params_5944_, lean_object* v_ps_5945_, uint8_t v_only_5946_, lean_object* v_k_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_, lean_object* v_a_5952_, lean_object* v_a_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_){
_start:
{
lean_object* v___x_5957_; 
v___x_5957_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5944_, v_ps_5945_, v_only_5946_, v_k_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
return v___x_5957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_5958_, lean_object* v_params_5959_, lean_object* v_ps_5960_, lean_object* v_only_5961_, lean_object* v_k_5962_, lean_object* v_a_5963_, lean_object* v_a_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_){
_start:
{
uint8_t v_only_boxed_5972_; lean_object* v_res_5973_; 
v_only_boxed_5972_ = lean_unbox(v_only_5961_);
v_res_5973_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_5958_, v_params_5959_, v_ps_5960_, v_only_boxed_5972_, v_k_5962_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_);
lean_dec(v_a_5970_);
lean_dec_ref(v_a_5969_);
lean_dec(v_a_5968_);
lean_dec_ref(v_a_5967_);
lean_dec(v_a_5966_);
lean_dec_ref(v_a_5965_);
lean_dec(v_a_5964_);
lean_dec_ref(v_a_5963_);
lean_dec_ref(v_ps_5960_);
return v_res_5973_;
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
