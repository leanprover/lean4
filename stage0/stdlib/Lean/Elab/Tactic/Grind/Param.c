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
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1111_, lean_object* v_declHint_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v_env_1117_; uint8_t v___x_1118_; 
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_st_ref_get(v___y_1113_);
v_env_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc_ref(v_env_1117_);
lean_dec(v___x_1116_);
v___x_1118_ = l_Lean_Name_isAnonymous(v_declHint_1112_);
if (v___x_1118_ == 0)
{
uint8_t v_isExporting_1119_; 
v_isExporting_1119_ = lean_ctor_get_uint8(v_env_1117_, sizeof(void*)*13);
if (v_isExporting_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref(v_env_1117_);
lean_dec(v_declHint_1112_);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_msg_1111_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
lean_inc_ref(v_env_1117_);
v___x_1121_ = l_Lean_Environment_setExporting(v_env_1117_, v___x_1118_);
lean_inc(v_declHint_1112_);
lean_inc_ref(v___x_1121_);
v___x_1122_ = l_Lean_Environment_contains(v___x_1121_, v_declHint_1112_, v_isExporting_1119_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref(v___x_1121_);
lean_dec_ref(v_env_1117_);
lean_dec(v_declHint_1112_);
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_msg_1111_);
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
lean_inc(v_declHint_1112_);
v___x_1128_ = l_Lean_MessageData_ofConstName(v_declHint_1112_, v___x_1118_);
v_c_1129_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1129_, 0, v___x_1127_);
lean_ctor_set(v_c_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1117_, v_declHint_1112_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec_ref(v_env_1117_);
lean_dec(v_declHint_1112_);
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
lean_ctor_set(v___x_1136_, 0, v_msg_1111_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
else
{
lean_object* v_val_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1172_; 
v_val_1138_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1140_ = v___x_1130_;
v_isShared_1141_ = v_isSharedCheck_1172_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_val_1138_);
lean_dec(v___x_1130_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1172_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v_moduleNames_1143_; lean_object* v_mod_1144_; uint8_t v___x_1145_; 
v___x_1142_ = l_Lean_Environment_header(v_env_1117_);
lean_dec_ref(v_env_1117_);
v_moduleNames_1143_ = lean_ctor_get(v___x_1142_, 4);
lean_inc_ref(v_moduleNames_1143_);
lean_dec_ref(v___x_1142_);
v_mod_1144_ = lean_array_get(v___x_1115_, v_moduleNames_1143_, v_val_1138_);
lean_dec(v_val_1138_);
lean_dec_ref(v_moduleNames_1143_);
v___x_1145_ = l_Lean_isPrivateName(v_declHint_1112_);
lean_dec(v_declHint_1112_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_c_1129_);
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
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1155_);
v___x_1157_ = v___x_1140_;
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
lean_ctor_set(v___x_1160_, 1, v_c_1129_);
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
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1168_);
v___x_1170_ = v___x_1140_;
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
lean_dec_ref(v_env_1117_);
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
lean_object* v_toCold_1212_; lean_object* v_currRecDepth_1213_; lean_object* v_ref_1214_; uint16_t v_optionFlags_1215_; uint8_t v_suppressElabErrors_1216_; uint8_t v_isRecordingDeps_1217_; lean_object* v_ref_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_toCold_1212_ = lean_ctor_get(v___y_1209_, 0);
v_currRecDepth_1213_ = lean_ctor_get(v___y_1209_, 1);
v_ref_1214_ = lean_ctor_get(v___y_1209_, 2);
v_optionFlags_1215_ = lean_ctor_get_uint16(v___y_1209_, sizeof(void*)*3);
v_suppressElabErrors_1216_ = lean_ctor_get_uint8(v___y_1209_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1217_ = lean_ctor_get_uint8(v___y_1209_, sizeof(void*)*3 + 3);
v_ref_1218_ = l_Lean_replaceRef(v_ref_1205_, v_ref_1214_);
lean_inc(v_currRecDepth_1213_);
lean_inc_ref(v_toCold_1212_);
v___x_1219_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1219_, 0, v_toCold_1212_);
lean_ctor_set(v___x_1219_, 1, v_currRecDepth_1213_);
lean_ctor_set(v___x_1219_, 2, v_ref_1218_);
lean_ctor_set_uint16(v___x_1219_, sizeof(void*)*3, v_optionFlags_1215_);
lean_ctor_set_uint8(v___x_1219_, sizeof(void*)*3 + 2, v_suppressElabErrors_1216_);
lean_ctor_set_uint8(v___x_1219_, sizeof(void*)*3 + 3, v_isRecordingDeps_1217_);
v___x_1220_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1206_, v___y_1207_, v___y_1208_, v___x_1219_, v___y_1210_);
lean_dec_ref_known(v___x_1219_, 3);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1221_, lean_object* v_msg_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1221_, v_msg_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v_ref_1221_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1229_, lean_object* v_msg_1230_, lean_object* v_declHint_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; lean_object* v_a_1238_; lean_object* v___x_1239_; 
v___x_1237_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1230_, v_declHint_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1229_, v_a_1238_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1240_, lean_object* v_msg_1241_, lean_object* v_declHint_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1240_, v_msg_1241_, v_declHint_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v_ref_1240_);
return v_res_1248_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1251_ = l_Lean_stringToMessageData(v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1252_, lean_object* v_constName_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1259_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1260_ = 0;
lean_inc(v_constName_1253_);
v___x_1261_ = l_Lean_MessageData_ofConstName(v_constName_1253_, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1259_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1252_, v___x_1264_, v_constName_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1266_, lean_object* v_constName_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1266_, v_constName_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v_ref_1266_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_constName_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_ref_1280_; lean_object* v___x_1281_; 
v_ref_1280_ = lean_ctor_get(v___y_1277_, 2);
v___x_1281_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1280_, v_constName_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* v_constName_1289_, uint8_t v_skipRealize_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; lean_object* v_env_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_st_ref_get(v___y_1294_);
v_env_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc_ref(v_env_1297_);
lean_dec(v___x_1296_);
lean_inc(v_constName_1289_);
v___x_1298_ = l_Lean_Environment_findAsync_x3f(v_env_1297_, v_constName_1289_, v_skipRealize_1290_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1289_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
return v___x_1299_;
}
else
{
lean_object* v_val_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_constName_1289_);
v_val_1300_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1298_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_val_1300_);
lean_dec(v___x_1298_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 0);
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_val_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* v_constName_1308_, lean_object* v_skipRealize_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
uint8_t v_skipRealize_boxed_1315_; lean_object* v_res_1316_; 
v_skipRealize_boxed_1315_ = lean_unbox(v_skipRealize_1309_);
v_res_1316_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1308_, v_skipRealize_boxed_1315_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* v_declName_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; lean_object* v_env_1321_; uint8_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1320_ = lean_st_ref_get(v___y_1318_);
v_env_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc_ref(v_env_1321_);
lean_dec(v___x_1320_);
v___x_1322_ = l_Lean_getReducibilityStatusCore(v_env_1321_, v_declName_1317_);
v___x_1323_ = lean_box(v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_declName_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1325_, v___y_1326_);
lean_dec(v___y_1326_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* v_declName_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1351_; 
v___x_1335_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1329_, v___y_1333_);
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1351_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1351_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_unbox(v_a_1336_);
lean_dec(v_a_1336_);
if (v___x_1340_ == 0)
{
uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1341_ = 1;
v___x_1342_ = lean_box(v___x_1341_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1342_);
v___x_1344_ = v___x_1338_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
else
{
uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1346_ = 0;
v___x_1347_ = lean_box(v___x_1346_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1347_);
v___x_1349_ = v___x_1338_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* v_declName_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1358_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
return v___x_1361_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
v___x_1364_ = l_Lean_stringToMessageData(v___x_1363_);
return v___x_1364_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
v___x_1367_ = l_Lean_stringToMessageData(v___x_1366_);
return v___x_1367_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
v___x_1370_ = l_Lean_stringToMessageData(v___x_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
v___x_1373_ = l_Lean_stringToMessageData(v___x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* v_params_1374_, lean_object* v_id_1375_, lean_object* v_declName_1376_, lean_object* v_kind_1377_, uint8_t v_minIndexable_1378_, uint8_t v_suggest_1379_, uint8_t v_warn_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v___y_1387_; lean_object* v_thm_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; uint8_t v___x_1442_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___x_1639_; 
v___x_1442_ = 0;
lean_inc(v_declName_1376_);
v___x_1639_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1376_, v___x_1442_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; uint8_t v_kind_1641_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v_kind_1641_ = lean_ctor_get_uint8(v_a_1640_, sizeof(void*)*3);
lean_dec(v_a_1640_);
switch(v_kind_1641_)
{
case 1:
{
v___y_1570_ = v_a_1381_;
v___y_1571_ = v_a_1382_;
v___y_1572_ = v_a_1383_;
v___y_1573_ = v_a_1384_;
goto v___jp_1569_;
}
case 2:
{
v___y_1570_ = v_a_1381_;
v___y_1571_ = v_a_1382_;
v___y_1572_ = v_a_1383_;
v___y_1573_ = v_a_1384_;
goto v___jp_1569_;
}
case 6:
{
v___y_1570_ = v_a_1381_;
v___y_1571_ = v_a_1382_;
v___y_1572_ = v_a_1383_;
v___y_1573_ = v_a_1384_;
goto v___jp_1569_;
}
case 0:
{
lean_object* v___x_1642_; 
lean_dec(v_id_1375_);
lean_inc(v_declName_1376_);
v___x_1642_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1376_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; uint8_t v___x_1644_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1642_, 1);
v___x_1644_ = lean_unbox(v_a_1643_);
lean_dec(v_a_1643_);
if (v___x_1644_ == 0)
{
v___y_1500_ = v_a_1381_;
v___y_1501_ = v_a_1382_;
v___y_1502_ = v_a_1383_;
v___y_1503_ = v_a_1384_;
goto v___jp_1499_;
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_kind_1377_);
lean_dec_ref(v_params_1374_);
v___x_1645_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1646_ = l_Lean_MessageData_ofConstName(v_declName_1376_, v___x_1442_);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1649_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_kind_1377_);
lean_dec(v_declName_1376_);
lean_dec_ref(v_params_1374_);
v_a_1659_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1642_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1642_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
default: 
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec(v_kind_1377_);
lean_dec(v_id_1375_);
lean_dec_ref(v_params_1374_);
v___x_1667_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1668_ = l_Lean_MessageData_ofConstName(v_declName_1376_, v___x_1442_);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1671_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
return v___x_1672_;
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v_kind_1377_);
lean_dec(v_declName_1376_);
lean_dec(v_id_1375_);
lean_dec_ref(v_params_1374_);
v_a_1673_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1639_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1639_);
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
v___jp_1386_:
{
lean_object* v_config_1388_; lean_object* v_extensions_1389_; lean_object* v_extra_1390_; lean_object* v_extraInj_1391_; lean_object* v_extraFacts_1392_; lean_object* v_symPrios_1393_; lean_object* v_norm_1394_; lean_object* v_normProcs_1395_; lean_object* v_anchorRefs_x3f_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1405_; 
v_config_1388_ = lean_ctor_get(v_params_1374_, 0);
v_extensions_1389_ = lean_ctor_get(v_params_1374_, 1);
v_extra_1390_ = lean_ctor_get(v_params_1374_, 2);
v_extraInj_1391_ = lean_ctor_get(v_params_1374_, 3);
v_extraFacts_1392_ = lean_ctor_get(v_params_1374_, 4);
v_symPrios_1393_ = lean_ctor_get(v_params_1374_, 5);
v_norm_1394_ = lean_ctor_get(v_params_1374_, 6);
v_normProcs_1395_ = lean_ctor_get(v_params_1374_, 7);
v_anchorRefs_x3f_1396_ = lean_ctor_get(v_params_1374_, 8);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_params_1374_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1398_ = v_params_1374_;
v_isShared_1399_ = v_isSharedCheck_1405_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_anchorRefs_x3f_1396_);
lean_inc(v_normProcs_1395_);
lean_inc(v_norm_1394_);
lean_inc(v_symPrios_1393_);
lean_inc(v_extraFacts_1392_);
lean_inc(v_extraInj_1391_);
lean_inc(v_extra_1390_);
lean_inc(v_extensions_1389_);
lean_inc(v_config_1388_);
lean_dec(v_params_1374_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1405_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = l_Lean_PersistentArray_push___redArg(v_extra_1390_, v___y_1387_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 2, v___x_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_config_1388_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_extensions_1389_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v_extraInj_1391_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_extraFacts_1392_);
lean_ctor_set(v_reuseFailAlloc_1404_, 5, v_symPrios_1393_);
lean_ctor_set(v_reuseFailAlloc_1404_, 6, v_norm_1394_);
lean_ctor_set(v_reuseFailAlloc_1404_, 7, v_normProcs_1395_);
lean_ctor_set(v_reuseFailAlloc_1404_, 8, v_anchorRefs_x3f_1396_);
v___x_1402_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
return v___x_1403_;
}
}
}
v___jp_1406_:
{
if (v_warn_1380_ == 0)
{
lean_dec(v_declName_1376_);
v___y_1387_ = v_thm_1407_;
goto v___jp_1386_;
}
else
{
lean_object* v_extensions_1412_; lean_object* v_patterns_1413_; lean_object* v_origin_1414_; lean_object* v_cnstrs_1415_; uint8_t v___x_1416_; 
v_extensions_1412_ = lean_ctor_get(v_params_1374_, 1);
v_patterns_1413_ = lean_ctor_get(v_thm_1407_, 3);
v_origin_1414_ = lean_ctor_get(v_thm_1407_, 5);
v_cnstrs_1415_ = lean_ctor_get(v_thm_1407_, 7);
v___x_1416_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1412_, v_origin_1414_, v_patterns_1413_, v_cnstrs_1415_);
if (v___x_1416_ == 0)
{
lean_dec(v_declName_1376_);
v___y_1387_ = v_thm_1407_;
goto v___jp_1386_;
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1412_, v_declName_1376_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_dec_ref_known(v___x_1417_, 1);
v___y_1387_ = v_thm_1407_;
goto v___jp_1386_;
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v_thm_1407_);
lean_dec_ref(v_params_1374_);
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
}
v___jp_1426_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1438_ = l_Lean_PersistentArray_push___redArg(v___y_1431_, v___y_1437_);
v___x_1439_ = l_Lean_PersistentArray_push___redArg(v___x_1438_, v___y_1433_);
v___x_1440_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1440_, 0, v___y_1434_);
lean_ctor_set(v___x_1440_, 1, v___y_1432_);
lean_ctor_set(v___x_1440_, 2, v___x_1439_);
lean_ctor_set(v___x_1440_, 3, v___y_1436_);
lean_ctor_set(v___x_1440_, 4, v___y_1428_);
lean_ctor_set(v___x_1440_, 5, v___y_1427_);
lean_ctor_set(v___x_1440_, 6, v___y_1435_);
lean_ctor_set(v___x_1440_, 7, v___y_1430_);
lean_ctor_set(v___x_1440_, 8, v___y_1429_);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
v___jp_1443_:
{
lean_object* v___x_1448_; 
v___x_1448_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1378_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v___x_1449_; 
lean_dec_ref_known(v___x_1448_, 1);
lean_inc(v_declName_1376_);
v___x_1449_ = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(v_declName_1376_, v___x_1442_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1482_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1482_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1482_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
if (lean_obj_tag(v_a_1450_) == 1)
{
lean_object* v_val_1454_; lean_object* v_config_1455_; lean_object* v_extensions_1456_; lean_object* v_extra_1457_; lean_object* v_extraInj_1458_; lean_object* v_extraFacts_1459_; lean_object* v_symPrios_1460_; lean_object* v_norm_1461_; lean_object* v_normProcs_1462_; lean_object* v_anchorRefs_x3f_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_declName_1376_);
v_val_1454_ = lean_ctor_get(v_a_1450_, 0);
lean_inc(v_val_1454_);
lean_dec_ref_known(v_a_1450_, 1);
v_config_1455_ = lean_ctor_get(v_params_1374_, 0);
v_extensions_1456_ = lean_ctor_get(v_params_1374_, 1);
v_extra_1457_ = lean_ctor_get(v_params_1374_, 2);
v_extraInj_1458_ = lean_ctor_get(v_params_1374_, 3);
v_extraFacts_1459_ = lean_ctor_get(v_params_1374_, 4);
v_symPrios_1460_ = lean_ctor_get(v_params_1374_, 5);
v_norm_1461_ = lean_ctor_get(v_params_1374_, 6);
v_normProcs_1462_ = lean_ctor_get(v_params_1374_, 7);
v_anchorRefs_x3f_1463_ = lean_ctor_get(v_params_1374_, 8);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_params_1374_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1465_ = v_params_1374_;
v_isShared_1466_ = v_isSharedCheck_1475_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_anchorRefs_x3f_1463_);
lean_inc(v_normProcs_1462_);
lean_inc(v_norm_1461_);
lean_inc(v_symPrios_1460_);
lean_inc(v_extraFacts_1459_);
lean_inc(v_extraInj_1458_);
lean_inc(v_extra_1457_);
lean_inc(v_extensions_1456_);
lean_inc(v_config_1455_);
lean_dec(v_params_1374_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1475_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1467_ = l_Lean_Array_toPArray_x27___redArg(v_val_1454_);
lean_dec(v_val_1454_);
v___x_1468_ = l_Lean_PersistentArray_append___redArg(v_extra_1457_, v___x_1467_);
lean_dec_ref(v___x_1467_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 2, v___x_1468_);
v___x_1470_ = v___x_1465_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_config_1455_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_extensions_1456_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1474_, 3, v_extraInj_1458_);
lean_ctor_set(v_reuseFailAlloc_1474_, 4, v_extraFacts_1459_);
lean_ctor_set(v_reuseFailAlloc_1474_, 5, v_symPrios_1460_);
lean_ctor_set(v_reuseFailAlloc_1474_, 6, v_norm_1461_);
lean_ctor_set(v_reuseFailAlloc_1474_, 7, v_normProcs_1462_);
lean_ctor_set(v_reuseFailAlloc_1474_, 8, v_anchorRefs_x3f_1463_);
v___x_1470_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1472_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1470_);
v___x_1472_ = v___x_1452_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_del_object(v___x_1452_);
lean_dec(v_a_1450_);
lean_dec_ref(v_params_1374_);
v___x_1476_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__1, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
v___x_1477_ = l_Lean_MessageData_ofConstName(v_declName_1376_, v___x_1442_);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
v___x_1481_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1480_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
return v___x_1481_;
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_declName_1376_);
lean_dec_ref(v_params_1374_);
v_a_1483_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1449_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1449_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
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
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v_declName_1376_);
lean_dec_ref(v_params_1374_);
v_a_1491_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1448_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1448_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
v___jp_1499_:
{
uint8_t v___x_1504_; 
v___x_1504_ = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(v_kind_1377_);
if (v___x_1504_ == 0)
{
uint8_t v___x_1505_; 
v___x_1505_ = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(v_kind_1377_);
lean_dec(v_kind_1377_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec_ref(v_params_1374_);
v___x_1506_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1507_ = l_Lean_MessageData_ofConstName(v_declName_1376_, v___x_1442_);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__5, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1510_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
else
{
v___y_1444_ = v___y_1500_;
v___y_1445_ = v___y_1501_;
v___y_1446_ = v___y_1502_;
v___y_1447_ = v___y_1503_;
goto v___jp_1443_;
}
}
else
{
lean_dec(v_kind_1377_);
v___y_1444_ = v___y_1500_;
v___y_1445_ = v___y_1501_;
v___y_1446_ = v___y_1502_;
v___y_1447_ = v___y_1503_;
goto v___jp_1443_;
}
}
v___jp_1520_:
{
lean_object* v_symPrios_1525_; lean_object* v___x_1526_; 
v_symPrios_1525_ = lean_ctor_get(v_params_1374_, 5);
lean_inc_ref(v_symPrios_1525_);
lean_inc(v_declName_1376_);
v___x_1526_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1376_, v_kind_1377_, v_symPrios_1525_, v___x_1442_, v_minIndexable_1378_, v___y_1523_, v___y_1524_, v___y_1522_, v___y_1521_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v_thm_1407_ = v_a_1527_;
v___y_1408_ = v___y_1523_;
v___y_1409_ = v___y_1524_;
v___y_1410_ = v___y_1522_;
v___y_1411_ = v___y_1521_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_declName_1376_);
lean_dec_ref(v_params_1374_);
v_a_1528_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1526_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1526_);
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
}
v___jp_1536_:
{
if (v_suggest_1379_ == 0)
{
lean_dec(v_id_1375_);
v___y_1521_ = v___y_1540_;
v___y_1522_ = v___y_1539_;
v___y_1523_ = v___y_1537_;
v___y_1524_ = v___y_1538_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1541_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1539_);
v___x_1542_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1543_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_1541_, v___x_1542_);
lean_dec_ref(v___x_1541_);
if (v___x_1543_ == 0)
{
lean_object* v_symPrios_1544_; lean_object* v___x_1545_; 
lean_dec(v_kind_1377_);
v_symPrios_1544_ = lean_ctor_get(v_params_1374_, 5);
lean_inc_ref(v_symPrios_1544_);
lean_inc(v_declName_1376_);
v___x_1545_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1375_, v_declName_1376_, v_symPrios_1544_, v_minIndexable_1378_, v_suggest_1379_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v_thm_1407_ = v_a_1546_;
v___y_1408_ = v___y_1537_;
v___y_1409_ = v___y_1538_;
v___y_1410_ = v___y_1539_;
v___y_1411_ = v___y_1540_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_declName_1376_);
lean_dec_ref(v_params_1374_);
v_a_1547_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1545_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1545_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_dec(v_id_1375_);
v___y_1521_ = v___y_1540_;
v___y_1522_ = v___y_1539_;
v___y_1523_ = v___y_1537_;
v___y_1524_ = v___y_1538_;
goto v___jp_1520_;
}
}
}
v___jp_1555_:
{
lean_object* v___x_1560_; 
v___x_1560_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1378_, v___y_1557_, v___y_1559_, v___y_1558_, v___y_1556_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_dec_ref_known(v___x_1560_, 1);
v___y_1537_ = v___y_1557_;
v___y_1538_ = v___y_1559_;
v___y_1539_ = v___y_1558_;
v___y_1540_ = v___y_1556_;
goto v___jp_1536_;
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec(v_kind_1377_);
lean_dec(v_declName_1376_);
lean_dec(v_id_1375_);
lean_dec_ref(v_params_1374_);
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
v___jp_1569_:
{
if (lean_obj_tag(v_kind_1377_) == 2)
{
uint8_t v_gen_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_id_1375_);
v_gen_1574_ = lean_ctor_get_uint8(v_kind_1377_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_kind_1377_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1576_ = v_kind_1377_;
v_isShared_1577_ = v_isSharedCheck_1638_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v_kind_1377_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1638_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; 
v___x_1578_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1378_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_config_1579_; lean_object* v_extensions_1580_; lean_object* v_extra_1581_; lean_object* v_extraInj_1582_; lean_object* v_extraFacts_1583_; lean_object* v_symPrios_1584_; lean_object* v_norm_1585_; lean_object* v_normProcs_1586_; lean_object* v_anchorRefs_x3f_1587_; lean_object* v___x_1589_; 
lean_dec_ref_known(v___x_1578_, 1);
v_config_1579_ = lean_ctor_get(v_params_1374_, 0);
lean_inc_ref(v_config_1579_);
v_extensions_1580_ = lean_ctor_get(v_params_1374_, 1);
lean_inc_ref(v_extensions_1580_);
v_extra_1581_ = lean_ctor_get(v_params_1374_, 2);
lean_inc_ref(v_extra_1581_);
v_extraInj_1582_ = lean_ctor_get(v_params_1374_, 3);
lean_inc_ref(v_extraInj_1582_);
v_extraFacts_1583_ = lean_ctor_get(v_params_1374_, 4);
lean_inc_ref(v_extraFacts_1583_);
v_symPrios_1584_ = lean_ctor_get(v_params_1374_, 5);
lean_inc_ref(v_symPrios_1584_);
v_norm_1585_ = lean_ctor_get(v_params_1374_, 6);
lean_inc_ref(v_norm_1585_);
v_normProcs_1586_ = lean_ctor_get(v_params_1374_, 7);
lean_inc_ref(v_normProcs_1586_);
v_anchorRefs_x3f_1587_ = lean_ctor_get(v_params_1374_, 8);
lean_inc(v_anchorRefs_x3f_1587_);
lean_dec_ref(v_params_1374_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 0);
v___x_1589_ = v___x_1576_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_1629_, 0, v_gen_1574_);
v___x_1589_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; 
lean_inc_ref(v_symPrios_1584_);
lean_inc(v_declName_1376_);
v___x_1590_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1376_, v___x_1589_, v_symPrios_1584_, v___x_1442_, v___x_1442_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1592_, 0, v_gen_1574_);
lean_inc_ref(v_symPrios_1584_);
lean_inc(v_declName_1376_);
v___x_1593_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1376_, v___x_1592_, v_symPrios_1584_, v___x_1442_, v___x_1442_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1593_) == 0)
{
if (v_warn_1380_ == 0)
{
lean_object* v_a_1594_; 
lean_dec(v_declName_1376_);
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v___y_1427_ = v_symPrios_1584_;
v___y_1428_ = v_extraFacts_1583_;
v___y_1429_ = v_anchorRefs_x3f_1587_;
v___y_1430_ = v_normProcs_1586_;
v___y_1431_ = v_extra_1581_;
v___y_1432_ = v_extensions_1580_;
v___y_1433_ = v_a_1594_;
v___y_1434_ = v_config_1579_;
v___y_1435_ = v_norm_1585_;
v___y_1436_ = v_extraInj_1582_;
v___y_1437_ = v_a_1591_;
goto v___jp_1426_;
}
else
{
lean_object* v_a_1595_; lean_object* v_patterns_1596_; lean_object* v_origin_1597_; lean_object* v_cnstrs_1598_; uint8_t v___x_1599_; 
v_a_1595_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1593_, 1);
v_patterns_1596_ = lean_ctor_get(v_a_1591_, 3);
v_origin_1597_ = lean_ctor_get(v_a_1591_, 5);
v_cnstrs_1598_ = lean_ctor_get(v_a_1591_, 7);
v___x_1599_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1580_, v_origin_1597_, v_patterns_1596_, v_cnstrs_1598_);
if (v___x_1599_ == 0)
{
lean_dec(v_declName_1376_);
v___y_1427_ = v_symPrios_1584_;
v___y_1428_ = v_extraFacts_1583_;
v___y_1429_ = v_anchorRefs_x3f_1587_;
v___y_1430_ = v_normProcs_1586_;
v___y_1431_ = v_extra_1581_;
v___y_1432_ = v_extensions_1580_;
v___y_1433_ = v_a_1595_;
v___y_1434_ = v_config_1579_;
v___y_1435_ = v_norm_1585_;
v___y_1436_ = v_extraInj_1582_;
v___y_1437_ = v_a_1591_;
goto v___jp_1426_;
}
else
{
lean_object* v_patterns_1600_; lean_object* v_origin_1601_; lean_object* v_cnstrs_1602_; uint8_t v___x_1603_; 
v_patterns_1600_ = lean_ctor_get(v_a_1595_, 3);
v_origin_1601_ = lean_ctor_get(v_a_1595_, 5);
v_cnstrs_1602_ = lean_ctor_get(v_a_1595_, 7);
v___x_1603_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1580_, v_origin_1601_, v_patterns_1600_, v_cnstrs_1602_);
if (v___x_1603_ == 0)
{
lean_dec(v_declName_1376_);
v___y_1427_ = v_symPrios_1584_;
v___y_1428_ = v_extraFacts_1583_;
v___y_1429_ = v_anchorRefs_x3f_1587_;
v___y_1430_ = v_normProcs_1586_;
v___y_1431_ = v_extra_1581_;
v___y_1432_ = v_extensions_1580_;
v___y_1433_ = v_a_1595_;
v___y_1434_ = v_config_1579_;
v___y_1435_ = v_norm_1585_;
v___y_1436_ = v_extraInj_1582_;
v___y_1437_ = v_a_1591_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1604_; 
v___x_1604_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1580_, v_declName_1376_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_dec_ref_known(v___x_1604_, 1);
v___y_1427_ = v_symPrios_1584_;
v___y_1428_ = v_extraFacts_1583_;
v___y_1429_ = v_anchorRefs_x3f_1587_;
v___y_1430_ = v_normProcs_1586_;
v___y_1431_ = v_extra_1581_;
v___y_1432_ = v_extensions_1580_;
v___y_1433_ = v_a_1595_;
v___y_1434_ = v_config_1579_;
v___y_1435_ = v_norm_1585_;
v___y_1436_ = v_extraInj_1582_;
v___y_1437_ = v_a_1591_;
goto v___jp_1426_;
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_a_1595_);
lean_dec(v_a_1591_);
lean_dec(v_anchorRefs_x3f_1587_);
lean_dec_ref(v_normProcs_1586_);
lean_dec_ref(v_norm_1585_);
lean_dec_ref(v_symPrios_1584_);
lean_dec_ref(v_extraFacts_1583_);
lean_dec_ref(v_extraInj_1582_);
lean_dec_ref(v_extra_1581_);
lean_dec_ref(v_extensions_1580_);
lean_dec_ref(v_config_1579_);
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v_a_1591_);
lean_dec(v_anchorRefs_x3f_1587_);
lean_dec_ref(v_normProcs_1586_);
lean_dec_ref(v_norm_1585_);
lean_dec_ref(v_symPrios_1584_);
lean_dec_ref(v_extraFacts_1583_);
lean_dec_ref(v_extraInj_1582_);
lean_dec_ref(v_extra_1581_);
lean_dec_ref(v_extensions_1580_);
lean_dec_ref(v_config_1579_);
lean_dec(v_declName_1376_);
v_a_1613_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1593_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1593_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec(v_anchorRefs_x3f_1587_);
lean_dec_ref(v_normProcs_1586_);
lean_dec_ref(v_norm_1585_);
lean_dec_ref(v_symPrios_1584_);
lean_dec_ref(v_extraFacts_1583_);
lean_dec_ref(v_extraInj_1582_);
lean_dec_ref(v_extra_1581_);
lean_dec_ref(v_extensions_1580_);
lean_dec_ref(v_config_1579_);
lean_dec(v_declName_1376_);
v_a_1621_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1590_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1590_);
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
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_del_object(v___x_1576_);
lean_dec(v_declName_1376_);
lean_dec_ref(v_params_1374_);
v_a_1630_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1578_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1578_);
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
switch(lean_obj_tag(v_kind_1377_))
{
case 0:
{
v___y_1556_ = v___y_1573_;
v___y_1557_ = v___y_1570_;
v___y_1558_ = v___y_1572_;
v___y_1559_ = v___y_1571_;
goto v___jp_1555_;
}
case 1:
{
v___y_1556_ = v___y_1573_;
v___y_1557_ = v___y_1570_;
v___y_1558_ = v___y_1572_;
v___y_1559_ = v___y_1571_;
goto v___jp_1555_;
}
default: 
{
v___y_1537_ = v___y_1570_;
v___y_1538_ = v___y_1571_;
v___y_1539_ = v___y_1572_;
v___y_1540_ = v___y_1573_;
goto v___jp_1536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object* v_params_1681_, lean_object* v_id_1682_, lean_object* v_declName_1683_, lean_object* v_kind_1684_, lean_object* v_minIndexable_1685_, lean_object* v_suggest_1686_, lean_object* v_warn_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
uint8_t v_minIndexable_boxed_1693_; uint8_t v_suggest_boxed_1694_; uint8_t v_warn_boxed_1695_; lean_object* v_res_1696_; 
v_minIndexable_boxed_1693_ = lean_unbox(v_minIndexable_1685_);
v_suggest_boxed_1694_ = lean_unbox(v_suggest_1686_);
v_warn_boxed_1695_ = lean_unbox(v_warn_1687_);
v_res_1696_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_1681_, v_id_1682_, v_declName_1683_, v_kind_1684_, v_minIndexable_boxed_1693_, v_suggest_boxed_1694_, v_warn_boxed_1695_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object* v_declName_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1697_, v___y_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object* v_declName_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(v_declName_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_1711_, lean_object* v_constName_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_constName_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(v_00_u03b1_1719_, v_constName_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1727_, lean_object* v_ref_1728_, lean_object* v_constName_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1728_, v_constName_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1736_, lean_object* v_ref_1737_, lean_object* v_constName_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(v_00_u03b1_1736_, v_ref_1737_, v_constName_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v_ref_1737_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1745_, lean_object* v_ref_1746_, lean_object* v_msg_1747_, lean_object* v_declHint_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1746_, v_msg_1747_, v_declHint_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1755_, lean_object* v_ref_1756_, lean_object* v_msg_1757_, lean_object* v_declHint_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1755_, v_ref_1756_, v_msg_1757_, v_declHint_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v_ref_1756_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1765_, lean_object* v_declHint_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1765_, v_declHint_1766_, v___y_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1773_, lean_object* v_declHint_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1773_, v_declHint_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1781_, lean_object* v_ref_1782_, lean_object* v_msg_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1782_, v_msg_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1790_, lean_object* v_ref_1791_, lean_object* v_msg_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1790_, v_ref_1791_, v_msg_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v_ref_1791_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1801_, lean_object* v_val_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_config_1806_; lean_object* v_extensions_1807_; lean_object* v_extra_1808_; lean_object* v_extraInj_1809_; lean_object* v_extraFacts_1810_; lean_object* v_symPrios_1811_; lean_object* v_norm_1812_; lean_object* v_normProcs_1813_; lean_object* v_anchorRefs_x3f_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1844_; 
v_config_1806_ = lean_ctor_get(v_params_1801_, 0);
v_extensions_1807_ = lean_ctor_get(v_params_1801_, 1);
v_extra_1808_ = lean_ctor_get(v_params_1801_, 2);
v_extraInj_1809_ = lean_ctor_get(v_params_1801_, 3);
v_extraFacts_1810_ = lean_ctor_get(v_params_1801_, 4);
v_symPrios_1811_ = lean_ctor_get(v_params_1801_, 5);
v_norm_1812_ = lean_ctor_get(v_params_1801_, 6);
v_normProcs_1813_ = lean_ctor_get(v_params_1801_, 7);
v_anchorRefs_x3f_1814_ = lean_ctor_get(v_params_1801_, 8);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_params_1801_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1816_ = v_params_1801_;
v_isShared_1817_ = v_isSharedCheck_1844_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_anchorRefs_x3f_1814_);
lean_inc(v_normProcs_1813_);
lean_inc(v_norm_1812_);
lean_inc(v_symPrios_1811_);
lean_inc(v_extraFacts_1810_);
lean_inc(v_extraInj_1809_);
lean_inc(v_extra_1808_);
lean_inc(v_extensions_1807_);
lean_inc(v_config_1806_);
lean_dec(v_params_1801_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1844_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___y_1819_; 
if (lean_obj_tag(v_anchorRefs_x3f_1814_) == 0)
{
lean_object* v___x_1842_; 
v___x_1842_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_1819_ = v___x_1842_;
goto v___jp_1818_;
}
else
{
lean_object* v_val_1843_; 
v_val_1843_ = lean_ctor_get(v_anchorRefs_x3f_1814_, 0);
lean_inc(v_val_1843_);
lean_dec_ref_known(v_anchorRefs_x3f_1814_, 1);
v___y_1819_ = v_val_1843_;
goto v___jp_1818_;
}
v___jp_1818_:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1833_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1833_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1833_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1825_ = lean_array_push(v___y_1819_, v_a_1821_);
v___x_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 8, v___x_1826_);
v___x_1828_ = v___x_1816_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_config_1806_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_extensions_1807_);
lean_ctor_set(v_reuseFailAlloc_1832_, 2, v_extra_1808_);
lean_ctor_set(v_reuseFailAlloc_1832_, 3, v_extraInj_1809_);
lean_ctor_set(v_reuseFailAlloc_1832_, 4, v_extraFacts_1810_);
lean_ctor_set(v_reuseFailAlloc_1832_, 5, v_symPrios_1811_);
lean_ctor_set(v_reuseFailAlloc_1832_, 6, v_norm_1812_);
lean_ctor_set(v_reuseFailAlloc_1832_, 7, v_normProcs_1813_);
lean_ctor_set(v_reuseFailAlloc_1832_, 8, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1830_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1828_);
v___x_1830_ = v___x_1823_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v___y_1819_);
lean_del_object(v___x_1816_);
lean_dec_ref(v_normProcs_1813_);
lean_dec_ref(v_norm_1812_);
lean_dec_ref(v_symPrios_1811_);
lean_dec_ref(v_extraFacts_1810_);
lean_dec_ref(v_extraInj_1809_);
lean_dec_ref(v_extra_1808_);
lean_dec_ref(v_extensions_1807_);
lean_dec_ref(v_config_1806_);
v_a_1834_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1820_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1820_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_1845_, lean_object* v_val_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_1845_, v_val_1846_, v_a_1847_, v_a_1848_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
lean_dec(v_val_1846_);
return v_res_1850_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_1853_ = l_Lean_stringToMessageData(v___x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_config_1858_; uint8_t v_revert_1859_; 
v_config_1858_ = lean_ctor_get(v_params_1854_, 0);
v_revert_1859_ = lean_ctor_get_uint8(v_config_1858_, sizeof(void*)*14 + 30);
if (v_revert_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_1863_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1862_, v_a_1855_, v_a_1856_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_1864_, v_a_1865_, v_a_1866_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec_ref(v_params_1864_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_1869_, lean_object* v___y_1870_){
_start:
{
uint8_t v___x_1872_; 
v___x_1872_ = l_Lean_Expr_hasMVar(v_e_1869_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_e_1869_);
return v___x_1873_;
}
else
{
lean_object* v___x_1874_; lean_object* v_mctx_1875_; lean_object* v___x_1876_; lean_object* v_fst_1877_; lean_object* v_snd_1878_; lean_object* v___x_1879_; lean_object* v_cache_1880_; lean_object* v_zetaDeltaFVarIds_1881_; lean_object* v_postponed_1882_; lean_object* v_diag_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1892_; 
v___x_1874_ = lean_st_ref_get(v___y_1870_);
v_mctx_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc_ref(v_mctx_1875_);
lean_dec(v___x_1874_);
v___x_1876_ = l_Lean_instantiateMVarsCore(v_mctx_1875_, v_e_1869_);
v_fst_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_fst_1877_);
v_snd_1878_ = lean_ctor_get(v___x_1876_, 1);
lean_inc(v_snd_1878_);
lean_dec_ref(v___x_1876_);
v___x_1879_ = lean_st_ref_take(v___y_1870_);
v_cache_1880_ = lean_ctor_get(v___x_1879_, 1);
v_zetaDeltaFVarIds_1881_ = lean_ctor_get(v___x_1879_, 2);
v_postponed_1882_ = lean_ctor_get(v___x_1879_, 3);
v_diag_1883_ = lean_ctor_get(v___x_1879_, 4);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1892_ == 0)
{
lean_object* v_unused_1893_; 
v_unused_1893_ = lean_ctor_get(v___x_1879_, 0);
lean_dec(v_unused_1893_);
v___x_1885_ = v___x_1879_;
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_diag_1883_);
lean_inc(v_postponed_1882_);
lean_inc(v_zetaDeltaFVarIds_1881_);
lean_inc(v_cache_1880_);
lean_dec(v___x_1879_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v_snd_1878_);
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_snd_1878_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_cache_1880_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_zetaDeltaFVarIds_1881_);
lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_postponed_1882_);
lean_ctor_set(v_reuseFailAlloc_1891_, 4, v_diag_1883_);
v___x_1888_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_st_ref_put(v___y_1870_, v___x_1888_);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v_fst_1877_);
return v___x_1890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1894_, v___y_1895_);
lean_dec(v___y_1895_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1898_, v___y_1902_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(uint8_t v___x_1916_, uint8_t v___x_1917_, uint8_t v_____do__lift_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
if (v_____do__lift_1918_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_box(v___x_1916_);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_box(v___x_1917_);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v___x_1930_, lean_object* v___x_1931_, lean_object* v_____do__lift_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
uint8_t v___x_14719__boxed_1940_; uint8_t v___x_14720__boxed_1941_; uint8_t v_____do__lift_14721__boxed_1942_; lean_object* v_res_1943_; 
v___x_14719__boxed_1940_ = lean_unbox(v___x_1930_);
v___x_14720__boxed_1941_ = lean_unbox(v___x_1931_);
v_____do__lift_14721__boxed_1942_ = lean_unbox(v_____do__lift_1932_);
v_res_1943_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_14719__boxed_1940_, v___x_14720__boxed_1941_, v_____do__lift_14721__boxed_1942_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(uint8_t v___x_1944_, uint8_t v___x_1945_, lean_object* v_as_1946_, size_t v_i_1947_, size_t v_stop_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_usize_dec_eq(v_i_1947_, v_stop_1948_);
if (v___x_1954_ == 0)
{
uint8_t v___x_1955_; uint8_t v_a_1957_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1955_ = 1;
v___x_1963_ = lean_array_uget_borrowed(v_as_1946_, v_i_1947_);
lean_inc(v___x_1963_);
v___x_1964_ = l_Lean_Meta_isProof(v___x_1963_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; uint8_t v___x_1966_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v___x_1966_ = lean_unbox(v_a_1965_);
lean_dec(v_a_1965_);
if (v___x_1966_ == 0)
{
v_a_1957_ = v___x_1944_;
goto v___jp_1956_;
}
else
{
v_a_1957_ = v___x_1945_;
goto v___jp_1956_;
}
}
else
{
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1967_; uint8_t v___x_1968_; 
v_a_1967_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1964_, 1);
v___x_1968_ = lean_unbox(v_a_1967_);
lean_dec(v_a_1967_);
v_a_1957_ = v___x_1968_;
goto v___jp_1956_;
}
else
{
return v___x_1964_;
}
}
v___jp_1956_:
{
if (v_a_1957_ == 0)
{
size_t v___x_1958_; size_t v___x_1959_; 
v___x_1958_ = ((size_t)1ULL);
v___x_1959_ = lean_usize_add(v_i_1947_, v___x_1958_);
v_i_1947_ = v___x_1959_;
goto _start;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_box(v___x_1955_);
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
}
else
{
uint8_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = 0;
v___x_1970_ = lean_box(v___x_1969_);
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
return v___x_1971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v___x_1972_, lean_object* v___x_1973_, lean_object* v_as_1974_, lean_object* v_i_1975_, lean_object* v_stop_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
uint8_t v___x_14757__boxed_1982_; uint8_t v___x_14758__boxed_1983_; size_t v_i_boxed_1984_; size_t v_stop_boxed_1985_; lean_object* v_res_1986_; 
v___x_14757__boxed_1982_ = lean_unbox(v___x_1972_);
v___x_14758__boxed_1983_ = lean_unbox(v___x_1973_);
v_i_boxed_1984_ = lean_unbox_usize(v_i_1975_);
lean_dec(v_i_1975_);
v_stop_boxed_1985_ = lean_unbox_usize(v_stop_1976_);
lean_dec(v_stop_1976_);
v_res_1986_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_14757__boxed_1982_, v___x_14758__boxed_1983_, v_as_1974_, v_i_boxed_1984_, v_stop_boxed_1985_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec_ref(v_as_1974_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_p_1989_, lean_object* v_term_1990_, lean_object* v___x_1991_, uint8_t v___x_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_toCold_2000_; lean_object* v_currRecDepth_2001_; lean_object* v_ref_2002_; uint16_t v_optionFlags_2003_; uint8_t v_suppressElabErrors_2004_; uint8_t v_isRecordingDeps_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2102_; 
v_toCold_2000_ = lean_ctor_get(v___y_1997_, 0);
v_currRecDepth_2001_ = lean_ctor_get(v___y_1997_, 1);
v_ref_2002_ = lean_ctor_get(v___y_1997_, 2);
v_optionFlags_2003_ = lean_ctor_get_uint16(v___y_1997_, sizeof(void*)*3);
v_suppressElabErrors_2004_ = lean_ctor_get_uint8(v___y_1997_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2005_ = lean_ctor_get_uint8(v___y_1997_, sizeof(void*)*3 + 3);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___y_1997_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2007_ = v___y_1997_;
v_isShared_2008_ = v_isSharedCheck_2102_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_ref_2002_);
lean_inc(v_currRecDepth_2001_);
lean_inc(v_toCold_2000_);
lean_dec(v___y_1997_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2102_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v_ref_2009_; lean_object* v___x_2011_; 
v_ref_2009_ = l_Lean_replaceRef(v_p_1989_, v_ref_2002_);
lean_dec(v_ref_2002_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 2, v_ref_2009_);
v___x_2011_ = v___x_2007_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_toCold_2000_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_currRecDepth_2001_);
lean_ctor_set(v_reuseFailAlloc_2101_, 2, v_ref_2009_);
lean_ctor_set_uint16(v_reuseFailAlloc_2101_, sizeof(void*)*3, v_optionFlags_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2101_, sizeof(void*)*3 + 2, v_suppressElabErrors_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2101_, sizeof(void*)*3 + 3, v_isRecordingDeps_2005_);
v___x_2011_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_Elab_Term_elabTerm(v_term_1990_, v___x_1991_, v___x_1992_, v___x_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___x_2011_, v___y_1998_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v___x_2014_ = 1;
v___x_2015_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_2014_, v___x_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___x_2011_, v___y_1998_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2016_; lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref_known(v___x_2015_, 1);
v___x_2016_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_2013_, v___y_1996_);
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2084_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2084_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
uint8_t v___x_2021_; 
v___x_2021_ = l_Lean_Expr_hasSyntheticSorry(v_a_2017_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = l_Lean_Expr_eta(v_a_2017_);
v___x_2023_ = l_Lean_Expr_hasMVar(v___x_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2030_; 
lean_dec_ref(v___x_2011_);
v___x_2024_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0));
v___x_2025_ = lean_box(v___x_2023_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2022_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2024_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2028_);
v___x_2030_ = v___x_2019_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
else
{
lean_object* v___x_2032_; 
lean_del_object(v___x_2019_);
v___x_2032_ = l_Lean_Meta_abstractMVars(v___x_2022_, v___x_1992_, v___y_1995_, v___y_1996_, v___x_2011_, v___y_1998_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2071_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2035_ = v___x_2032_;
v_isShared_2036_ = v_isSharedCheck_2071_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2071_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v_paramNames_2037_; lean_object* v_mvars_2038_; lean_object* v_expr_2039_; uint8_t v_a_2041_; lean_object* v___y_2050_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v_paramNames_2037_ = lean_ctor_get(v_a_2033_, 0);
lean_inc_ref(v_paramNames_2037_);
v_mvars_2038_ = lean_ctor_get(v_a_2033_, 1);
lean_inc_ref(v_mvars_2038_);
v_expr_2039_ = lean_ctor_get(v_a_2033_, 2);
lean_inc_ref(v_expr_2039_);
lean_dec(v_a_2033_);
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = lean_array_get_size(v_mvars_2038_);
v___x_2063_ = lean_nat_dec_lt(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; 
lean_dec_ref(v_mvars_2038_);
v___x_2064_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2023_, v___x_2021_, v___x_2063_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___x_2011_, v___y_1998_);
lean_dec_ref(v___x_2011_);
v___y_2050_ = v___x_2064_;
goto v___jp_2049_;
}
else
{
if (v___x_2063_ == 0)
{
lean_dec_ref(v_mvars_2038_);
lean_dec_ref(v___x_2011_);
v_a_2041_ = v___x_2023_;
goto v___jp_2040_;
}
else
{
size_t v___x_2065_; size_t v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = ((size_t)0ULL);
v___x_2066_ = lean_usize_of_nat(v___x_2062_);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2023_, v___x_2021_, v_mvars_2038_, v___x_2065_, v___x_2066_, v___y_1995_, v___y_1996_, v___x_2011_, v___y_1998_);
lean_dec_ref(v_mvars_2038_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; uint8_t v___x_2069_; lean_object* v___x_2070_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2067_, 1);
v___x_2069_ = lean_unbox(v_a_2068_);
lean_dec(v_a_2068_);
v___x_2070_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2023_, v___x_2021_, v___x_2069_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___x_2011_, v___y_1998_);
lean_dec_ref(v___x_2011_);
v___y_2050_ = v___x_2070_;
goto v___jp_2049_;
}
else
{
lean_dec_ref(v___x_2011_);
v___y_2050_ = v___x_2067_;
goto v___jp_2049_;
}
}
}
v___jp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2042_ = lean_box(v_a_2041_);
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v_expr_2039_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v_paramNames_2037_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2045_);
v___x_2047_ = v___x_2035_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
v___jp_2049_:
{
if (lean_obj_tag(v___y_2050_) == 0)
{
lean_object* v_a_2051_; uint8_t v___x_2052_; 
v_a_2051_ = lean_ctor_get(v___y_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___y_2050_, 1);
v___x_2052_ = lean_unbox(v_a_2051_);
lean_dec(v_a_2051_);
v_a_2041_ = v___x_2052_;
goto v___jp_2040_;
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref(v_expr_2039_);
lean_dec_ref(v_paramNames_2037_);
lean_del_object(v___x_2035_);
v_a_2053_ = lean_ctor_get(v___y_2050_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___y_2050_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___y_2050_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___y_2050_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v___x_2011_);
v_a_2072_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2032_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2032_);
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
else
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
lean_dec(v_a_2017_);
lean_dec_ref(v___x_2011_);
v___x_2080_ = lean_box(0);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2080_);
v___x_2082_ = v___x_2019_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_a_2013_);
lean_dec_ref(v___x_2011_);
v_a_2085_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2015_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2015_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec_ref(v___x_2011_);
v_a_2093_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2012_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2012_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_p_2103_, lean_object* v_term_2104_, lean_object* v___x_2105_, lean_object* v___x_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
uint8_t v___x_14820__boxed_2114_; lean_object* v_res_2115_; 
v___x_14820__boxed_2114_ = lean_unbox(v___x_2106_);
v_res_2115_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_p_2103_, v_term_2104_, v___x_2105_, v___x_14820__boxed_2114_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v_p_2103_);
return v_res_2115_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__2));
v___x_2121_ = l_Lean_stringToMessageData(v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(lean_object* v_params_2122_, lean_object* v_p_2123_, lean_object* v_fst_2124_, lean_object* v_fst_2125_, uint8_t v___x_2126_, uint8_t v_minIndexable_2127_, lean_object* v_kind_2128_, lean_object* v_idx_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_symPrios_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; 
v_symPrios_2135_ = lean_ctor_get(v_params_2122_, 5);
lean_inc_ref(v_symPrios_2135_);
lean_dec_ref(v_params_2122_);
v___x_2136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__1));
v___x_2137_ = lean_name_append_index_after(v___x_2136_, v_idx_2129_);
v___x_2138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
lean_ctor_set(v___x_2138_, 1, v_p_2123_);
v___x_2139_ = 0;
v___x_2140_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2138_, v_fst_2124_, v_fst_2125_, v_kind_2128_, v_symPrios_2135_, v___x_2126_, v___x_2139_, v_minIndexable_2127_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2151_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2151_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2151_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
if (lean_obj_tag(v_a_2141_) == 1)
{
lean_object* v_val_2145_; lean_object* v___x_2147_; 
v_val_2145_ = lean_ctor_get(v_a_2141_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v_a_2141_, 1);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v_val_2145_);
v___x_2147_ = v___x_2143_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_val_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_del_object(v___x_2143_);
lean_dec(v_a_2141_);
v___x_2149_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3);
v___x_2150_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2149_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
return v___x_2150_;
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
v_a_2152_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2140_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2140_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed(lean_object* v_params_2160_, lean_object* v_p_2161_, lean_object* v_fst_2162_, lean_object* v_fst_2163_, lean_object* v___x_2164_, lean_object* v_minIndexable_2165_, lean_object* v_kind_2166_, lean_object* v_idx_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
uint8_t v___x_15051__boxed_2173_; uint8_t v_minIndexable_boxed_2174_; lean_object* v_res_2175_; 
v___x_15051__boxed_2173_ = lean_unbox(v___x_2164_);
v_minIndexable_boxed_2174_ = lean_unbox(v_minIndexable_2165_);
v_res_2175_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(v_params_2160_, v_p_2161_, v_fst_2162_, v_fst_2163_, v___x_15051__boxed_2173_, v_minIndexable_boxed_2174_, v_kind_2166_, v_idx_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
return v_res_2175_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_box(1);
v___x_2177_ = l_Lean_MessageData_ofFormat(v___x_2176_);
return v___x_2177_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__2));
v___x_2182_ = l_Lean_MessageData_ofFormat(v___x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(lean_object* v_x_2183_, lean_object* v_x_2184_){
_start:
{
if (lean_obj_tag(v_x_2184_) == 0)
{
return v_x_2183_;
}
else
{
lean_object* v_head_2185_; lean_object* v_tail_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2208_; 
v_head_2185_ = lean_ctor_get(v_x_2184_, 0);
v_tail_2186_ = lean_ctor_get(v_x_2184_, 1);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_x_2184_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2188_ = v_x_2184_;
v_isShared_2189_ = v_isSharedCheck_2208_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_tail_2186_);
lean_inc(v_head_2185_);
lean_dec(v_x_2184_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2208_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_before_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2206_; 
v_before_2190_ = lean_ctor_get(v_head_2185_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_head_2185_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v_head_2185_, 1);
lean_dec(v_unused_2207_);
v___x_2192_ = v_head_2185_;
v_isShared_2193_ = v_isSharedCheck_2206_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_before_2190_);
lean_dec(v_head_2185_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2206_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2193_ == 0)
{
lean_ctor_set_tag(v___x_2192_, 7);
lean_ctor_set(v___x_2192_, 1, v___x_2194_);
lean_ctor_set(v___x_2192_, 0, v_x_2183_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_x_2183_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2197_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3);
if (v_isShared_2189_ == 0)
{
lean_ctor_set_tag(v___x_2188_, 7);
lean_ctor_set(v___x_2188_, 1, v___x_2197_);
lean_ctor_set(v___x_2188_, 0, v___x_2196_);
v___x_2199_ = v___x_2188_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = l_Lean_MessageData_ofSyntax(v_before_2190_);
v___x_2201_ = l_Lean_indentD(v___x_2200_);
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2199_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v_x_2183_ = v___x_2202_;
v_x_2184_ = v_tail_2186_;
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
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__1));
v___x_2213_ = l_Lean_MessageData_ofFormat(v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(lean_object* v_msgData_2214_, lean_object* v_macroStack_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2218_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2216_);
v___x_2219_ = l_Lean_Elab_pp_macroStack;
v___x_2220_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_2218_, v___x_2219_);
lean_dec_ref(v___x_2218_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; 
lean_dec(v_macroStack_2215_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v_msgData_2214_);
return v___x_2221_;
}
else
{
if (lean_obj_tag(v_macroStack_2215_) == 0)
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_msgData_2214_);
return v___x_2222_;
}
else
{
lean_object* v_head_2223_; lean_object* v_after_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2239_; 
v_head_2223_ = lean_ctor_get(v_macroStack_2215_, 0);
lean_inc(v_head_2223_);
v_after_2224_ = lean_ctor_get(v_head_2223_, 1);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_head_2223_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; 
v_unused_2240_ = lean_ctor_get(v_head_2223_, 0);
lean_dec(v_unused_2240_);
v___x_2226_ = v_head_2223_;
v_isShared_2227_ = v_isSharedCheck_2239_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_after_2224_);
lean_dec(v_head_2223_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2239_;
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
lean_ctor_set(v___x_2226_, 0, v_msgData_2214_);
v___x_2230_ = v___x_2226_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_msgData_2214_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v_msgData_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2231_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2);
v___x_2232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2230_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = l_Lean_MessageData_ofSyntax(v_after_2224_);
v___x_2234_ = l_Lean_indentD(v___x_2233_);
v_msgData_2235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2235_, 0, v___x_2232_);
lean_ctor_set(v_msgData_2235_, 1, v___x_2234_);
v___x_2236_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(v_msgData_2235_, v_macroStack_2215_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
return v___x_2237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_2241_, lean_object* v_macroStack_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2241_, v_macroStack_2242_, v___y_2243_);
lean_dec_ref(v___y_2243_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(lean_object* v_msg_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_ref_2254_; lean_object* v_macroStack_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v_a_2258_; lean_object* v___x_2259_; lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2268_; 
v_ref_2254_ = lean_ctor_get(v___y_2251_, 2);
v_macroStack_2255_ = lean_ctor_get(v___y_2247_, 1);
v___x_2256_ = l_Lean_Elab_getBetterRef(v_ref_2254_, v_macroStack_2255_);
v___x_2257_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2246_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref(v___x_2257_);
lean_inc(v_macroStack_2255_);
v___x_2259_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_a_2258_, v_macroStack_2255_, v___y_2251_);
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2268_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2268_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2256_);
lean_ctor_set(v___x_2264_, 1, v_a_2260_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set_tag(v___x_2262_, 1);
lean_ctor_set(v___x_2262_, 0, v___x_2264_);
v___x_2266_ = v___x_2262_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg___boxed(lean_object* v_msg_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
return v_res_2277_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2280_ = l_Lean_stringToMessageData(v___x_2279_);
return v___x_2280_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2283_ = l_Lean_stringToMessageData(v___x_2282_);
return v___x_2283_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2286_ = l_Lean_stringToMessageData(v___x_2285_);
return v___x_2286_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_2289_ = l_Lean_stringToMessageData(v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2292_, lean_object* v_p_2293_, lean_object* v_mod_x3f_2294_, lean_object* v_term_2295_, uint8_t v_minIndexable_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___y_2305_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; uint8_t v___y_2445_; uint8_t v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v_kind_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v_toCold_2666_; lean_object* v_currRecDepth_2667_; lean_object* v_ref_2668_; uint16_t v_optionFlags_2669_; uint8_t v_suppressElabErrors_2670_; uint8_t v_isRecordingDeps_2671_; lean_object* v_ref_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_toCold_2666_ = lean_ctor_get(v_a_2301_, 0);
v_currRecDepth_2667_ = lean_ctor_get(v_a_2301_, 1);
v_ref_2668_ = lean_ctor_get(v_a_2301_, 2);
v_optionFlags_2669_ = lean_ctor_get_uint16(v_a_2301_, sizeof(void*)*3);
v_suppressElabErrors_2670_ = lean_ctor_get_uint8(v_a_2301_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2671_ = lean_ctor_get_uint8(v_a_2301_, sizeof(void*)*3 + 3);
v_ref_2672_ = l_Lean_replaceRef(v_p_2293_, v_ref_2668_);
lean_inc(v_currRecDepth_2667_);
lean_inc_ref(v_toCold_2666_);
v___x_2673_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2673_, 0, v_toCold_2666_);
lean_ctor_set(v___x_2673_, 1, v_currRecDepth_2667_);
lean_ctor_set(v___x_2673_, 2, v_ref_2672_);
lean_ctor_set_uint16(v___x_2673_, sizeof(void*)*3, v_optionFlags_2669_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*3 + 2, v_suppressElabErrors_2670_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*3 + 3, v_isRecordingDeps_2671_);
v___x_2674_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2292_, v___x_2673_, v_a_2302_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_dec_ref_known(v___x_2674_, 1);
if (lean_obj_tag(v_mod_x3f_2294_) == 1)
{
lean_object* v_val_2675_; lean_object* v___x_2676_; 
v_val_2675_ = lean_ctor_get(v_mod_x3f_2294_, 0);
lean_inc(v_val_2675_);
v___x_2676_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2675_, v___x_2673_, v_a_2302_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
switch(lean_obj_tag(v_a_2677_))
{
case 0:
{
lean_object* v_k_2678_; 
v_k_2678_ = lean_ctor_get(v_a_2677_, 0);
lean_inc(v_k_2678_);
lean_dec_ref_known(v_a_2677_, 1);
if (lean_obj_tag(v_k_2678_) == 9)
{
lean_dec_ref_known(v_mod_x3f_2294_, 1);
lean_dec(v_term_2295_);
lean_dec(v_p_2293_);
lean_dec_ref(v_params_2292_);
v___y_2625_ = v_a_2297_;
v___y_2626_ = v_a_2298_;
v___y_2627_ = v_a_2299_;
v___y_2628_ = v_a_2300_;
v___y_2629_ = v___x_2673_;
v___y_2630_ = v_a_2302_;
goto v___jp_2624_;
}
else
{
v_kind_2556_ = v_k_2678_;
v___y_2557_ = v_a_2297_;
v___y_2558_ = v_a_2298_;
v___y_2559_ = v_a_2299_;
v___y_2560_ = v_a_2300_;
v___y_2561_ = v___x_2673_;
v___y_2562_ = v_a_2302_;
goto v___jp_2555_;
}
}
case 1:
{
lean_dec_ref_known(v_a_2677_, 0);
lean_dec_ref_known(v_mod_x3f_2294_, 1);
lean_dec(v_term_2295_);
lean_dec(v_p_2293_);
lean_dec_ref(v_params_2292_);
v___y_2642_ = v_a_2297_;
v___y_2643_ = v_a_2298_;
v___y_2644_ = v_a_2299_;
v___y_2645_ = v_a_2300_;
v___y_2646_ = v___x_2673_;
v___y_2647_ = v_a_2302_;
goto v___jp_2641_;
}
case 3:
{
v___y_2659_ = v_a_2297_;
v___y_2660_ = v_a_2298_;
v___y_2661_ = v_a_2299_;
v___y_2662_ = v_a_2300_;
v___y_2663_ = v___x_2673_;
v___y_2664_ = v_a_2302_;
goto v___jp_2658_;
}
case 5:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec_ref_known(v_a_2677_, 1);
lean_dec_ref_known(v_mod_x3f_2294_, 1);
lean_dec(v_term_2295_);
lean_dec(v_p_2293_);
lean_dec_ref(v_params_2292_);
v___x_2679_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2680_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2679_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v___x_2673_, v_a_2302_);
lean_dec_ref_known(v___x_2673_, 3);
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2680_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2680_);
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
case 8:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec_ref_known(v_a_2677_, 0);
lean_dec_ref_known(v_mod_x3f_2294_, 1);
lean_dec(v_term_2295_);
lean_dec(v_p_2293_);
lean_dec_ref(v_params_2292_);
v___x_2689_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2690_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2689_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v___x_2673_, v_a_2302_);
lean_dec_ref_known(v___x_2673_, 3);
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2690_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2690_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
case 10:
{
lean_dec_ref_known(v_a_2677_, 0);
lean_dec_ref_known(v_mod_x3f_2294_, 1);
lean_dec(v_term_2295_);
lean_dec(v_p_2293_);
lean_dec_ref(v_params_2292_);
v___y_2642_ = v_a_2297_;
v___y_2643_ = v_a_2298_;
v___y_2644_ = v_a_2299_;
v___y_2645_ = v_a_2300_;
v___y_2646_ = v___x_2673_;
v___y_2647_ = v_a_2302_;
goto v___jp_2641_;
}
default: 
{
lean_dec(v_a_2677_);
lean_dec_ref_known(v_mod_x3f_2294_, 1);
lean_dec(v_term_2295_);
lean_dec(v_p_2293_);
lean_dec_ref(v_params_2292_);
v___y_2625_ = v_a_2297_;
v___y_2626_ = v_a_2298_;
v___y_2627_ = v_a_2299_;
v___y_2628_ = v_a_2300_;
v___y_2629_ = v___x_2673_;
v___y_2630_ = v_a_2302_;
goto v___jp_2624_;
}
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec_ref_known(v_mod_x3f_2294_, 1);
lean_dec_ref_known(v___x_2673_, 3);
lean_dec(v_term_2295_);
lean_dec(v_p_2293_);
lean_dec_ref(v_params_2292_);
v_a_2699_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2676_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2676_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
else
{
v___y_2659_ = v_a_2297_;
v___y_2660_ = v_a_2298_;
v___y_2661_ = v_a_2299_;
v___y_2662_ = v_a_2300_;
v___y_2663_ = v___x_2673_;
v___y_2664_ = v_a_2302_;
goto v___jp_2658_;
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec_ref_known(v___x_2673_, 3);
lean_dec(v_term_2295_);
lean_dec(v_mod_x3f_2294_);
lean_dec(v_p_2293_);
lean_dec_ref(v_params_2292_);
v_a_2707_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2674_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2674_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
v___jp_2304_:
{
lean_object* v_config_2306_; lean_object* v_extensions_2307_; lean_object* v_extra_2308_; lean_object* v_extraInj_2309_; lean_object* v_extraFacts_2310_; lean_object* v_symPrios_2311_; lean_object* v_norm_2312_; lean_object* v_normProcs_2313_; lean_object* v_anchorRefs_x3f_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2323_; 
v_config_2306_ = lean_ctor_get(v_params_2292_, 0);
v_extensions_2307_ = lean_ctor_get(v_params_2292_, 1);
v_extra_2308_ = lean_ctor_get(v_params_2292_, 2);
v_extraInj_2309_ = lean_ctor_get(v_params_2292_, 3);
v_extraFacts_2310_ = lean_ctor_get(v_params_2292_, 4);
v_symPrios_2311_ = lean_ctor_get(v_params_2292_, 5);
v_norm_2312_ = lean_ctor_get(v_params_2292_, 6);
v_normProcs_2313_ = lean_ctor_get(v_params_2292_, 7);
v_anchorRefs_x3f_2314_ = lean_ctor_get(v_params_2292_, 8);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_params_2292_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2316_ = v_params_2292_;
v_isShared_2317_ = v_isSharedCheck_2323_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_anchorRefs_x3f_2314_);
lean_inc(v_normProcs_2313_);
lean_inc(v_norm_2312_);
lean_inc(v_symPrios_2311_);
lean_inc(v_extraFacts_2310_);
lean_inc(v_extraInj_2309_);
lean_inc(v_extra_2308_);
lean_inc(v_extensions_2307_);
lean_inc(v_config_2306_);
lean_dec(v_params_2292_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2323_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2318_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2310_, v___y_2305_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 4, v___x_2318_);
v___x_2320_ = v___x_2316_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_config_2306_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_extensions_2307_);
lean_ctor_set(v_reuseFailAlloc_2322_, 2, v_extra_2308_);
lean_ctor_set(v_reuseFailAlloc_2322_, 3, v_extraInj_2309_);
lean_ctor_set(v_reuseFailAlloc_2322_, 4, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2322_, 5, v_symPrios_2311_);
lean_ctor_set(v_reuseFailAlloc_2322_, 6, v_norm_2312_);
lean_ctor_set(v_reuseFailAlloc_2322_, 7, v_normProcs_2313_);
lean_ctor_set(v_reuseFailAlloc_2322_, 8, v_anchorRefs_x3f_2314_);
v___x_2320_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
return v___x_2321_;
}
}
}
v___jp_2324_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2334_ = lean_array_get_size(v___y_2327_);
lean_dec_ref(v___y_2327_);
v___x_2335_ = lean_unsigned_to_nat(0u);
v___x_2336_ = lean_nat_dec_eq(v___x_2334_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec_ref(v___y_2325_);
lean_dec_ref(v_params_2292_);
v___x_2337_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2338_ = l_Lean_indentExpr(v___y_2326_);
v___x_2339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2337_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2339_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec_ref(v___y_2332_);
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
else
{
lean_dec_ref(v___y_2332_);
lean_dec_ref(v___y_2326_);
v___y_2305_ = v___y_2325_;
goto v___jp_2304_;
}
}
v___jp_2349_:
{
if (lean_obj_tag(v_mod_x3f_2294_) == 0)
{
v___y_2325_ = v___y_2356_;
v___y_2326_ = v___y_2355_;
v___y_2327_ = v___y_2354_;
v___y_2328_ = v___y_2351_;
v___y_2329_ = v___y_2353_;
v___y_2330_ = v___y_2357_;
v___y_2331_ = v___y_2352_;
v___y_2332_ = v___y_2350_;
v___y_2333_ = v___y_2358_;
goto v___jp_2324_;
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref_known(v_mod_x3f_2294_, 1);
lean_dec_ref(v___y_2356_);
lean_dec_ref(v___y_2354_);
lean_dec_ref(v_params_2292_);
v___x_2359_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2360_ = l_Lean_indentExpr(v___y_2355_);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2361_, v___y_2351_, v___y_2353_, v___y_2357_, v___y_2352_, v___y_2350_, v___y_2358_);
lean_dec_ref(v___y_2350_);
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
v___jp_2371_:
{
lean_object* v___x_2388_; 
lean_inc(v___y_2387_);
lean_inc(v___y_2385_);
lean_inc_ref(v___y_2384_);
v___x_2388_ = lean_apply_7(v___y_2378_, v___y_2377_, v___y_2379_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, lean_box(0));
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2398_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2398_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2398_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2396_; 
v___x_2393_ = l_Lean_PersistentArray_push___redArg(v___y_2373_, v_a_2389_);
v___x_2394_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2394_, 0, v___y_2381_);
lean_ctor_set(v___x_2394_, 1, v___y_2376_);
lean_ctor_set(v___x_2394_, 2, v___x_2393_);
lean_ctor_set(v___x_2394_, 3, v___y_2374_);
lean_ctor_set(v___x_2394_, 4, v___y_2382_);
lean_ctor_set(v___x_2394_, 5, v___y_2372_);
lean_ctor_set(v___x_2394_, 6, v___y_2380_);
lean_ctor_set(v___x_2394_, 7, v___y_2375_);
lean_ctor_set(v___x_2394_, 8, v___y_2383_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2394_);
v___x_2396_ = v___x_2391_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec_ref(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec_ref(v___y_2372_);
v_a_2399_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2388_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2388_);
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
v___jp_2407_:
{
lean_object* v___x_2424_; 
v___x_2424_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2296_, v___y_2412_, v___y_2416_, v___y_2415_, v___y_2423_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_dec_ref_known(v___x_2424_, 1);
v___y_2372_ = v___y_2417_;
v___y_2373_ = v___y_2408_;
v___y_2374_ = v___y_2409_;
v___y_2375_ = v___y_2418_;
v___y_2376_ = v___y_2410_;
v___y_2377_ = v___y_2411_;
v___y_2378_ = v___y_2419_;
v___y_2379_ = v___y_2420_;
v___y_2380_ = v___y_2422_;
v___y_2381_ = v___y_2421_;
v___y_2382_ = v___y_2413_;
v___y_2383_ = v___y_2414_;
v___y_2384_ = v___y_2412_;
v___y_2385_ = v___y_2416_;
v___y_2386_ = v___y_2415_;
v___y_2387_ = v___y_2423_;
goto v___jp_2371_;
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec_ref(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec_ref(v___y_2408_);
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
v___jp_2433_:
{
if (v___y_2445_ == 0)
{
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
v___y_2350_ = v___y_2435_;
v___y_2351_ = v___y_2434_;
v___y_2352_ = v___y_2436_;
v___y_2353_ = v___y_2437_;
v___y_2354_ = v___y_2442_;
v___y_2355_ = v___y_2441_;
v___y_2356_ = v___y_2440_;
v___y_2357_ = v___y_2443_;
v___y_2358_ = v___y_2444_;
goto v___jp_2349_;
}
else
{
lean_object* v_extra_2446_; 
lean_dec_ref(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v_mod_x3f_2294_);
v_extra_2446_ = lean_ctor_get(v_params_2292_, 2);
lean_inc_ref(v_extra_2446_);
if (lean_obj_tag(v___y_2439_) == 2)
{
lean_object* v_config_2447_; lean_object* v_extensions_2448_; lean_object* v_extraInj_2449_; lean_object* v_extraFacts_2450_; lean_object* v_symPrios_2451_; lean_object* v_norm_2452_; lean_object* v_normProcs_2453_; lean_object* v_anchorRefs_x3f_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2509_; 
v_config_2447_ = lean_ctor_get(v_params_2292_, 0);
v_extensions_2448_ = lean_ctor_get(v_params_2292_, 1);
v_extraInj_2449_ = lean_ctor_get(v_params_2292_, 3);
v_extraFacts_2450_ = lean_ctor_get(v_params_2292_, 4);
v_symPrios_2451_ = lean_ctor_get(v_params_2292_, 5);
v_norm_2452_ = lean_ctor_get(v_params_2292_, 6);
v_normProcs_2453_ = lean_ctor_get(v_params_2292_, 7);
v_anchorRefs_x3f_2454_ = lean_ctor_get(v_params_2292_, 8);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_params_2292_);
if (v_isSharedCheck_2509_ == 0)
{
lean_object* v_unused_2510_; 
v_unused_2510_ = lean_ctor_get(v_params_2292_, 2);
lean_dec(v_unused_2510_);
v___x_2456_ = v_params_2292_;
v_isShared_2457_ = v_isSharedCheck_2509_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_anchorRefs_x3f_2454_);
lean_inc(v_normProcs_2453_);
lean_inc(v_norm_2452_);
lean_inc(v_symPrios_2451_);
lean_inc(v_extraFacts_2450_);
lean_inc(v_extraInj_2449_);
lean_inc(v_extensions_2448_);
lean_inc(v_config_2447_);
lean_dec(v_params_2292_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2509_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v_size_2458_; uint8_t v_gen_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2508_; 
v_size_2458_ = lean_ctor_get(v_extra_2446_, 2);
v_gen_2459_ = lean_ctor_get_uint8(v___y_2439_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___y_2439_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2461_ = v___y_2439_;
v_isShared_2462_ = v_isSharedCheck_2508_;
goto v_resetjp_2460_;
}
else
{
lean_dec(v___y_2439_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2508_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; 
v___x_2463_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2296_, v___y_2443_, v___y_2436_, v___y_2435_, v___y_2444_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v___x_2465_; 
lean_dec_ref_known(v___x_2463_, 1);
if (v_isShared_2462_ == 0)
{
lean_ctor_set_tag(v___x_2461_, 0);
v___x_2465_ = v___x_2461_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2499_, 0, v_gen_2459_);
v___x_2465_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; 
lean_inc_ref(v___y_2438_);
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2435_);
lean_inc(v___y_2436_);
lean_inc_ref(v___y_2443_);
lean_inc(v_size_2458_);
v___x_2466_ = lean_apply_7(v___y_2438_, v___x_2465_, v_size_2458_, v___y_2443_, v___y_2436_, v___y_2435_, v___y_2444_, lean_box(0));
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
v___x_2468_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2468_, 0, v_gen_2459_);
lean_inc(v___y_2444_);
lean_inc(v___y_2436_);
lean_inc_ref(v___y_2443_);
lean_inc(v_size_2458_);
v___x_2469_ = lean_apply_7(v___y_2438_, v___x_2468_, v_size_2458_, v___y_2443_, v___y_2436_, v___y_2435_, v___y_2444_, lean_box(0));
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2482_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2472_ = v___x_2469_;
v_isShared_2473_ = v_isSharedCheck_2482_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2469_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2482_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2474_ = l_Lean_PersistentArray_push___redArg(v_extra_2446_, v_a_2467_);
v___x_2475_ = l_Lean_PersistentArray_push___redArg(v___x_2474_, v_a_2470_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 2, v___x_2475_);
v___x_2477_ = v___x_2456_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_config_2447_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v_extensions_2448_);
lean_ctor_set(v_reuseFailAlloc_2481_, 2, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2481_, 3, v_extraInj_2449_);
lean_ctor_set(v_reuseFailAlloc_2481_, 4, v_extraFacts_2450_);
lean_ctor_set(v_reuseFailAlloc_2481_, 5, v_symPrios_2451_);
lean_ctor_set(v_reuseFailAlloc_2481_, 6, v_norm_2452_);
lean_ctor_set(v_reuseFailAlloc_2481_, 7, v_normProcs_2453_);
lean_ctor_set(v_reuseFailAlloc_2481_, 8, v_anchorRefs_x3f_2454_);
v___x_2477_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2479_; 
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2477_);
v___x_2479_ = v___x_2472_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_a_2467_);
lean_del_object(v___x_2456_);
lean_dec(v_anchorRefs_x3f_2454_);
lean_dec_ref(v_normProcs_2453_);
lean_dec_ref(v_norm_2452_);
lean_dec_ref(v_symPrios_2451_);
lean_dec_ref(v_extraFacts_2450_);
lean_dec_ref(v_extraInj_2449_);
lean_dec_ref(v_extensions_2448_);
lean_dec_ref(v_config_2447_);
lean_dec_ref(v_extra_2446_);
v_a_2483_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2469_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2469_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_del_object(v___x_2456_);
lean_dec(v_anchorRefs_x3f_2454_);
lean_dec_ref(v_normProcs_2453_);
lean_dec_ref(v_norm_2452_);
lean_dec_ref(v_symPrios_2451_);
lean_dec_ref(v_extraFacts_2450_);
lean_dec_ref(v_extraInj_2449_);
lean_dec_ref(v_extensions_2448_);
lean_dec_ref(v_config_2447_);
lean_dec_ref(v_extra_2446_);
lean_dec_ref(v___y_2438_);
lean_dec_ref(v___y_2435_);
v_a_2491_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2466_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2466_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_del_object(v___x_2461_);
lean_del_object(v___x_2456_);
lean_dec(v_anchorRefs_x3f_2454_);
lean_dec_ref(v_normProcs_2453_);
lean_dec_ref(v_norm_2452_);
lean_dec_ref(v_symPrios_2451_);
lean_dec_ref(v_extraFacts_2450_);
lean_dec_ref(v_extraInj_2449_);
lean_dec_ref(v_extensions_2448_);
lean_dec_ref(v_config_2447_);
lean_dec_ref(v_extra_2446_);
lean_dec_ref(v___y_2438_);
lean_dec_ref(v___y_2435_);
v_a_2500_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2463_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2463_);
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
}
}
else
{
switch(lean_obj_tag(v___y_2439_))
{
case 0:
{
lean_object* v_config_2511_; lean_object* v_extensions_2512_; lean_object* v_extraInj_2513_; lean_object* v_extraFacts_2514_; lean_object* v_symPrios_2515_; lean_object* v_norm_2516_; lean_object* v_normProcs_2517_; lean_object* v_anchorRefs_x3f_2518_; lean_object* v_size_2519_; 
v_config_2511_ = lean_ctor_get(v_params_2292_, 0);
lean_inc_ref(v_config_2511_);
v_extensions_2512_ = lean_ctor_get(v_params_2292_, 1);
lean_inc_ref(v_extensions_2512_);
v_extraInj_2513_ = lean_ctor_get(v_params_2292_, 3);
lean_inc_ref(v_extraInj_2513_);
v_extraFacts_2514_ = lean_ctor_get(v_params_2292_, 4);
lean_inc_ref(v_extraFacts_2514_);
v_symPrios_2515_ = lean_ctor_get(v_params_2292_, 5);
lean_inc_ref(v_symPrios_2515_);
v_norm_2516_ = lean_ctor_get(v_params_2292_, 6);
lean_inc_ref(v_norm_2516_);
v_normProcs_2517_ = lean_ctor_get(v_params_2292_, 7);
lean_inc_ref(v_normProcs_2517_);
v_anchorRefs_x3f_2518_ = lean_ctor_get(v_params_2292_, 8);
lean_inc(v_anchorRefs_x3f_2518_);
lean_dec_ref(v_params_2292_);
v_size_2519_ = lean_ctor_get(v_extra_2446_, 2);
lean_inc(v_size_2519_);
v___y_2408_ = v_extra_2446_;
v___y_2409_ = v_extraInj_2513_;
v___y_2410_ = v_extensions_2512_;
v___y_2411_ = v___y_2439_;
v___y_2412_ = v___y_2443_;
v___y_2413_ = v_extraFacts_2514_;
v___y_2414_ = v_anchorRefs_x3f_2518_;
v___y_2415_ = v___y_2435_;
v___y_2416_ = v___y_2436_;
v___y_2417_ = v_symPrios_2515_;
v___y_2418_ = v_normProcs_2517_;
v___y_2419_ = v___y_2438_;
v___y_2420_ = v_size_2519_;
v___y_2421_ = v_config_2511_;
v___y_2422_ = v_norm_2516_;
v___y_2423_ = v___y_2444_;
goto v___jp_2407_;
}
case 1:
{
lean_object* v_config_2520_; lean_object* v_extensions_2521_; lean_object* v_extraInj_2522_; lean_object* v_extraFacts_2523_; lean_object* v_symPrios_2524_; lean_object* v_norm_2525_; lean_object* v_normProcs_2526_; lean_object* v_anchorRefs_x3f_2527_; lean_object* v_size_2528_; 
v_config_2520_ = lean_ctor_get(v_params_2292_, 0);
lean_inc_ref(v_config_2520_);
v_extensions_2521_ = lean_ctor_get(v_params_2292_, 1);
lean_inc_ref(v_extensions_2521_);
v_extraInj_2522_ = lean_ctor_get(v_params_2292_, 3);
lean_inc_ref(v_extraInj_2522_);
v_extraFacts_2523_ = lean_ctor_get(v_params_2292_, 4);
lean_inc_ref(v_extraFacts_2523_);
v_symPrios_2524_ = lean_ctor_get(v_params_2292_, 5);
lean_inc_ref(v_symPrios_2524_);
v_norm_2525_ = lean_ctor_get(v_params_2292_, 6);
lean_inc_ref(v_norm_2525_);
v_normProcs_2526_ = lean_ctor_get(v_params_2292_, 7);
lean_inc_ref(v_normProcs_2526_);
v_anchorRefs_x3f_2527_ = lean_ctor_get(v_params_2292_, 8);
lean_inc(v_anchorRefs_x3f_2527_);
lean_dec_ref(v_params_2292_);
v_size_2528_ = lean_ctor_get(v_extra_2446_, 2);
lean_inc(v_size_2528_);
v___y_2408_ = v_extra_2446_;
v___y_2409_ = v_extraInj_2522_;
v___y_2410_ = v_extensions_2521_;
v___y_2411_ = v___y_2439_;
v___y_2412_ = v___y_2443_;
v___y_2413_ = v_extraFacts_2523_;
v___y_2414_ = v_anchorRefs_x3f_2527_;
v___y_2415_ = v___y_2435_;
v___y_2416_ = v___y_2436_;
v___y_2417_ = v_symPrios_2524_;
v___y_2418_ = v_normProcs_2526_;
v___y_2419_ = v___y_2438_;
v___y_2420_ = v_size_2528_;
v___y_2421_ = v_config_2520_;
v___y_2422_ = v_norm_2525_;
v___y_2423_ = v___y_2444_;
goto v___jp_2407_;
}
default: 
{
lean_object* v_config_2529_; lean_object* v_extensions_2530_; lean_object* v_extraInj_2531_; lean_object* v_extraFacts_2532_; lean_object* v_symPrios_2533_; lean_object* v_norm_2534_; lean_object* v_normProcs_2535_; lean_object* v_anchorRefs_x3f_2536_; lean_object* v_size_2537_; 
v_config_2529_ = lean_ctor_get(v_params_2292_, 0);
lean_inc_ref(v_config_2529_);
v_extensions_2530_ = lean_ctor_get(v_params_2292_, 1);
lean_inc_ref(v_extensions_2530_);
v_extraInj_2531_ = lean_ctor_get(v_params_2292_, 3);
lean_inc_ref(v_extraInj_2531_);
v_extraFacts_2532_ = lean_ctor_get(v_params_2292_, 4);
lean_inc_ref(v_extraFacts_2532_);
v_symPrios_2533_ = lean_ctor_get(v_params_2292_, 5);
lean_inc_ref(v_symPrios_2533_);
v_norm_2534_ = lean_ctor_get(v_params_2292_, 6);
lean_inc_ref(v_norm_2534_);
v_normProcs_2535_ = lean_ctor_get(v_params_2292_, 7);
lean_inc_ref(v_normProcs_2535_);
v_anchorRefs_x3f_2536_ = lean_ctor_get(v_params_2292_, 8);
lean_inc(v_anchorRefs_x3f_2536_);
lean_dec_ref(v_params_2292_);
v_size_2537_ = lean_ctor_get(v_extra_2446_, 2);
lean_inc(v_size_2537_);
v___y_2372_ = v_symPrios_2533_;
v___y_2373_ = v_extra_2446_;
v___y_2374_ = v_extraInj_2531_;
v___y_2375_ = v_normProcs_2535_;
v___y_2376_ = v_extensions_2530_;
v___y_2377_ = v___y_2439_;
v___y_2378_ = v___y_2438_;
v___y_2379_ = v_size_2537_;
v___y_2380_ = v_norm_2534_;
v___y_2381_ = v_config_2529_;
v___y_2382_ = v_extraFacts_2532_;
v___y_2383_ = v_anchorRefs_x3f_2536_;
v___y_2384_ = v___y_2443_;
v___y_2385_ = v___y_2436_;
v___y_2386_ = v___y_2435_;
v___y_2387_ = v___y_2444_;
goto v___jp_2371_;
}
}
}
}
}
v___jp_2538_:
{
uint8_t v___x_2551_; 
v___x_2551_ = l_Lean_Expr_isForall(v___y_2543_);
if (v___x_2551_ == 0)
{
v___y_2434_ = v___y_2545_;
v___y_2435_ = v___y_2549_;
v___y_2436_ = v___y_2548_;
v___y_2437_ = v___y_2546_;
v___y_2438_ = v___y_2541_;
v___y_2439_ = v___y_2540_;
v___y_2440_ = v___y_2542_;
v___y_2441_ = v___y_2543_;
v___y_2442_ = v___y_2544_;
v___y_2443_ = v___y_2547_;
v___y_2444_ = v___y_2550_;
v___y_2445_ = v___x_2551_;
goto v___jp_2433_;
}
else
{
if (v___y_2539_ == 0)
{
v___y_2434_ = v___y_2545_;
v___y_2435_ = v___y_2549_;
v___y_2436_ = v___y_2548_;
v___y_2437_ = v___y_2546_;
v___y_2438_ = v___y_2541_;
v___y_2439_ = v___y_2540_;
v___y_2440_ = v___y_2542_;
v___y_2441_ = v___y_2543_;
v___y_2442_ = v___y_2544_;
v___y_2443_ = v___y_2547_;
v___y_2444_ = v___y_2550_;
v___y_2445_ = v___x_2551_;
goto v___jp_2433_;
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2552_ = lean_array_get_size(v___y_2544_);
v___x_2553_ = lean_unsigned_to_nat(0u);
v___x_2554_ = lean_nat_dec_eq(v___x_2552_, v___x_2553_);
if (v___x_2554_ == 0)
{
v___y_2434_ = v___y_2545_;
v___y_2435_ = v___y_2549_;
v___y_2436_ = v___y_2548_;
v___y_2437_ = v___y_2546_;
v___y_2438_ = v___y_2541_;
v___y_2439_ = v___y_2540_;
v___y_2440_ = v___y_2542_;
v___y_2441_ = v___y_2543_;
v___y_2442_ = v___y_2544_;
v___y_2443_ = v___y_2547_;
v___y_2444_ = v___y_2550_;
v___y_2445_ = v___x_2551_;
goto v___jp_2433_;
}
else
{
if (lean_obj_tag(v_mod_x3f_2294_) == 0)
{
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
v___y_2350_ = v___y_2549_;
v___y_2351_ = v___y_2545_;
v___y_2352_ = v___y_2548_;
v___y_2353_ = v___y_2546_;
v___y_2354_ = v___y_2544_;
v___y_2355_ = v___y_2543_;
v___y_2356_ = v___y_2542_;
v___y_2357_ = v___y_2547_;
v___y_2358_ = v___y_2550_;
goto v___jp_2349_;
}
else
{
v___y_2434_ = v___y_2545_;
v___y_2435_ = v___y_2549_;
v___y_2436_ = v___y_2548_;
v___y_2437_ = v___y_2546_;
v___y_2438_ = v___y_2541_;
v___y_2439_ = v___y_2540_;
v___y_2440_ = v___y_2542_;
v___y_2441_ = v___y_2543_;
v___y_2442_ = v___y_2544_;
v___y_2443_ = v___y_2547_;
v___y_2444_ = v___y_2550_;
v___y_2445_ = v___x_2551_;
goto v___jp_2433_;
}
}
}
}
}
v___jp_2555_:
{
lean_object* v___x_2563_; uint8_t v___x_2564_; lean_object* v___x_2565_; lean_object* v___f_2566_; lean_object* v___x_2567_; 
v___x_2563_ = lean_box(0);
v___x_2564_ = 1;
v___x_2565_ = lean_box(v___x_2564_);
lean_inc(v_p_2293_);
v___f_2566_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2566_, 0, v_p_2293_);
lean_closure_set(v___f_2566_, 1, v_term_2295_);
lean_closure_set(v___f_2566_, 2, v___x_2563_);
lean_closure_set(v___f_2566_, 3, v___x_2565_);
v___x_2567_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2566_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2615_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2615_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2615_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
if (lean_obj_tag(v_a_2568_) == 1)
{
lean_object* v_val_2572_; lean_object* v_snd_2573_; lean_object* v_fst_2574_; lean_object* v_fst_2575_; lean_object* v_snd_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___f_2579_; lean_object* v___x_2580_; 
lean_del_object(v___x_2570_);
v_val_2572_ = lean_ctor_get(v_a_2568_, 0);
lean_inc(v_val_2572_);
lean_dec_ref_known(v_a_2568_, 1);
v_snd_2573_ = lean_ctor_get(v_val_2572_, 1);
lean_inc(v_snd_2573_);
v_fst_2574_ = lean_ctor_get(v_val_2572_, 0);
lean_inc_n(v_fst_2574_, 2);
lean_dec(v_val_2572_);
v_fst_2575_ = lean_ctor_get(v_snd_2573_, 0);
lean_inc_n(v_fst_2575_, 3);
v_snd_2576_ = lean_ctor_get(v_snd_2573_, 1);
lean_inc(v_snd_2576_);
lean_dec(v_snd_2573_);
v___x_2577_ = lean_box(v___x_2564_);
v___x_2578_ = lean_box(v_minIndexable_2296_);
lean_inc_ref(v_params_2292_);
v___f_2579_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed), 13, 6);
lean_closure_set(v___f_2579_, 0, v_params_2292_);
lean_closure_set(v___f_2579_, 1, v_p_2293_);
lean_closure_set(v___f_2579_, 2, v_fst_2574_);
lean_closure_set(v___f_2579_, 3, v_fst_2575_);
lean_closure_set(v___f_2579_, 4, v___x_2577_);
lean_closure_set(v___f_2579_, 5, v___x_2578_);
lean_inc(v___y_2562_);
lean_inc_ref(v___y_2561_);
lean_inc(v___y_2560_);
lean_inc_ref(v___y_2559_);
v___x_2580_ = lean_infer_type(v_fst_2575_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2582_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc_n(v_a_2581_, 2);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2582_ = l_Lean_Meta_isProp(v_a_2581_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; uint8_t v___x_2584_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = lean_unbox(v_a_2583_);
lean_dec(v_a_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_dec(v_a_2581_);
lean_dec_ref(v___f_2579_);
lean_dec(v_snd_2576_);
lean_dec(v_fst_2575_);
lean_dec(v_fst_2574_);
lean_dec(v_kind_2556_);
lean_dec(v_mod_x3f_2294_);
lean_dec_ref(v_params_2292_);
v___x_2585_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2586_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2585_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec_ref(v___y_2561_);
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
else
{
uint8_t v___x_2595_; 
v___x_2595_ = lean_unbox(v_snd_2576_);
lean_dec(v_snd_2576_);
v___y_2539_ = v___x_2595_;
v___y_2540_ = v_kind_2556_;
v___y_2541_ = v___f_2579_;
v___y_2542_ = v_fst_2575_;
v___y_2543_ = v_a_2581_;
v___y_2544_ = v_fst_2574_;
v___y_2545_ = v___y_2557_;
v___y_2546_ = v___y_2558_;
v___y_2547_ = v___y_2559_;
v___y_2548_ = v___y_2560_;
v___y_2549_ = v___y_2561_;
v___y_2550_ = v___y_2562_;
goto v___jp_2538_;
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_a_2581_);
lean_dec_ref(v___f_2579_);
lean_dec(v_snd_2576_);
lean_dec(v_fst_2575_);
lean_dec(v_fst_2574_);
lean_dec_ref(v___y_2561_);
lean_dec(v_kind_2556_);
lean_dec(v_mod_x3f_2294_);
lean_dec_ref(v_params_2292_);
v_a_2596_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2582_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2582_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v___f_2579_);
lean_dec(v_snd_2576_);
lean_dec(v_fst_2575_);
lean_dec(v_fst_2574_);
lean_dec_ref(v___y_2561_);
lean_dec(v_kind_2556_);
lean_dec(v_mod_x3f_2294_);
lean_dec_ref(v_params_2292_);
v_a_2604_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2580_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2580_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v___x_2613_; 
lean_dec(v_a_2568_);
lean_dec_ref(v___y_2561_);
lean_dec(v_kind_2556_);
lean_dec(v_mod_x3f_2294_);
lean_dec(v_p_2293_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v_params_2292_);
v___x_2613_ = v___x_2570_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_params_2292_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v___y_2561_);
lean_dec(v_kind_2556_);
lean_dec(v_mod_x3f_2294_);
lean_dec(v_p_2293_);
lean_dec_ref(v_params_2292_);
v_a_2616_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2567_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2567_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
v___jp_2624_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
v___x_2631_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2632_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2631_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec_ref(v___y_2629_);
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
v___jp_2641_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
v___x_2648_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2649_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2648_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec_ref(v___y_2646_);
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
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
v___jp_2658_:
{
lean_object* v___x_2665_; 
v___x_2665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_kind_2556_ = v___x_2665_;
v___y_2557_ = v___y_2659_;
v___y_2558_ = v___y_2660_;
v___y_2559_ = v___y_2661_;
v___y_2560_ = v___y_2662_;
v___y_2561_ = v___y_2663_;
v___y_2562_ = v___y_2664_;
goto v___jp_2555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2715_, lean_object* v_p_2716_, lean_object* v_mod_x3f_2717_, lean_object* v_term_2718_, lean_object* v_minIndexable_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
uint8_t v_minIndexable_boxed_2727_; lean_object* v_res_2728_; 
v_minIndexable_boxed_2727_ = lean_unbox(v_minIndexable_2719_);
v_res_2728_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2715_, v_p_2716_, v_mod_x3f_2717_, v_term_2718_, v_minIndexable_boxed_2727_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(uint8_t v___x_2729_, uint8_t v___x_2730_, lean_object* v_as_2731_, size_t v_i_2732_, size_t v_stop_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2729_, v___x_2730_, v_as_2731_, v_i_2732_, v_stop_2733_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v___x_2742_, lean_object* v___x_2743_, lean_object* v_as_2744_, lean_object* v_i_2745_, lean_object* v_stop_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
uint8_t v___x_16098__boxed_2754_; uint8_t v___x_16099__boxed_2755_; size_t v_i_boxed_2756_; size_t v_stop_boxed_2757_; lean_object* v_res_2758_; 
v___x_16098__boxed_2754_ = lean_unbox(v___x_2742_);
v___x_16099__boxed_2755_ = lean_unbox(v___x_2743_);
v_i_boxed_2756_ = lean_unbox_usize(v_i_2745_);
lean_dec(v_i_2745_);
v_stop_boxed_2757_ = lean_unbox_usize(v_stop_2746_);
lean_dec(v_stop_2746_);
v_res_2758_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v___x_16098__boxed_2754_, v___x_16099__boxed_2755_, v_as_2744_, v_i_boxed_2756_, v_stop_boxed_2757_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec_ref(v_as_2744_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(lean_object* v_00_u03b1_2759_, lean_object* v_msg_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___boxed(lean_object* v_00_u03b1_2769_, lean_object* v_msg_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(v_00_u03b1_2769_, v_msg_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(lean_object* v_msgData_2779_, lean_object* v_macroStack_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2779_, v_macroStack_2780_, v___y_2785_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___boxed(lean_object* v_msgData_2789_, lean_object* v_macroStack_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(v_msgData_2789_, v_macroStack_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2799_, lean_object* v_val_2800_, lean_object* v___x_2801_, uint8_t v___y_2802_, lean_object* v_____r_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v___x_2811_; lean_object* v_ext_2812_; lean_object* v_toEnvExtension_2813_; lean_object* v_env_2814_; lean_object* v_config_2815_; lean_object* v_extensions_2816_; lean_object* v_extra_2817_; lean_object* v_extraInj_2818_; lean_object* v_extraFacts_2819_; lean_object* v_symPrios_2820_; lean_object* v_norm_2821_; lean_object* v_normProcs_2822_; lean_object* v_anchorRefs_x3f_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2835_; 
v___x_2811_ = lean_st_ref_get(v___y_2809_);
v_ext_2812_ = lean_ctor_get(v_val_2800_, 1);
v_toEnvExtension_2813_ = lean_ctor_get(v_ext_2812_, 0);
v_env_2814_ = lean_ctor_get(v___x_2811_, 0);
lean_inc_ref(v_env_2814_);
lean_dec(v___x_2811_);
v_config_2815_ = lean_ctor_get(v_params_2799_, 0);
v_extensions_2816_ = lean_ctor_get(v_params_2799_, 1);
v_extra_2817_ = lean_ctor_get(v_params_2799_, 2);
v_extraInj_2818_ = lean_ctor_get(v_params_2799_, 3);
v_extraFacts_2819_ = lean_ctor_get(v_params_2799_, 4);
v_symPrios_2820_ = lean_ctor_get(v_params_2799_, 5);
v_norm_2821_ = lean_ctor_get(v_params_2799_, 6);
v_normProcs_2822_ = lean_ctor_get(v_params_2799_, 7);
v_anchorRefs_x3f_2823_ = lean_ctor_get(v_params_2799_, 8);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_params_2799_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2825_ = v_params_2799_;
v_isShared_2826_ = v_isSharedCheck_2835_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_anchorRefs_x3f_2823_);
lean_inc(v_normProcs_2822_);
lean_inc(v_norm_2821_);
lean_inc(v_symPrios_2820_);
lean_inc(v_extraFacts_2819_);
lean_inc(v_extraInj_2818_);
lean_inc(v_extra_2817_);
lean_inc(v_extensions_2816_);
lean_inc(v_config_2815_);
lean_dec(v_params_2799_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2835_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v_asyncMode_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
v_asyncMode_2827_ = lean_ctor_get(v_toEnvExtension_2813_, 2);
v___x_2828_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2801_, v_val_2800_, v_env_2814_, v_asyncMode_2827_, v___y_2802_);
v___x_2829_ = lean_array_push(v_extensions_2816_, v___x_2828_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 1, v___x_2829_);
v___x_2831_ = v___x_2825_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_config_2815_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2834_, 2, v_extra_2817_);
lean_ctor_set(v_reuseFailAlloc_2834_, 3, v_extraInj_2818_);
lean_ctor_set(v_reuseFailAlloc_2834_, 4, v_extraFacts_2819_);
lean_ctor_set(v_reuseFailAlloc_2834_, 5, v_symPrios_2820_);
lean_ctor_set(v_reuseFailAlloc_2834_, 6, v_norm_2821_);
lean_ctor_set(v_reuseFailAlloc_2834_, 7, v_normProcs_2822_);
lean_ctor_set(v_reuseFailAlloc_2834_, 8, v_anchorRefs_x3f_2823_);
v___x_2831_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2836_, lean_object* v_val_2837_, lean_object* v___x_2838_, lean_object* v___y_2839_, lean_object* v_____r_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
uint8_t v___y_30061__boxed_2848_; lean_object* v_res_2849_; 
v___y_30061__boxed_2848_ = lean_unbox(v___y_2839_);
v_res_2849_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2836_, v_val_2837_, v___x_2838_, v___y_30061__boxed_2848_, v_____r_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec_ref(v___x_2838_);
lean_dec_ref(v_val_2837_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2850_, lean_object* v_id_2851_, uint8_t v_minIndexable_2852_, lean_object* v_as_x27_2853_, lean_object* v_b_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
if (lean_obj_tag(v_as_x27_2853_) == 0)
{
lean_object* v___x_2860_; 
lean_dec(v_id_2851_);
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_b_2854_);
return v___x_2860_;
}
else
{
lean_object* v_head_2861_; lean_object* v_tail_2862_; lean_object* v_toCold_2863_; lean_object* v_currRecDepth_2864_; lean_object* v_ref_2865_; uint16_t v_optionFlags_2866_; uint8_t v_suppressElabErrors_2867_; uint8_t v_isRecordingDeps_2868_; uint8_t v___x_2869_; lean_object* v___x_2870_; lean_object* v_ref_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_head_2861_ = lean_ctor_get(v_as_x27_2853_, 0);
v_tail_2862_ = lean_ctor_get(v_as_x27_2853_, 1);
v_toCold_2863_ = lean_ctor_get(v___y_2857_, 0);
v_currRecDepth_2864_ = lean_ctor_get(v___y_2857_, 1);
v_ref_2865_ = lean_ctor_get(v___y_2857_, 2);
v_optionFlags_2866_ = lean_ctor_get_uint16(v___y_2857_, sizeof(void*)*3);
v_suppressElabErrors_2867_ = lean_ctor_get_uint8(v___y_2857_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2868_ = lean_ctor_get_uint8(v___y_2857_, sizeof(void*)*3 + 3);
v___x_2869_ = 0;
v___x_2870_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_ref_2871_ = l_Lean_replaceRef(v_p_2850_, v_ref_2865_);
lean_inc(v_currRecDepth_2864_);
lean_inc_ref(v_toCold_2863_);
v___x_2872_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2872_, 0, v_toCold_2863_);
lean_ctor_set(v___x_2872_, 1, v_currRecDepth_2864_);
lean_ctor_set(v___x_2872_, 2, v_ref_2871_);
lean_ctor_set_uint16(v___x_2872_, sizeof(void*)*3, v_optionFlags_2866_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 2, v_suppressElabErrors_2867_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*3 + 3, v_isRecordingDeps_2868_);
lean_inc(v_head_2861_);
lean_inc(v_id_2851_);
v___x_2873_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2854_, v_id_2851_, v_head_2861_, v___x_2870_, v_minIndexable_2852_, v___x_2869_, v___x_2869_, v___y_2855_, v___y_2856_, v___x_2872_, v___y_2858_);
lean_dec_ref_known(v___x_2872_, 3);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v_as_x27_2853_ = v_tail_2862_;
v_b_2854_ = v_a_2874_;
goto _start;
}
else
{
lean_dec(v_id_2851_);
return v___x_2873_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_2876_, lean_object* v_id_2877_, lean_object* v_minIndexable_2878_, lean_object* v_as_x27_2879_, lean_object* v_b_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v_minIndexable_boxed_2886_; lean_object* v_res_2887_; 
v_minIndexable_boxed_2886_ = lean_unbox(v_minIndexable_2878_);
v_res_2887_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_2876_, v_id_2877_, v_minIndexable_boxed_2886_, v_as_x27_2879_, v_b_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v_as_x27_2879_);
lean_dec(v_p_2876_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
if (lean_obj_tag(v_a_2889_) == 0)
{
lean_object* v___x_2891_; 
v___x_2891_ = l_List_reverse___redArg(v_a_2890_);
return v___x_2891_;
}
else
{
lean_object* v_head_2892_; lean_object* v_tail_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2904_; 
v_head_2892_ = lean_ctor_get(v_a_2889_, 0);
v_tail_2893_ = lean_ctor_get(v_a_2889_, 1);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_a_2889_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2895_ = v_a_2889_;
v_isShared_2896_ = v_isSharedCheck_2904_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_tail_2893_);
lean_inc(v_head_2892_);
lean_dec(v_a_2889_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2904_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v_kind_2897_; uint8_t v___x_2898_; 
v_kind_2897_ = lean_ctor_get(v_head_2892_, 6);
v___x_2898_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_2897_, v_k_2888_);
if (v___x_2898_ == 0)
{
lean_del_object(v___x_2895_);
lean_dec(v_head_2892_);
v_a_2889_ = v_tail_2893_;
goto _start;
}
else
{
lean_object* v___x_2901_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 1, v_a_2890_);
v___x_2901_ = v___x_2895_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_head_2892_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_a_2890_);
v___x_2901_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
v_a_2889_ = v_tail_2893_;
v_a_2890_ = v___x_2901_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_2905_, v_a_2906_, v_a_2907_);
lean_dec(v_k_2905_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_2909_, lean_object* v_msg_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_toCold_2918_; lean_object* v_currRecDepth_2919_; lean_object* v_ref_2920_; uint16_t v_optionFlags_2921_; uint8_t v_suppressElabErrors_2922_; uint8_t v_isRecordingDeps_2923_; lean_object* v_ref_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_toCold_2918_ = lean_ctor_get(v___y_2915_, 0);
v_currRecDepth_2919_ = lean_ctor_get(v___y_2915_, 1);
v_ref_2920_ = lean_ctor_get(v___y_2915_, 2);
v_optionFlags_2921_ = lean_ctor_get_uint16(v___y_2915_, sizeof(void*)*3);
v_suppressElabErrors_2922_ = lean_ctor_get_uint8(v___y_2915_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2923_ = lean_ctor_get_uint8(v___y_2915_, sizeof(void*)*3 + 3);
v_ref_2924_ = l_Lean_replaceRef(v_ref_2909_, v_ref_2920_);
lean_inc(v_currRecDepth_2919_);
lean_inc_ref(v_toCold_2918_);
v___x_2925_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2925_, 0, v_toCold_2918_);
lean_ctor_set(v___x_2925_, 1, v_currRecDepth_2919_);
lean_ctor_set(v___x_2925_, 2, v_ref_2924_);
lean_ctor_set_uint16(v___x_2925_, sizeof(void*)*3, v_optionFlags_2921_);
lean_ctor_set_uint8(v___x_2925_, sizeof(void*)*3 + 2, v_suppressElabErrors_2922_);
lean_ctor_set_uint8(v___x_2925_, sizeof(void*)*3 + 3, v_isRecordingDeps_2923_);
v___x_2926_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___x_2925_, v___y_2916_);
lean_dec_ref_known(v___x_2925_, 3);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_2927_, lean_object* v_msg_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_2927_, v_msg_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v_ref_2927_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_2937_, lean_object* v_id_2938_, uint8_t v_minIndexable_2939_, lean_object* v_as_x27_2940_, lean_object* v_b_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
if (lean_obj_tag(v_as_x27_2940_) == 0)
{
lean_object* v___x_2947_; 
lean_dec(v_id_2938_);
v___x_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_b_2941_);
return v___x_2947_;
}
else
{
lean_object* v_head_2948_; lean_object* v_tail_2949_; lean_object* v_toCold_2950_; lean_object* v_currRecDepth_2951_; lean_object* v_ref_2952_; uint16_t v_optionFlags_2953_; uint8_t v_suppressElabErrors_2954_; uint8_t v_isRecordingDeps_2955_; uint8_t v___x_2956_; uint8_t v___x_2957_; lean_object* v___x_2958_; lean_object* v_ref_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_head_2948_ = lean_ctor_get(v_as_x27_2940_, 0);
v_tail_2949_ = lean_ctor_get(v_as_x27_2940_, 1);
v_toCold_2950_ = lean_ctor_get(v___y_2944_, 0);
v_currRecDepth_2951_ = lean_ctor_get(v___y_2944_, 1);
v_ref_2952_ = lean_ctor_get(v___y_2944_, 2);
v_optionFlags_2953_ = lean_ctor_get_uint16(v___y_2944_, sizeof(void*)*3);
v_suppressElabErrors_2954_ = lean_ctor_get_uint8(v___y_2944_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2955_ = lean_ctor_get_uint8(v___y_2944_, sizeof(void*)*3 + 3);
v___x_2956_ = 0;
v___x_2957_ = 1;
v___x_2958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_ref_2959_ = l_Lean_replaceRef(v_p_2937_, v_ref_2952_);
lean_inc(v_currRecDepth_2951_);
lean_inc_ref(v_toCold_2950_);
v___x_2960_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2960_, 0, v_toCold_2950_);
lean_ctor_set(v___x_2960_, 1, v_currRecDepth_2951_);
lean_ctor_set(v___x_2960_, 2, v_ref_2959_);
lean_ctor_set_uint16(v___x_2960_, sizeof(void*)*3, v_optionFlags_2953_);
lean_ctor_set_uint8(v___x_2960_, sizeof(void*)*3 + 2, v_suppressElabErrors_2954_);
lean_ctor_set_uint8(v___x_2960_, sizeof(void*)*3 + 3, v_isRecordingDeps_2955_);
lean_inc(v_head_2948_);
lean_inc(v_id_2938_);
v___x_2961_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2941_, v_id_2938_, v_head_2948_, v___x_2958_, v_minIndexable_2939_, v___x_2956_, v___x_2957_, v___y_2942_, v___y_2943_, v___x_2960_, v___y_2945_);
lean_dec_ref_known(v___x_2960_, 3);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2961_, 1);
v_as_x27_2940_ = v_tail_2949_;
v_b_2941_ = v_a_2962_;
goto _start;
}
else
{
lean_dec(v_id_2938_);
return v___x_2961_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_2964_, lean_object* v_id_2965_, lean_object* v_minIndexable_2966_, lean_object* v_as_x27_2967_, lean_object* v_b_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
uint8_t v_minIndexable_boxed_2974_; lean_object* v_res_2975_; 
v_minIndexable_boxed_2974_ = lean_unbox(v_minIndexable_2966_);
v_res_2975_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_2964_, v_id_2965_, v_minIndexable_boxed_2974_, v_as_x27_2967_, v_b_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v_as_x27_2967_);
lean_dec(v_p_2964_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_2976_){
_start:
{
if (lean_obj_tag(v_x_2976_) == 0)
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_box(0);
return v___x_2977_;
}
else
{
lean_object* v_head_2978_; lean_object* v_tail_2979_; lean_object* v_fst_2980_; uint8_t v___x_2981_; 
v_head_2978_ = lean_ctor_get(v_x_2976_, 0);
v_tail_2979_ = lean_ctor_get(v_x_2976_, 1);
v_fst_2980_ = lean_ctor_get(v_head_2978_, 0);
v___x_2981_ = l_Lean_isPrivateName(v_fst_2980_);
if (v___x_2981_ == 0)
{
v_x_2976_ = v_tail_2979_;
goto _start;
}
else
{
lean_object* v___x_2983_; 
lean_inc(v_head_2978_);
v___x_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2983_, 0, v_head_2978_);
return v___x_2983_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_2984_);
lean_dec(v_x_2984_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_2986_, lean_object* v_msgData_2987_, uint8_t v_severity_2988_, uint8_t v_isSilent_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; uint8_t v___y_3001_; uint8_t v___y_3002_; lean_object* v_toCold_3003_; lean_object* v___y_3004_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; uint8_t v___y_3036_; lean_object* v___y_3037_; uint8_t v___y_3038_; uint8_t v___y_3039_; lean_object* v___y_3040_; uint8_t v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; uint8_t v___y_3064_; uint8_t v___y_3065_; lean_object* v___y_3066_; uint8_t v___y_3070_; uint8_t v___y_3071_; uint8_t v___y_3072_; uint8_t v___x_3083_; uint8_t v___y_3085_; uint8_t v___y_3086_; uint8_t v___y_3087_; uint8_t v___y_3089_; uint8_t v___x_3097_; 
v___x_3083_ = 2;
v___x_3097_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2988_, v___x_3083_);
if (v___x_3097_ == 0)
{
v___y_3089_ = v___x_3097_;
goto v___jp_3088_;
}
else
{
uint8_t v___x_3098_; 
lean_inc_ref(v_msgData_2987_);
v___x_3098_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2987_);
v___y_3089_ = v___x_3098_;
goto v___jp_3088_;
}
v___jp_2995_:
{
lean_object* v_currNamespace_3005_; lean_object* v_openDecls_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v_env_3011_; lean_object* v_nextMacroScope_3012_; lean_object* v_ngen_3013_; lean_object* v_auxDeclNGen_3014_; lean_object* v_traceState_3015_; lean_object* v_cache_3016_; lean_object* v_recordedDeps_3017_; lean_object* v_messages_3018_; lean_object* v_infoState_3019_; lean_object* v_snapshotTasks_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3031_; 
v_currNamespace_3005_ = lean_ctor_get(v_toCold_3003_, 4);
v_openDecls_3006_ = lean_ctor_get(v_toCold_3003_, 5);
lean_inc(v_openDecls_3006_);
lean_inc(v_currNamespace_3005_);
v___x_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3007_, 0, v_currNamespace_3005_);
lean_ctor_set(v___x_3007_, 1, v_openDecls_3006_);
v___x_3008_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v___y_2999_);
lean_inc_ref(v___y_3000_);
lean_inc_ref(v___y_2997_);
v___x_3009_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3009_, 0, v___y_2997_);
lean_ctor_set(v___x_3009_, 1, v___y_2998_);
lean_ctor_set(v___x_3009_, 2, v___y_2996_);
lean_ctor_set(v___x_3009_, 3, v___y_3000_);
lean_ctor_set(v___x_3009_, 4, v___x_3008_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*5, v___y_3002_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*5 + 1, v___y_3001_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*5 + 2, v_isSilent_2989_);
v___x_3010_ = lean_st_ref_take(v___y_3004_);
v_env_3011_ = lean_ctor_get(v___x_3010_, 0);
v_nextMacroScope_3012_ = lean_ctor_get(v___x_3010_, 1);
v_ngen_3013_ = lean_ctor_get(v___x_3010_, 2);
v_auxDeclNGen_3014_ = lean_ctor_get(v___x_3010_, 3);
v_traceState_3015_ = lean_ctor_get(v___x_3010_, 4);
v_cache_3016_ = lean_ctor_get(v___x_3010_, 5);
v_recordedDeps_3017_ = lean_ctor_get(v___x_3010_, 6);
v_messages_3018_ = lean_ctor_get(v___x_3010_, 7);
v_infoState_3019_ = lean_ctor_get(v___x_3010_, 8);
v_snapshotTasks_3020_ = lean_ctor_get(v___x_3010_, 9);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3022_ = v___x_3010_;
v_isShared_3023_ = v_isSharedCheck_3031_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_snapshotTasks_3020_);
lean_inc(v_infoState_3019_);
lean_inc(v_messages_3018_);
lean_inc(v_recordedDeps_3017_);
lean_inc(v_cache_3016_);
lean_inc(v_traceState_3015_);
lean_inc(v_auxDeclNGen_3014_);
lean_inc(v_ngen_3013_);
lean_inc(v_nextMacroScope_3012_);
lean_inc(v_env_3011_);
lean_dec(v___x_3010_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3031_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3027_; 
v___x_3024_ = lean_box(0);
v___x_3025_ = l_Lean_MessageLog_add(v___x_3009_, v_messages_3018_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 7, v___x_3025_);
v___x_3027_ = v___x_3022_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_env_3011_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v_nextMacroScope_3012_);
lean_ctor_set(v_reuseFailAlloc_3030_, 2, v_ngen_3013_);
lean_ctor_set(v_reuseFailAlloc_3030_, 3, v_auxDeclNGen_3014_);
lean_ctor_set(v_reuseFailAlloc_3030_, 4, v_traceState_3015_);
lean_ctor_set(v_reuseFailAlloc_3030_, 5, v_cache_3016_);
lean_ctor_set(v_reuseFailAlloc_3030_, 6, v_recordedDeps_3017_);
lean_ctor_set(v_reuseFailAlloc_3030_, 7, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3030_, 8, v_infoState_3019_);
lean_ctor_set(v_reuseFailAlloc_3030_, 9, v_snapshotTasks_3020_);
v___x_3027_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_st_ref_put(v___y_3004_, v___x_3027_);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3024_);
return v___x_3029_;
}
}
}
v___jp_3032_:
{
lean_object* v_fileName_3041_; lean_object* v_fileMap_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3058_; 
v_fileName_3041_ = lean_ctor_get(v___y_3037_, 0);
v_fileMap_3042_ = lean_ctor_get(v___y_3037_, 1);
v___x_3043_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2987_);
v___x_3044_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_3043_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3047_ = v___x_3044_;
v_isShared_3048_ = v_isSharedCheck_3058_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3058_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
lean_inc_ref_n(v_fileMap_3042_, 2);
v___x_3049_ = l_Lean_FileMap_toPosition(v_fileMap_3042_, v___y_3035_);
lean_dec(v___y_3035_);
v___x_3050_ = l_Lean_FileMap_toPosition(v_fileMap_3042_, v___y_3040_);
lean_dec(v___y_3040_);
v___x_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
v___x_3052_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_3036_ == 0)
{
lean_del_object(v___x_3047_);
lean_dec_ref(v___y_3034_);
v___y_2996_ = v___x_3051_;
v___y_2997_ = v_fileName_3041_;
v___y_2998_ = v___x_3049_;
v___y_2999_ = v_a_3045_;
v___y_3000_ = v___x_3052_;
v___y_3001_ = v___y_3039_;
v___y_3002_ = v___y_3038_;
v_toCold_3003_ = v___y_3033_;
v___y_3004_ = v___y_2993_;
goto v___jp_2995_;
}
else
{
uint8_t v___x_3053_; 
lean_inc(v_a_3045_);
v___x_3053_ = l_Lean_MessageData_hasTag(v___y_3034_, v_a_3045_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
lean_dec_ref_known(v___x_3051_, 1);
lean_dec_ref(v___x_3049_);
lean_dec(v_a_3045_);
v___x_3054_ = lean_box(0);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3054_);
v___x_3056_ = v___x_3047_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
else
{
lean_del_object(v___x_3047_);
v___y_2996_ = v___x_3051_;
v___y_2997_ = v_fileName_3041_;
v___y_2998_ = v___x_3049_;
v___y_2999_ = v_a_3045_;
v___y_3000_ = v___x_3052_;
v___y_3001_ = v___y_3039_;
v___y_3002_ = v___y_3038_;
v_toCold_3003_ = v___y_3033_;
v___y_3004_ = v___y_2993_;
goto v___jp_2995_;
}
}
}
}
v___jp_3059_:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Lean_Syntax_getTailPos_x3f(v___y_3063_, v___y_3065_);
lean_dec(v___y_3063_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_inc(v___y_3066_);
v___y_3033_ = v___y_3061_;
v___y_3034_ = v___y_3062_;
v___y_3035_ = v___y_3066_;
v___y_3036_ = v___y_3060_;
v___y_3037_ = v___y_3061_;
v___y_3038_ = v___y_3065_;
v___y_3039_ = v___y_3064_;
v___y_3040_ = v___y_3066_;
goto v___jp_3032_;
}
else
{
lean_object* v_val_3068_; 
v_val_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_val_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v___y_3033_ = v___y_3061_;
v___y_3034_ = v___y_3062_;
v___y_3035_ = v___y_3066_;
v___y_3036_ = v___y_3060_;
v___y_3037_ = v___y_3061_;
v___y_3038_ = v___y_3065_;
v___y_3039_ = v___y_3064_;
v___y_3040_ = v_val_3068_;
goto v___jp_3032_;
}
}
v___jp_3069_:
{
lean_object* v_toCold_3073_; lean_object* v_ref_3074_; uint8_t v_suppressElabErrors_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___f_3078_; lean_object* v_ref_3079_; lean_object* v___x_3080_; 
v_toCold_3073_ = lean_ctor_get(v___y_2992_, 0);
v_ref_3074_ = lean_ctor_get(v___y_2992_, 2);
v_suppressElabErrors_3075_ = lean_ctor_get_uint8(v___y_2992_, sizeof(void*)*3 + 2);
v___x_3076_ = lean_box(v_suppressElabErrors_3075_);
v___x_3077_ = lean_box(v___y_3070_);
v___f_3078_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3078_, 0, v___x_3076_);
lean_closure_set(v___f_3078_, 1, v___x_3077_);
v_ref_3079_ = l_Lean_replaceRef(v_ref_2986_, v_ref_3074_);
v___x_3080_ = l_Lean_Syntax_getPos_x3f(v_ref_3079_, v___y_3071_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v___x_3081_; 
v___x_3081_ = lean_unsigned_to_nat(0u);
v___y_3060_ = v_suppressElabErrors_3075_;
v___y_3061_ = v_toCold_3073_;
v___y_3062_ = v___f_3078_;
v___y_3063_ = v_ref_3079_;
v___y_3064_ = v___y_3072_;
v___y_3065_ = v___y_3071_;
v___y_3066_ = v___x_3081_;
goto v___jp_3059_;
}
else
{
lean_object* v_val_3082_; 
v_val_3082_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_val_3082_);
lean_dec_ref_known(v___x_3080_, 1);
v___y_3060_ = v_suppressElabErrors_3075_;
v___y_3061_ = v_toCold_3073_;
v___y_3062_ = v___f_3078_;
v___y_3063_ = v_ref_3079_;
v___y_3064_ = v___y_3072_;
v___y_3065_ = v___y_3071_;
v___y_3066_ = v_val_3082_;
goto v___jp_3059_;
}
}
v___jp_3084_:
{
if (v___y_3087_ == 0)
{
v___y_3070_ = v___y_3085_;
v___y_3071_ = v___y_3086_;
v___y_3072_ = v_severity_2988_;
goto v___jp_3069_;
}
else
{
v___y_3070_ = v___y_3085_;
v___y_3071_ = v___y_3086_;
v___y_3072_ = v___x_3083_;
goto v___jp_3069_;
}
}
v___jp_3088_:
{
if (v___y_3089_ == 0)
{
uint8_t v___x_3090_; uint8_t v___x_3091_; 
v___x_3090_ = 1;
v___x_3091_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2988_, v___x_3090_);
if (v___x_3091_ == 0)
{
v___y_3085_ = v___y_3089_;
v___y_3086_ = v___y_3089_;
v___y_3087_ = v___x_3091_;
goto v___jp_3084_;
}
else
{
lean_object* v___x_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; 
v___x_3092_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2992_);
v___x_3093_ = l_Lean_warningAsError;
v___x_3094_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3092_, v___x_3093_);
lean_dec_ref(v___x_3092_);
v___y_3085_ = v___y_3089_;
v___y_3086_ = v___y_3089_;
v___y_3087_ = v___x_3094_;
goto v___jp_3084_;
}
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
lean_dec_ref(v_msgData_2987_);
v___x_3095_ = lean_box(0);
v___x_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
return v___x_3096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_3099_, lean_object* v_msgData_3100_, lean_object* v_severity_3101_, lean_object* v_isSilent_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
uint8_t v_severity_boxed_3108_; uint8_t v_isSilent_boxed_3109_; lean_object* v_res_3110_; 
v_severity_boxed_3108_ = lean_unbox(v_severity_3101_);
v_isSilent_boxed_3109_ = lean_unbox(v_isSilent_3102_);
v_res_3110_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3099_, v_msgData_3100_, v_severity_boxed_3108_, v_isSilent_boxed_3109_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v_ref_3099_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_3111_, uint8_t v_severity_3112_, uint8_t v_isSilent_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v_ref_3121_; lean_object* v___x_3122_; 
v_ref_3121_ = lean_ctor_get(v___y_3118_, 2);
v___x_3122_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3121_, v_msgData_3111_, v_severity_3112_, v_isSilent_3113_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_3123_, lean_object* v_severity_3124_, lean_object* v_isSilent_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
uint8_t v_severity_boxed_3133_; uint8_t v_isSilent_boxed_3134_; lean_object* v_res_3135_; 
v_severity_boxed_3133_ = lean_unbox(v_severity_3124_);
v_isSilent_boxed_3134_ = lean_unbox(v_isSilent_3125_);
v_res_3135_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3123_, v_severity_boxed_3133_, v_isSilent_boxed_3134_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
uint8_t v___x_3144_; uint8_t v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = 1;
v___x_3145_ = 0;
v___x_3146_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3136_, v___x_3144_, v___x_3145_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3159_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3157_);
v___x_3160_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3159_, v_opt_3156_);
lean_dec_ref(v___x_3159_);
v___x_3161_ = lean_box(v___x_3160_);
v___x_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3163_, v___y_3164_);
lean_dec_ref(v___y_3164_);
lean_dec_ref(v_opt_3163_);
return v_res_3166_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3169_ = l_Lean_stringToMessageData(v___x_3168_);
return v___x_3169_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3172_ = l_Lean_stringToMessageData(v___x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; lean_object* v_env_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3204_; 
v___x_3181_ = lean_st_ref_get(v___y_3179_);
v_env_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc_ref(v_env_3182_);
lean_dec(v___x_3181_);
v___x_3183_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3184_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3183_, v___y_3178_);
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3187_ = v___x_3184_;
v_isShared_3188_ = v_isSharedCheck_3204_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3204_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
uint8_t v_isExporting_3194_; 
v_isExporting_3194_ = lean_ctor_get_uint8(v_env_3182_, sizeof(void*)*13);
lean_dec_ref(v_env_3182_);
if (v_isExporting_3194_ == 0)
{
lean_dec(v_a_3185_);
lean_dec(v_id_3173_);
goto v___jp_3189_;
}
else
{
uint8_t v___x_3195_; 
v___x_3195_ = l_Lean_isPrivateName(v_id_3173_);
if (v___x_3195_ == 0)
{
lean_dec(v_a_3185_);
lean_dec(v_id_3173_);
goto v___jp_3189_;
}
else
{
uint8_t v___x_3196_; 
v___x_3196_ = lean_unbox(v_a_3185_);
lean_dec(v_a_3185_);
if (v___x_3196_ == 0)
{
lean_dec(v_id_3173_);
goto v___jp_3189_;
}
else
{
lean_object* v___x_3197_; uint8_t v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
lean_del_object(v___x_3187_);
v___x_3197_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3198_ = 0;
v___x_3199_ = l_Lean_MessageData_ofConstName(v_id_3173_, v___x_3198_);
v___x_3200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3197_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3200_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
v___x_3203_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3202_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3203_;
}
}
}
v___jp_3189_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3190_ = lean_box(0);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3190_);
v___x_3192_ = v___x_3187_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3214_, uint8_t v_enableLog_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v___x_3223_; lean_object* v_toCold_3224_; lean_object* v_env_3225_; lean_object* v_currNamespace_3226_; lean_object* v_openDecls_3227_; lean_object* v___x_3228_; lean_object* v_res_3229_; lean_object* v___x_3230_; 
v___x_3223_ = lean_st_ref_get(v___y_3221_);
v_toCold_3224_ = lean_ctor_get(v___y_3220_, 0);
v_env_3225_ = lean_ctor_get(v___x_3223_, 0);
lean_inc_ref(v_env_3225_);
lean_dec(v___x_3223_);
v_currNamespace_3226_ = lean_ctor_get(v_toCold_3224_, 4);
v_openDecls_3227_ = lean_ctor_get(v_toCold_3224_, 5);
v___x_3228_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3220_);
lean_inc(v_openDecls_3227_);
lean_inc(v_currNamespace_3226_);
v_res_3229_ = l_Lean_ResolveName_resolveGlobalName(v_env_3225_, v___x_3228_, v_currNamespace_3226_, v_openDecls_3227_, v_id_3214_);
lean_dec_ref(v___x_3228_);
v___x_3230_ = lean_st_ref_get(v___y_3221_);
if (v_enableLog_3215_ == 0)
{
lean_object* v___x_3231_; 
lean_dec(v___x_3230_);
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_res_3229_);
return v___x_3231_;
}
else
{
lean_object* v_env_3232_; uint8_t v_isExporting_3233_; 
v_env_3232_ = lean_ctor_get(v___x_3230_, 0);
lean_inc_ref(v_env_3232_);
lean_dec(v___x_3230_);
v_isExporting_3233_ = lean_ctor_get_uint8(v_env_3232_, sizeof(void*)*13);
lean_dec_ref(v_env_3232_);
if (v_isExporting_3233_ == 0)
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3234_, 0, v_res_3229_);
return v___x_3234_;
}
else
{
lean_object* v___x_3235_; 
v___x_3235_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3229_);
if (lean_obj_tag(v___x_3235_) == 1)
{
lean_object* v_val_3236_; lean_object* v_fst_3237_; lean_object* v___x_3238_; 
v_val_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_val_3236_);
lean_dec_ref_known(v___x_3235_, 1);
v_fst_3237_ = lean_ctor_get(v_val_3236_, 0);
lean_inc(v_fst_3237_);
lean_dec(v_val_3236_);
v___x_3238_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3237_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; 
v_unused_3246_ = lean_ctor_get(v___x_3238_, 0);
lean_dec(v_unused_3246_);
v___x_3240_ = v___x_3238_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_dec(v___x_3238_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v_res_3229_);
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_res_3229_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec(v_res_3229_);
v_a_3247_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3238_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3238_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
else
{
lean_object* v___x_3255_; 
lean_dec(v___x_3235_);
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v_res_3229_);
return v___x_3255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3256_, lean_object* v_enableLog_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_){
_start:
{
uint8_t v_enableLog_boxed_3265_; lean_object* v_res_3266_; 
v_enableLog_boxed_3265_ = lean_unbox(v_enableLog_3257_);
v_res_3266_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3256_, v_enableLog_boxed_3265_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3267_, lean_object* v_a_3268_){
_start:
{
if (lean_obj_tag(v_a_3267_) == 0)
{
lean_object* v___x_3269_; 
v___x_3269_ = l_List_reverse___redArg(v_a_3268_);
return v___x_3269_;
}
else
{
lean_object* v_head_3270_; lean_object* v_tail_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3282_; 
v_head_3270_ = lean_ctor_get(v_a_3267_, 0);
v_tail_3271_ = lean_ctor_get(v_a_3267_, 1);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_a_3267_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3273_ = v_a_3267_;
v_isShared_3274_ = v_isSharedCheck_3282_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_tail_3271_);
lean_inc(v_head_3270_);
lean_dec(v_a_3267_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3282_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v_snd_3275_; uint8_t v___x_3276_; 
v_snd_3275_ = lean_ctor_get(v_head_3270_, 1);
v___x_3276_ = l_List_isEmpty___redArg(v_snd_3275_);
if (v___x_3276_ == 0)
{
lean_del_object(v___x_3273_);
lean_dec(v_head_3270_);
v_a_3267_ = v_tail_3271_;
goto _start;
}
else
{
lean_object* v___x_3279_; 
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 1, v_a_3268_);
v___x_3279_ = v___x_3273_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_head_3270_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_a_3268_);
v___x_3279_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
v_a_3267_ = v_tail_3271_;
v_a_3268_ = v___x_3279_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3283_, lean_object* v_findLocalDecl_x3f_3284_, lean_object* v_n_3285_, lean_object* v_projs_3286_, uint8_t v_globalDeclFound_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___y_3296_; lean_object* v___y_3297_; uint8_t v_globalDeclFoundNext_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v_imported_3307_; lean_object* v_ctx_3308_; lean_object* v_scopes_3309_; lean_object* v_givenNameView_3310_; uint8_t v___y_3312_; 
v_imported_3307_ = lean_ctor_get(v_view_3283_, 1);
v_ctx_3308_ = lean_ctor_get(v_view_3283_, 2);
v_scopes_3309_ = lean_ctor_get(v_view_3283_, 3);
lean_inc(v_scopes_3309_);
lean_inc(v_ctx_3308_);
lean_inc(v_imported_3307_);
lean_inc(v_n_3285_);
v_givenNameView_3310_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3310_, 0, v_n_3285_);
lean_ctor_set(v_givenNameView_3310_, 1, v_imported_3307_);
lean_ctor_set(v_givenNameView_3310_, 2, v_ctx_3308_);
lean_ctor_set(v_givenNameView_3310_, 3, v_scopes_3309_);
if (v_globalDeclFound_3287_ == 0)
{
v___y_3312_ = v_globalDeclFound_3287_;
goto v___jp_3311_;
}
else
{
uint8_t v___x_3347_; 
v___x_3347_ = l_List_isEmpty___redArg(v_projs_3286_);
if (v___x_3347_ == 0)
{
v___y_3312_ = v_globalDeclFound_3287_;
goto v___jp_3311_;
}
else
{
uint8_t v___x_3348_; 
v___x_3348_ = 0;
v___y_3312_ = v___x_3348_;
goto v___jp_3311_;
}
}
v___jp_3295_:
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___y_3296_);
lean_ctor_set(v___x_3305_, 1, v_projs_3286_);
v_n_3285_ = v___y_3297_;
v_projs_3286_ = v___x_3305_;
v_globalDeclFound_3287_ = v_globalDeclFoundNext_3298_;
v___y_3288_ = v___y_3299_;
v___y_3289_ = v___y_3300_;
v___y_3290_ = v___y_3301_;
v___y_3291_ = v___y_3302_;
v___y_3292_ = v___y_3303_;
v___y_3293_ = v___y_3304_;
goto _start;
}
v___jp_3311_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = lean_box(v___y_3312_);
lean_inc_ref(v_findLocalDecl_x3f_3284_);
lean_inc_ref(v_givenNameView_3310_);
v___x_3314_ = lean_apply_2(v_findLocalDecl_x3f_3284_, v_givenNameView_3310_, v___x_3313_);
if (lean_obj_tag(v___x_3314_) == 0)
{
if (lean_obj_tag(v_n_3285_) == 1)
{
if (v_globalDeclFound_3287_ == 0)
{
lean_object* v_pre_3315_; lean_object* v_str_3316_; uint8_t v_globalDeclFoundNext_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_pre_3315_ = lean_ctor_get(v_n_3285_, 0);
lean_inc(v_pre_3315_);
v_str_3316_ = lean_ctor_get(v_n_3285_, 1);
lean_inc_ref(v_str_3316_);
lean_dec_ref_known(v_n_3285_, 2);
v_globalDeclFoundNext_3317_ = 1;
v___x_3318_ = l_Lean_MacroScopesView_review(v_givenNameView_3310_);
v___x_3319_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3318_, v_globalDeclFound_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3321_; lean_object* v_r_3322_; uint8_t v___x_3323_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3319_, 1);
v___x_3321_ = lean_box(0);
v_r_3322_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3320_, v___x_3321_);
v___x_3323_ = l_List_isEmpty___redArg(v_r_3322_);
lean_dec(v_r_3322_);
if (v___x_3323_ == 0)
{
v___y_3296_ = v_str_3316_;
v___y_3297_ = v_pre_3315_;
v_globalDeclFoundNext_3298_ = v_globalDeclFoundNext_3317_;
v___y_3299_ = v___y_3288_;
v___y_3300_ = v___y_3289_;
v___y_3301_ = v___y_3290_;
v___y_3302_ = v___y_3291_;
v___y_3303_ = v___y_3292_;
v___y_3304_ = v___y_3293_;
goto v___jp_3295_;
}
else
{
v___y_3296_ = v_str_3316_;
v___y_3297_ = v_pre_3315_;
v_globalDeclFoundNext_3298_ = v_globalDeclFound_3287_;
v___y_3299_ = v___y_3288_;
v___y_3300_ = v___y_3289_;
v___y_3301_ = v___y_3290_;
v___y_3302_ = v___y_3291_;
v___y_3303_ = v___y_3292_;
v___y_3304_ = v___y_3293_;
goto v___jp_3295_;
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_dec_ref(v_str_3316_);
lean_dec(v_pre_3315_);
lean_dec(v_projs_3286_);
lean_dec_ref(v_findLocalDecl_x3f_3284_);
v_a_3324_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3319_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3319_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
lean_object* v_pre_3332_; lean_object* v_str_3333_; 
lean_dec_ref_known(v_givenNameView_3310_, 4);
v_pre_3332_ = lean_ctor_get(v_n_3285_, 0);
lean_inc(v_pre_3332_);
v_str_3333_ = lean_ctor_get(v_n_3285_, 1);
lean_inc_ref(v_str_3333_);
lean_dec_ref_known(v_n_3285_, 2);
v___y_3296_ = v_str_3333_;
v___y_3297_ = v_pre_3332_;
v_globalDeclFoundNext_3298_ = v_globalDeclFound_3287_;
v___y_3299_ = v___y_3288_;
v___y_3300_ = v___y_3289_;
v___y_3301_ = v___y_3290_;
v___y_3302_ = v___y_3291_;
v___y_3303_ = v___y_3292_;
v___y_3304_ = v___y_3293_;
goto v___jp_3295_;
}
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec_ref_known(v_givenNameView_3310_, 4);
lean_dec(v_projs_3286_);
lean_dec(v_n_3285_);
lean_dec_ref(v_findLocalDecl_x3f_3284_);
v___x_3334_ = lean_box(0);
v___x_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
return v___x_3335_;
}
}
else
{
lean_object* v_val_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3346_; 
lean_dec_ref_known(v_givenNameView_3310_, 4);
lean_dec(v_n_3285_);
lean_dec_ref(v_findLocalDecl_x3f_3284_);
v_val_3336_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3338_ = v___x_3314_;
v_isShared_3339_ = v_isSharedCheck_3346_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_val_3336_);
lean_dec(v___x_3314_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3346_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3343_; 
v___x_3340_ = l_Lean_LocalDecl_toExpr(v_val_3336_);
v___x_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
lean_ctor_set(v___x_3341_, 1, v_projs_3286_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v___x_3341_);
v___x_3343_ = v___x_3338_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3344_; 
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
return v___x_3344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3349_, lean_object* v_findLocalDecl_x3f_3350_, lean_object* v_n_3351_, lean_object* v_projs_3352_, lean_object* v_globalDeclFound_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
uint8_t v_globalDeclFound_boxed_3361_; lean_object* v_res_3362_; 
v_globalDeclFound_boxed_3361_ = lean_unbox(v_globalDeclFound_3353_);
v_res_3362_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3349_, v_findLocalDecl_x3f_3350_, v_n_3351_, v_projs_3352_, v_globalDeclFound_boxed_3361_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec_ref(v_view_3349_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3363_, lean_object* v_givenName_3364_, lean_object* v_as_3365_, lean_object* v_i_3366_){
_start:
{
lean_object* v_zero_3367_; uint8_t v_isZero_3368_; 
v_zero_3367_ = lean_unsigned_to_nat(0u);
v_isZero_3368_ = lean_nat_dec_eq(v_i_3366_, v_zero_3367_);
if (v_isZero_3368_ == 1)
{
lean_object* v___x_3369_; 
lean_dec(v_i_3366_);
v___x_3369_ = lean_box(0);
return v___x_3369_;
}
else
{
lean_object* v_one_3370_; lean_object* v_n_3371_; lean_object* v___y_3373_; lean_object* v___x_3375_; 
v_one_3370_ = lean_unsigned_to_nat(1u);
v_n_3371_ = lean_nat_sub(v_i_3366_, v_one_3370_);
lean_dec(v_i_3366_);
v___x_3375_ = lean_array_fget_borrowed(v_as_3365_, v_n_3371_);
if (lean_obj_tag(v___x_3375_) == 0)
{
v___y_3373_ = v___x_3375_;
goto v___jp_3372_;
}
else
{
lean_object* v_val_3376_; uint8_t v___x_3377_; 
v_val_3376_ = lean_ctor_get(v___x_3375_, 0);
v___x_3377_ = l_Lean_LocalDecl_isAuxDecl(v_val_3376_);
if (v___x_3377_ == 0)
{
v___y_3373_ = v_localDecl_x3f_3363_;
goto v___jp_3372_;
}
else
{
lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3378_ = l_Lean_LocalDecl_userName(v_val_3376_);
v___x_3379_ = lean_name_eq(v___x_3378_, v_givenName_3364_);
lean_dec(v___x_3378_);
if (v___x_3379_ == 0)
{
v_i_3366_ = v_n_3371_;
goto _start;
}
else
{
v___y_3373_ = v___x_3375_;
goto v___jp_3372_;
}
}
}
v___jp_3372_:
{
if (lean_obj_tag(v___y_3373_) == 0)
{
v_i_3366_ = v_n_3371_;
goto _start;
}
else
{
lean_dec(v_n_3371_);
lean_inc_ref(v___y_3373_);
return v___y_3373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3381_, lean_object* v_givenName_3382_, lean_object* v_as_3383_, lean_object* v_i_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3381_, v_givenName_3382_, v_as_3383_, v_i_3384_);
lean_dec_ref(v_as_3383_);
lean_dec(v_givenName_3382_);
lean_dec(v_localDecl_x3f_3381_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3386_, lean_object* v_givenName_3387_, lean_object* v_as_3388_, lean_object* v_i_3389_){
_start:
{
lean_object* v_zero_3390_; uint8_t v_isZero_3391_; 
v_zero_3390_ = lean_unsigned_to_nat(0u);
v_isZero_3391_ = lean_nat_dec_eq(v_i_3389_, v_zero_3390_);
if (v_isZero_3391_ == 1)
{
lean_object* v___x_3392_; 
lean_dec(v_i_3389_);
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
v___x_3396_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3386_, v_givenName_3387_, v___x_3395_);
if (lean_obj_tag(v___x_3396_) == 0)
{
v_i_3389_ = v_n_3394_;
goto _start;
}
else
{
lean_dec(v_n_3394_);
return v___x_3396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3398_, lean_object* v_givenName_3399_, lean_object* v_x_3400_){
_start:
{
if (lean_obj_tag(v_x_3400_) == 0)
{
lean_object* v_cs_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v_cs_3401_ = lean_ctor_get(v_x_3400_, 0);
v___x_3402_ = lean_array_get_size(v_cs_3401_);
v___x_3403_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3398_, v_givenName_3399_, v_cs_3401_, v___x_3402_);
return v___x_3403_;
}
else
{
lean_object* v_vs_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v_vs_3404_ = lean_ctor_get(v_x_3400_, 0);
v___x_3405_ = lean_array_get_size(v_vs_3404_);
v___x_3406_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3398_, v_givenName_3399_, v_vs_3404_, v___x_3405_);
return v___x_3406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3407_, lean_object* v_givenName_3408_, lean_object* v_x_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3407_, v_givenName_3408_, v_x_3409_);
lean_dec_ref(v_x_3409_);
lean_dec(v_givenName_3408_);
lean_dec(v_localDecl_x3f_3407_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3411_, lean_object* v_givenName_3412_, lean_object* v_as_3413_, lean_object* v_i_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3411_, v_givenName_3412_, v_as_3413_, v_i_3414_);
lean_dec_ref(v_as_3413_);
lean_dec(v_givenName_3412_);
lean_dec(v_localDecl_x3f_3411_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3416_, lean_object* v_givenName_3417_, lean_object* v_t_3418_){
_start:
{
lean_object* v_root_3419_; lean_object* v_tail_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_root_3419_ = lean_ctor_get(v_t_3418_, 0);
v_tail_3420_ = lean_ctor_get(v_t_3418_, 1);
v___x_3421_ = lean_array_get_size(v_tail_3420_);
v___x_3422_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3416_, v_givenName_3417_, v_tail_3420_, v___x_3421_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3416_, v_givenName_3417_, v_root_3419_);
return v___x_3423_;
}
else
{
return v___x_3422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3424_, lean_object* v_givenName_3425_, lean_object* v_t_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3424_, v_givenName_3425_, v_t_3426_);
lean_dec_ref(v_t_3426_);
lean_dec(v_givenName_3425_);
lean_dec(v_localDecl_x3f_3424_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3428_, lean_object* v_k_3429_){
_start:
{
if (lean_obj_tag(v_t_3428_) == 0)
{
lean_object* v_k_3430_; lean_object* v_v_3431_; lean_object* v_l_3432_; lean_object* v_r_3433_; uint8_t v___x_3434_; 
v_k_3430_ = lean_ctor_get(v_t_3428_, 1);
v_v_3431_ = lean_ctor_get(v_t_3428_, 2);
v_l_3432_ = lean_ctor_get(v_t_3428_, 3);
v_r_3433_ = lean_ctor_get(v_t_3428_, 4);
v___x_3434_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3429_, v_k_3430_);
switch(v___x_3434_)
{
case 0:
{
v_t_3428_ = v_l_3432_;
goto _start;
}
case 1:
{
lean_object* v___x_3436_; 
lean_inc(v_v_3431_);
v___x_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3436_, 0, v_v_3431_);
return v___x_3436_;
}
default: 
{
v_t_3428_ = v_r_3433_;
goto _start;
}
}
}
else
{
lean_object* v___x_3438_; 
v___x_3438_ = lean_box(0);
return v___x_3438_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3439_, lean_object* v_k_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3439_, v_k_3440_);
lean_dec(v_k_3440_);
lean_dec(v_t_3439_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3442_, lean_object* v_givenName_3443_){
_start:
{
lean_object* v___x_3444_; uint8_t v___x_3445_; 
v___x_3444_ = l_Lean_LocalDecl_userName(v_localDecl_3442_);
v___x_3445_ = lean_name_eq(v___x_3444_, v_givenName_3443_);
lean_dec(v___x_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; 
lean_dec_ref(v_localDecl_3442_);
v___x_3446_ = lean_box(0);
return v___x_3446_;
}
else
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3447_, 0, v_localDecl_3442_);
return v___x_3447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3448_, lean_object* v_givenName_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3448_, v_givenName_3449_);
lean_dec(v_givenName_3449_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3451_, uint8_t v_skipAuxDecl_3452_, lean_object* v_auxDeclToFullName_3453_, lean_object* v___x_3454_, lean_object* v_givenNameView_3455_, lean_object* v_as_3456_, lean_object* v_i_3457_){
_start:
{
lean_object* v_zero_3458_; uint8_t v_isZero_3459_; 
v_zero_3458_ = lean_unsigned_to_nat(0u);
v_isZero_3459_ = lean_nat_dec_eq(v_i_3457_, v_zero_3458_);
if (v_isZero_3459_ == 1)
{
lean_object* v___x_3460_; 
lean_dec(v_i_3457_);
lean_dec_ref(v_givenNameView_3455_);
lean_dec(v___x_3454_);
v___x_3460_ = lean_box(0);
return v___x_3460_;
}
else
{
lean_object* v_one_3461_; lean_object* v_n_3462_; lean_object* v___y_3464_; lean_object* v___x_3466_; 
v_one_3461_ = lean_unsigned_to_nat(1u);
v_n_3462_ = lean_nat_sub(v_i_3457_, v_one_3461_);
lean_dec(v_i_3457_);
v___x_3466_ = lean_array_fget_borrowed(v_as_3456_, v_n_3462_);
if (lean_obj_tag(v___x_3466_) == 0)
{
v___y_3464_ = v___x_3466_;
goto v___jp_3463_;
}
else
{
lean_object* v_val_3467_; uint8_t v___x_3468_; 
v_val_3467_ = lean_ctor_get(v___x_3466_, 0);
v___x_3468_ = l_Lean_LocalDecl_isAuxDecl(v_val_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; 
lean_inc(v_val_3467_);
v___x_3469_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3467_, v_givenName_3451_);
v___y_3464_ = v___x_3469_;
goto v___jp_3463_;
}
else
{
if (v_skipAuxDecl_3452_ == 0)
{
if (v___x_3468_ == 0)
{
v_i_3457_ = v_n_3462_;
goto _start;
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = l_Lean_LocalDecl_fvarId(v_val_3467_);
v___x_3472_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3453_, v___x_3471_);
lean_dec(v___x_3471_);
if (lean_obj_tag(v___x_3472_) == 1)
{
lean_object* v_val_3473_; lean_object* v_fullDeclView_3474_; lean_object* v___y_3476_; lean_object* v_name_3497_; lean_object* v___x_3498_; 
v_val_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_val_3473_);
lean_dec_ref_known(v___x_3472_, 1);
v_fullDeclView_3474_ = l_Lean_extractMacroScopes(v_val_3473_);
v_name_3497_ = lean_ctor_get(v_fullDeclView_3474_, 0);
lean_inc(v_name_3497_);
v___x_3498_ = l_Lean_privateToUserName_x3f(v_name_3497_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_inc(v_name_3497_);
v___y_3476_ = v_name_3497_;
goto v___jp_3475_;
}
else
{
lean_object* v_val_3499_; 
v_val_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_val_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v___y_3476_ = v_val_3499_;
goto v___jp_3475_;
}
v___jp_3475_:
{
lean_object* v_imported_3477_; lean_object* v_ctx_3478_; lean_object* v_scopes_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3495_; 
v_imported_3477_ = lean_ctor_get(v_fullDeclView_3474_, 1);
v_ctx_3478_ = lean_ctor_get(v_fullDeclView_3474_, 2);
v_scopes_3479_ = lean_ctor_get(v_fullDeclView_3474_, 3);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_fullDeclView_3474_);
if (v_isSharedCheck_3495_ == 0)
{
lean_object* v_unused_3496_; 
v_unused_3496_ = lean_ctor_get(v_fullDeclView_3474_, 0);
lean_dec(v_unused_3496_);
v___x_3481_ = v_fullDeclView_3474_;
v_isShared_3482_ = v_isSharedCheck_3495_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_scopes_3479_);
lean_inc(v_ctx_3478_);
lean_inc(v_imported_3477_);
lean_dec(v_fullDeclView_3474_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3495_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v_fullDeclView_3484_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v___y_3476_);
v_fullDeclView_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___y_3476_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_imported_3477_);
lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_ctx_3478_);
lean_ctor_set(v_reuseFailAlloc_3494_, 3, v_scopes_3479_);
v_fullDeclView_3484_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_object* v_fullDeclName_3485_; uint8_t v___x_3486_; 
lean_inc_ref(v_fullDeclView_3484_);
v_fullDeclName_3485_ = l_Lean_MacroScopesView_review(v_fullDeclView_3484_);
v___x_3486_ = l_Lean_Name_isPrefixOf(v___x_3454_, v_fullDeclName_3485_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; 
lean_dec_ref(v_fullDeclView_3484_);
lean_inc(v___x_3454_);
lean_inc_ref(v_givenNameView_3455_);
lean_inc(v_val_3467_);
v___x_3487_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3467_, v_givenNameView_3455_, v_fullDeclName_3485_, v___x_3454_);
lean_dec(v_fullDeclName_3485_);
v___y_3464_ = v___x_3487_;
goto v___jp_3463_;
}
else
{
lean_object* v___x_3488_; lean_object* v_localDeclNameView_3489_; uint8_t v___x_3490_; 
lean_dec(v_fullDeclName_3485_);
v___x_3488_ = l_Lean_LocalDecl_userName(v_val_3467_);
v_localDeclNameView_3489_ = l_Lean_extractMacroScopes(v___x_3488_);
v___x_3490_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3489_, v_givenNameView_3455_);
lean_dec_ref(v_localDeclNameView_3489_);
if (v___x_3490_ == 0)
{
lean_dec_ref(v_fullDeclView_3484_);
v_i_3457_ = v_n_3462_;
goto _start;
}
else
{
uint8_t v___x_3492_; 
v___x_3492_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3455_, v_fullDeclView_3484_);
lean_dec_ref(v_fullDeclView_3484_);
if (v___x_3492_ == 0)
{
v_i_3457_ = v_n_3462_;
goto _start;
}
else
{
lean_inc_ref(v___x_3466_);
v___y_3464_ = v___x_3466_;
goto v___jp_3463_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3500_; 
lean_dec(v___x_3472_);
lean_inc(v_val_3467_);
v___x_3500_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3467_, v_givenName_3451_);
v___y_3464_ = v___x_3500_;
goto v___jp_3463_;
}
}
}
else
{
v_i_3457_ = v_n_3462_;
goto _start;
}
}
}
v___jp_3463_:
{
if (lean_obj_tag(v___y_3464_) == 0)
{
v_i_3457_ = v_n_3462_;
goto _start;
}
else
{
lean_dec(v_n_3462_);
lean_dec_ref(v_givenNameView_3455_);
lean_dec(v___x_3454_);
return v___y_3464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3502_, lean_object* v_skipAuxDecl_3503_, lean_object* v_auxDeclToFullName_3504_, lean_object* v___x_3505_, lean_object* v_givenNameView_3506_, lean_object* v_as_3507_, lean_object* v_i_3508_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3509_; lean_object* v_res_3510_; 
v_skipAuxDecl_boxed_3509_ = lean_unbox(v_skipAuxDecl_3503_);
v_res_3510_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3502_, v_skipAuxDecl_boxed_3509_, v_auxDeclToFullName_3504_, v___x_3505_, v_givenNameView_3506_, v_as_3507_, v_i_3508_);
lean_dec_ref(v_as_3507_);
lean_dec(v_auxDeclToFullName_3504_);
lean_dec(v_givenName_3502_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3511_, uint8_t v_skipAuxDecl_3512_, lean_object* v_auxDeclToFullName_3513_, lean_object* v___x_3514_, lean_object* v_givenNameView_3515_, lean_object* v_as_3516_, lean_object* v_i_3517_){
_start:
{
lean_object* v_zero_3518_; uint8_t v_isZero_3519_; 
v_zero_3518_ = lean_unsigned_to_nat(0u);
v_isZero_3519_ = lean_nat_dec_eq(v_i_3517_, v_zero_3518_);
if (v_isZero_3519_ == 1)
{
lean_object* v___x_3520_; 
lean_dec(v_i_3517_);
lean_dec_ref(v_givenNameView_3515_);
lean_dec(v___x_3514_);
v___x_3520_ = lean_box(0);
return v___x_3520_;
}
else
{
lean_object* v_one_3521_; lean_object* v_n_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v_one_3521_ = lean_unsigned_to_nat(1u);
v_n_3522_ = lean_nat_sub(v_i_3517_, v_one_3521_);
lean_dec(v_i_3517_);
v___x_3523_ = lean_array_fget_borrowed(v_as_3516_, v_n_3522_);
lean_inc_ref(v_givenNameView_3515_);
lean_inc(v___x_3514_);
v___x_3524_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3511_, v_skipAuxDecl_3512_, v_auxDeclToFullName_3513_, v___x_3514_, v_givenNameView_3515_, v___x_3523_);
if (lean_obj_tag(v___x_3524_) == 0)
{
v_i_3517_ = v_n_3522_;
goto _start;
}
else
{
lean_dec(v_n_3522_);
lean_dec_ref(v_givenNameView_3515_);
lean_dec(v___x_3514_);
return v___x_3524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3526_, uint8_t v_skipAuxDecl_3527_, lean_object* v_auxDeclToFullName_3528_, lean_object* v___x_3529_, lean_object* v_givenNameView_3530_, lean_object* v_x_3531_){
_start:
{
if (lean_obj_tag(v_x_3531_) == 0)
{
lean_object* v_cs_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v_cs_3532_ = lean_ctor_get(v_x_3531_, 0);
v___x_3533_ = lean_array_get_size(v_cs_3532_);
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3526_, v_skipAuxDecl_3527_, v_auxDeclToFullName_3528_, v___x_3529_, v_givenNameView_3530_, v_cs_3532_, v___x_3533_);
return v___x_3534_;
}
else
{
lean_object* v_vs_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v_vs_3535_ = lean_ctor_get(v_x_3531_, 0);
v___x_3536_ = lean_array_get_size(v_vs_3535_);
v___x_3537_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3526_, v_skipAuxDecl_3527_, v_auxDeclToFullName_3528_, v___x_3529_, v_givenNameView_3530_, v_vs_3535_, v___x_3536_);
return v___x_3537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3538_, lean_object* v_skipAuxDecl_3539_, lean_object* v_auxDeclToFullName_3540_, lean_object* v___x_3541_, lean_object* v_givenNameView_3542_, lean_object* v_x_3543_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3544_; lean_object* v_res_3545_; 
v_skipAuxDecl_boxed_3544_ = lean_unbox(v_skipAuxDecl_3539_);
v_res_3545_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3538_, v_skipAuxDecl_boxed_3544_, v_auxDeclToFullName_3540_, v___x_3541_, v_givenNameView_3542_, v_x_3543_);
lean_dec_ref(v_x_3543_);
lean_dec(v_auxDeclToFullName_3540_);
lean_dec(v_givenName_3538_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3546_, lean_object* v_skipAuxDecl_3547_, lean_object* v_auxDeclToFullName_3548_, lean_object* v___x_3549_, lean_object* v_givenNameView_3550_, lean_object* v_as_3551_, lean_object* v_i_3552_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3553_; lean_object* v_res_3554_; 
v_skipAuxDecl_boxed_3553_ = lean_unbox(v_skipAuxDecl_3547_);
v_res_3554_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3546_, v_skipAuxDecl_boxed_3553_, v_auxDeclToFullName_3548_, v___x_3549_, v_givenNameView_3550_, v_as_3551_, v_i_3552_);
lean_dec_ref(v_as_3551_);
lean_dec(v_auxDeclToFullName_3548_);
lean_dec(v_givenName_3546_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3555_, uint8_t v_skipAuxDecl_3556_, lean_object* v_auxDeclToFullName_3557_, lean_object* v___x_3558_, lean_object* v_givenNameView_3559_, lean_object* v_t_3560_){
_start:
{
lean_object* v_root_3561_; lean_object* v_tail_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v_root_3561_ = lean_ctor_get(v_t_3560_, 0);
v_tail_3562_ = lean_ctor_get(v_t_3560_, 1);
v___x_3563_ = lean_array_get_size(v_tail_3562_);
lean_inc_ref(v_givenNameView_3559_);
lean_inc(v___x_3558_);
v___x_3564_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3555_, v_skipAuxDecl_3556_, v_auxDeclToFullName_3557_, v___x_3558_, v_givenNameView_3559_, v_tail_3562_, v___x_3563_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3555_, v_skipAuxDecl_3556_, v_auxDeclToFullName_3557_, v___x_3558_, v_givenNameView_3559_, v_root_3561_);
return v___x_3565_;
}
else
{
lean_dec_ref(v_givenNameView_3559_);
lean_dec(v___x_3558_);
return v___x_3564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3566_, lean_object* v_skipAuxDecl_3567_, lean_object* v_auxDeclToFullName_3568_, lean_object* v___x_3569_, lean_object* v_givenNameView_3570_, lean_object* v_t_3571_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3572_; lean_object* v_res_3573_; 
v_skipAuxDecl_boxed_3572_ = lean_unbox(v_skipAuxDecl_3567_);
v_res_3573_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3566_, v_skipAuxDecl_boxed_3572_, v_auxDeclToFullName_3568_, v___x_3569_, v_givenNameView_3570_, v_t_3571_);
lean_dec_ref(v_t_3571_);
lean_dec(v_auxDeclToFullName_3568_);
lean_dec(v_givenName_3566_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3574_, lean_object* v_currNamespace_3575_, lean_object* v_decls_3576_, lean_object* v_givenNameView_3577_, uint8_t v_skipAuxDecl_3578_){
_start:
{
lean_object* v_givenName_3579_; lean_object* v_localDecl_x3f_3580_; 
lean_inc_ref(v_givenNameView_3577_);
v_givenName_3579_ = l_Lean_MacroScopesView_review(v_givenNameView_3577_);
v_localDecl_x3f_3580_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3579_, v_skipAuxDecl_3578_, v_auxDeclToFullName_3574_, v_currNamespace_3575_, v_givenNameView_3577_, v_decls_3576_);
if (lean_obj_tag(v_localDecl_x3f_3580_) == 0)
{
if (v_skipAuxDecl_3578_ == 0)
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3580_, v_givenName_3579_, v_decls_3576_);
lean_dec(v_givenName_3579_);
return v___x_3581_;
}
else
{
lean_dec(v_givenName_3579_);
return v_localDecl_x3f_3580_;
}
}
else
{
lean_dec(v_givenName_3579_);
return v_localDecl_x3f_3580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3582_, lean_object* v_currNamespace_3583_, lean_object* v_decls_3584_, lean_object* v_givenNameView_3585_, lean_object* v_skipAuxDecl_3586_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3587_; lean_object* v_res_3588_; 
v_skipAuxDecl_boxed_3587_ = lean_unbox(v_skipAuxDecl_3586_);
v_res_3588_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3582_, v_currNamespace_3583_, v_decls_3584_, v_givenNameView_3585_, v_skipAuxDecl_boxed_3587_);
lean_dec_ref(v_decls_3584_);
lean_dec(v_auxDeclToFullName_3582_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_lctx_3597_; lean_object* v_toCold_3598_; lean_object* v_decls_3599_; lean_object* v_auxDeclToFullName_3600_; lean_object* v_currNamespace_3601_; lean_object* v_view_3602_; lean_object* v_name_3603_; lean_object* v_findLocalDecl_x3f_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; lean_object* v___x_3607_; 
v_lctx_3597_ = lean_ctor_get(v___y_3592_, 2);
v_toCold_3598_ = lean_ctor_get(v___y_3594_, 0);
v_decls_3599_ = lean_ctor_get(v_lctx_3597_, 1);
v_auxDeclToFullName_3600_ = lean_ctor_get(v_lctx_3597_, 2);
v_currNamespace_3601_ = lean_ctor_get(v_toCold_3598_, 4);
v_view_3602_ = l_Lean_extractMacroScopes(v_n_3589_);
v_name_3603_ = lean_ctor_get(v_view_3602_, 0);
lean_inc(v_name_3603_);
lean_inc_ref(v_decls_3599_);
lean_inc(v_currNamespace_3601_);
lean_inc(v_auxDeclToFullName_3600_);
v_findLocalDecl_x3f_3604_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3604_, 0, v_auxDeclToFullName_3600_);
lean_closure_set(v_findLocalDecl_x3f_3604_, 1, v_currNamespace_3601_);
lean_closure_set(v_findLocalDecl_x3f_3604_, 2, v_decls_3599_);
v___x_3605_ = lean_box(0);
v___x_3606_ = 0;
v___x_3607_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3602_, v_findLocalDecl_x3f_3604_, v_name_3603_, v___x_3605_, v___x_3606_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec_ref(v_view_3602_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3617_, lean_object* v_b_3618_){
_start:
{
if (lean_obj_tag(v_as_x27_3617_) == 0)
{
lean_object* v___x_3620_; 
v___x_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3620_, 0, v_b_3618_);
return v___x_3620_;
}
else
{
lean_object* v_head_3621_; lean_object* v_tail_3622_; lean_object* v_config_3623_; lean_object* v_extensions_3624_; lean_object* v_extra_3625_; lean_object* v_extraInj_3626_; lean_object* v_extraFacts_3627_; lean_object* v_symPrios_3628_; lean_object* v_norm_3629_; lean_object* v_normProcs_3630_; lean_object* v_anchorRefs_x3f_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3640_; 
v_head_3621_ = lean_ctor_get(v_as_x27_3617_, 0);
v_tail_3622_ = lean_ctor_get(v_as_x27_3617_, 1);
v_config_3623_ = lean_ctor_get(v_b_3618_, 0);
v_extensions_3624_ = lean_ctor_get(v_b_3618_, 1);
v_extra_3625_ = lean_ctor_get(v_b_3618_, 2);
v_extraInj_3626_ = lean_ctor_get(v_b_3618_, 3);
v_extraFacts_3627_ = lean_ctor_get(v_b_3618_, 4);
v_symPrios_3628_ = lean_ctor_get(v_b_3618_, 5);
v_norm_3629_ = lean_ctor_get(v_b_3618_, 6);
v_normProcs_3630_ = lean_ctor_get(v_b_3618_, 7);
v_anchorRefs_x3f_3631_ = lean_ctor_get(v_b_3618_, 8);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_b_3618_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3633_ = v_b_3618_;
v_isShared_3634_ = v_isSharedCheck_3640_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_anchorRefs_x3f_3631_);
lean_inc(v_normProcs_3630_);
lean_inc(v_norm_3629_);
lean_inc(v_symPrios_3628_);
lean_inc(v_extraFacts_3627_);
lean_inc(v_extraInj_3626_);
lean_inc(v_extra_3625_);
lean_inc(v_extensions_3624_);
lean_inc(v_config_3623_);
lean_dec(v_b_3618_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3640_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3635_; lean_object* v___x_3637_; 
lean_inc(v_head_3621_);
v___x_3635_ = l_Lean_PersistentArray_push___redArg(v_extra_3625_, v_head_3621_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 2, v___x_3635_);
v___x_3637_ = v___x_3633_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_config_3623_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_extensions_3624_);
lean_ctor_set(v_reuseFailAlloc_3639_, 2, v___x_3635_);
lean_ctor_set(v_reuseFailAlloc_3639_, 3, v_extraInj_3626_);
lean_ctor_set(v_reuseFailAlloc_3639_, 4, v_extraFacts_3627_);
lean_ctor_set(v_reuseFailAlloc_3639_, 5, v_symPrios_3628_);
lean_ctor_set(v_reuseFailAlloc_3639_, 6, v_norm_3629_);
lean_ctor_set(v_reuseFailAlloc_3639_, 7, v_normProcs_3630_);
lean_ctor_set(v_reuseFailAlloc_3639_, 8, v_anchorRefs_x3f_3631_);
v___x_3637_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
v_as_x27_3617_ = v_tail_3622_;
v_b_3618_ = v___x_3637_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3641_, lean_object* v_b_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3641_, v_b_3642_);
lean_dec(v_as_x27_3641_);
return v_res_3644_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3647_ = l_Lean_stringToMessageData(v___x_3646_);
return v___x_3647_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3650_ = l_Lean_stringToMessageData(v___x_3649_);
return v___x_3650_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v___x_3653_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3656_ = l_Lean_stringToMessageData(v___x_3655_);
return v___x_3656_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3659_ = l_Lean_stringToMessageData(v___x_3658_);
return v___x_3659_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3662_ = l_Lean_stringToMessageData(v___x_3661_);
return v___x_3662_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3665_ = l_Lean_stringToMessageData(v___x_3664_);
return v___x_3665_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3668_ = l_Lean_stringToMessageData(v___x_3667_);
return v___x_3668_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3671_ = l_Lean_stringToMessageData(v___x_3670_);
return v___x_3671_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3674_ = l_Lean_stringToMessageData(v___x_3673_);
return v___x_3674_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3677_ = l_Lean_stringToMessageData(v___x_3676_);
return v___x_3677_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23(void){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22));
v___x_3680_ = l_Lean_stringToMessageData(v___x_3679_);
return v___x_3680_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25(void){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24));
v___x_3683_ = l_Lean_stringToMessageData(v___x_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3684_, lean_object* v_p_3685_, lean_object* v_mod_x3f_3686_, lean_object* v_id_3687_, uint8_t v_minIndexable_3688_, uint8_t v_only_3689_, uint8_t v_incremental_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_){
_start:
{
uint8_t v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; uint8_t v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v_a_3853_; lean_object* v___y_4078_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4089_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4090_ = lean_box(0);
lean_inc(v_id_3687_);
v___x_4091_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3687_, v___x_4090_, v_a_3695_, v_a_3696_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4092_);
lean_dec_ref_known(v___x_4091_, 1);
v_a_3853_ = v_a_4092_;
goto v___jp_3852_;
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4167_; 
v_a_4093_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4095_ = v___x_4091_;
v_isShared_4096_ = v_isSharedCheck_4167_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4091_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4167_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
uint8_t v___y_4098_; uint8_t v___x_4165_; 
v___x_4165_ = l_Lean_Exception_isInterrupt(v_a_4093_);
if (v___x_4165_ == 0)
{
uint8_t v___x_4166_; 
lean_inc(v_a_4093_);
v___x_4166_ = l_Lean_Exception_isRuntime(v_a_4093_);
v___y_4098_ = v___x_4166_;
goto v___jp_4097_;
}
else
{
v___y_4098_ = v___x_4165_;
goto v___jp_4097_;
}
v___jp_4097_:
{
if (v___y_4098_ == 0)
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
lean_del_object(v___x_4095_);
v___x_4099_ = l_Lean_TSyntax_getId(v_id_3687_);
lean_inc(v___x_4099_);
v___x_4100_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4099_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v___x_4100_, 1);
if (lean_obj_tag(v_a_4101_) == 0)
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_4099_, v_a_3695_, v_a_3696_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4131_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4105_ = v___x_4102_;
v_isShared_4106_ = v_isSharedCheck_4131_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4102_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4131_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
if (lean_obj_tag(v_a_4103_) == 1)
{
lean_del_object(v___x_4105_);
lean_dec(v_a_4093_);
if (lean_obj_tag(v_mod_x3f_3686_) == 1)
{
lean_object* v_val_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
lean_dec_ref_known(v_a_4103_, 1);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v_val_4107_ = lean_ctor_get(v_mod_x3f_3686_, 0);
lean_inc(v_val_4107_);
lean_dec_ref_known(v_mod_x3f_3686_, 1);
v___x_4108_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4109_ = l_Lean_MessageData_ofName(v___x_4099_);
v___x_4110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4108_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4110_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
v___x_4113_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4107_, v___x_4112_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
lean_dec(v_val_4107_);
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4113_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4113_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
else
{
lean_object* v_val_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
lean_dec(v___x_4099_);
v_val_4122_ = lean_ctor_get(v_a_4103_, 0);
lean_inc(v_val_4122_);
lean_dec_ref_known(v_a_4103_, 1);
v___x_4123_ = lean_box(0);
lean_inc_ref(v_params_3684_);
v___x_4124_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3684_, v_val_4122_, v___x_4089_, v___y_4098_, v___x_4123_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
lean_dec(v_val_4122_);
v___y_4078_ = v___x_4124_;
goto v___jp_4077_;
}
}
else
{
lean_object* v___x_4125_; uint8_t v___x_4126_; 
lean_dec(v_a_4103_);
v___x_4125_ = l_Lean_Name_getPrefix(v___x_4099_);
lean_dec(v___x_4099_);
v___x_4126_ = l_Lean_Name_isAnonymous(v___x_4125_);
lean_dec(v___x_4125_);
if (v___x_4126_ == 0)
{
lean_object* v___x_4127_; 
lean_del_object(v___x_4105_);
lean_dec(v_a_4093_);
v___x_4127_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3684_, v_p_3685_, v_mod_x3f_3686_, v_id_3687_, v_minIndexable_3688_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
return v___x_4127_;
}
else
{
lean_object* v___x_4129_; 
lean_dec(v_id_3687_);
lean_dec(v_mod_x3f_3686_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set_tag(v___x_4105_, 1);
lean_ctor_set(v___x_4105_, 0, v_a_4093_);
v___x_4129_ = v___x_4105_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4093_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
lean_dec(v___x_4099_);
lean_dec(v_a_4093_);
lean_dec(v_id_3687_);
lean_dec(v_mod_x3f_3686_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v_a_4132_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4102_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4102_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
else
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec_ref_known(v_a_4101_, 1);
lean_dec(v___x_4099_);
lean_dec(v_a_4093_);
lean_dec(v_mod_x3f_3686_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v___x_4140_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23);
lean_inc(v_id_3687_);
v___x_4141_ = l_Lean_MessageData_ofSyntax(v_id_3687_);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4140_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25);
v___x_4144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4142_);
lean_ctor_set(v___x_4144_, 1, v___x_4143_);
v___x_4145_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3687_, v___x_4144_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
lean_dec(v_id_3687_);
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4145_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4145_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
lean_dec(v___x_4099_);
lean_dec(v_a_4093_);
lean_dec(v_id_3687_);
lean_dec(v_mod_x3f_3686_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v_a_4154_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4100_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4100_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
else
{
lean_object* v___x_4163_; 
lean_dec(v_id_3687_);
lean_dec(v_mod_x3f_3686_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
if (v_isShared_4096_ == 0)
{
v___x_4163_ = v___x_4095_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4093_);
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
v___jp_3698_:
{
uint8_t v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = 0;
lean_inc(v___y_3700_);
v___x_3708_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3700_, v___x_3707_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
if (lean_obj_tag(v_a_3709_) == 1)
{
lean_object* v_val_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
lean_dec(v___y_3700_);
v_val_3710_ = lean_ctor_get(v_a_3709_, 0);
lean_inc_n(v_val_3710_, 2);
lean_dec_ref_known(v_a_3709_, 1);
v___x_3711_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3684_, v_val_3710_, v___x_3707_);
v___x_3712_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3710_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3723_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3723_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3723_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
if (lean_obj_tag(v_a_3713_) == 1)
{
lean_object* v_val_3717_; lean_object* v_ctors_3718_; lean_object* v___x_3719_; 
lean_del_object(v___x_3715_);
v_val_3717_ = lean_ctor_get(v_a_3713_, 0);
lean_inc(v_val_3717_);
lean_dec_ref_known(v_a_3713_, 1);
v_ctors_3718_ = lean_ctor_get(v_val_3717_, 4);
lean_inc(v_ctors_3718_);
lean_dec(v_val_3717_);
v___x_3719_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3685_, v_id_3687_, v_minIndexable_3688_, v_ctors_3718_, v___x_3711_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec(v_ctors_3718_);
lean_dec(v_p_3685_);
return v___x_3719_;
}
else
{
lean_object* v___x_3721_; 
lean_dec(v_a_3713_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3711_);
v___x_3721_ = v___x_3715_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3711_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_dec_ref(v___x_3711_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
v_a_3724_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3712_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3712_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
else
{
lean_object* v_toCold_3732_; lean_object* v_currRecDepth_3733_; lean_object* v_ref_3734_; uint16_t v_optionFlags_3735_; uint8_t v_suppressElabErrors_3736_; uint8_t v_isRecordingDeps_3737_; lean_object* v___x_3738_; lean_object* v_ref_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_dec(v_a_3709_);
v_toCold_3732_ = lean_ctor_get(v___y_3705_, 0);
v_currRecDepth_3733_ = lean_ctor_get(v___y_3705_, 1);
v_ref_3734_ = lean_ctor_get(v___y_3705_, 2);
v_optionFlags_3735_ = lean_ctor_get_uint16(v___y_3705_, sizeof(void*)*3);
v_suppressElabErrors_3736_ = lean_ctor_get_uint8(v___y_3705_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3737_ = lean_ctor_get_uint8(v___y_3705_, sizeof(void*)*3 + 3);
v___x_3738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8));
v_ref_3739_ = l_Lean_replaceRef(v_p_3685_, v_ref_3734_);
lean_dec(v_p_3685_);
lean_inc(v_currRecDepth_3733_);
lean_inc_ref(v_toCold_3732_);
v___x_3740_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3740_, 0, v_toCold_3732_);
lean_ctor_set(v___x_3740_, 1, v_currRecDepth_3733_);
lean_ctor_set(v___x_3740_, 2, v_ref_3739_);
lean_ctor_set_uint16(v___x_3740_, sizeof(void*)*3, v_optionFlags_3735_);
lean_ctor_set_uint8(v___x_3740_, sizeof(void*)*3 + 2, v_suppressElabErrors_3736_);
lean_ctor_set_uint8(v___x_3740_, sizeof(void*)*3 + 3, v_isRecordingDeps_3737_);
v___x_3741_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3684_, v_id_3687_, v___y_3700_, v___x_3738_, v_minIndexable_3688_, v___y_3699_, v___y_3699_, v___y_3703_, v___y_3704_, v___x_3740_, v___y_3706_);
lean_dec_ref_known(v___x_3740_, 3);
return v___x_3741_;
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec(v___y_3700_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v_a_3742_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3708_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3708_);
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
lean_object* v___x_3759_; 
v___x_3759_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3688_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
lean_dec_ref_known(v___x_3759_, 1);
v___x_3760_ = l_Lean_Meta_Grind_grindExt;
v___x_3761_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3760_, v___y_3758_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v___x_3761_, 1);
lean_inc(v___y_3751_);
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___y_3751_);
v___x_3764_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3762_, v___x_3763_);
lean_dec_ref_known(v___x_3763_, 1);
lean_dec(v_a_3762_);
v___x_3765_ = lean_box(0);
v___x_3766_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3752_, v___x_3764_, v___x_3765_);
lean_dec(v___y_3752_);
v___x_3767_ = l_List_isEmpty___redArg(v___x_3766_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; 
lean_dec(v___y_3751_);
lean_dec(v_p_3685_);
v___x_3768_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3766_, v_params_3684_);
lean_dec(v___x_3766_);
return v___x_3768_;
}
else
{
lean_object* v___x_3769_; uint8_t v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec(v___x_3766_);
lean_dec_ref(v_params_3684_);
v___x_3769_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3770_ = 0;
v___x_3771_ = l_Lean_MessageData_ofConstName(v___y_3751_, v___x_3770_);
v___x_3772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3769_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3685_, v___x_3774_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v_p_3685_);
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
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
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_dec(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v_a_3784_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3761_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3761_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v_a_3792_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3759_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3759_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
v___jp_3800_:
{
lean_object* v___x_3807_; 
v___x_3807_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3688_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_toCold_3808_; lean_object* v_currRecDepth_3809_; lean_object* v_ref_3810_; uint16_t v_optionFlags_3811_; uint8_t v_suppressElabErrors_3812_; uint8_t v_isRecordingDeps_3813_; lean_object* v_ref_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
lean_dec_ref_known(v___x_3807_, 1);
v_toCold_3808_ = lean_ctor_get(v___y_3805_, 0);
v_currRecDepth_3809_ = lean_ctor_get(v___y_3805_, 1);
v_ref_3810_ = lean_ctor_get(v___y_3805_, 2);
v_optionFlags_3811_ = lean_ctor_get_uint16(v___y_3805_, sizeof(void*)*3);
v_suppressElabErrors_3812_ = lean_ctor_get_uint8(v___y_3805_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3813_ = lean_ctor_get_uint8(v___y_3805_, sizeof(void*)*3 + 3);
v_ref_3814_ = l_Lean_replaceRef(v_p_3685_, v_ref_3810_);
lean_dec(v_p_3685_);
lean_inc(v_currRecDepth_3809_);
lean_inc_ref(v_toCold_3808_);
v___x_3815_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3815_, 0, v_toCold_3808_);
lean_ctor_set(v___x_3815_, 1, v_currRecDepth_3809_);
lean_ctor_set(v___x_3815_, 2, v_ref_3814_);
lean_ctor_set_uint16(v___x_3815_, sizeof(void*)*3, v_optionFlags_3811_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*3 + 2, v_suppressElabErrors_3812_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*3 + 3, v_isRecordingDeps_3813_);
lean_inc(v___y_3802_);
v___x_3816_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3802_, v___y_3801_, v___x_3815_, v___y_3806_);
lean_dec_ref_known(v___x_3815_, 3);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3824_; 
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3824_ == 0)
{
lean_object* v_unused_3825_; 
v_unused_3825_ = lean_ctor_get(v___x_3816_, 0);
lean_dec(v_unused_3825_);
v___x_3818_ = v___x_3816_;
v_isShared_3819_ = v_isSharedCheck_3824_;
goto v_resetjp_3817_;
}
else
{
lean_dec(v___x_3816_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3824_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3820_; lean_object* v___x_3822_; 
v___x_3820_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3684_, v___y_3802_, v___y_3801_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v___x_3820_);
v___x_3822_ = v___x_3818_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v___x_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec(v___y_3802_);
lean_dec_ref(v_params_3684_);
v_a_3826_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3816_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3816_);
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
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec(v___y_3802_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v_a_3834_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3807_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3807_);
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
v___jp_3842_:
{
lean_object* v_ctors_3850_; lean_object* v___x_3851_; 
v_ctors_3850_ = lean_ctor_get(v___y_3843_, 4);
lean_inc(v_ctors_3850_);
lean_dec_ref(v___y_3843_);
v___x_3851_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3685_, v_id_3687_, v_minIndexable_3688_, v_ctors_3850_, v_params_3684_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v_ctors_3850_);
lean_dec(v_p_3685_);
return v___x_3851_;
}
v___jp_3852_:
{
uint8_t v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = 1;
lean_inc(v_a_3853_);
v___x_3855_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_3853_, v___x_3854_, v_a_3691_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_dec_ref_known(v___x_3855_, 1);
if (lean_obj_tag(v_mod_x3f_3686_) == 1)
{
lean_object* v_val_3856_; lean_object* v___x_3857_; 
v_val_3856_ = lean_ctor_get(v_mod_x3f_3686_, 0);
lean_inc(v_val_3856_);
lean_dec_ref_known(v_mod_x3f_3686_, 1);
v___x_3857_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_3856_, v_a_3695_, v_a_3696_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_4060_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_4060_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_4060_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
switch(lean_obj_tag(v_a_3858_))
{
case 0:
{
lean_object* v_k_3862_; 
lean_del_object(v___x_3860_);
v_k_3862_ = lean_ctor_get(v_a_3858_, 0);
lean_inc(v_k_3862_);
lean_dec_ref_known(v_a_3858_, 1);
if (lean_obj_tag(v_k_3862_) == 9)
{
lean_dec(v_id_3687_);
if (v_only_3689_ == 0)
{
lean_object* v_toCold_3863_; lean_object* v_currRecDepth_3864_; lean_object* v_ref_3865_; uint16_t v_optionFlags_3866_; uint8_t v_suppressElabErrors_3867_; uint8_t v_isRecordingDeps_3868_; lean_object* v_ref_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v_toCold_3863_ = lean_ctor_get(v_a_3695_, 0);
v_currRecDepth_3864_ = lean_ctor_get(v_a_3695_, 1);
v_ref_3865_ = lean_ctor_get(v_a_3695_, 2);
v_optionFlags_3866_ = lean_ctor_get_uint16(v_a_3695_, sizeof(void*)*3);
v_suppressElabErrors_3867_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3868_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*3 + 3);
v_ref_3869_ = l_Lean_replaceRef(v_p_3685_, v_ref_3865_);
lean_inc(v_currRecDepth_3864_);
lean_inc_ref(v_toCold_3863_);
v___x_3870_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3870_, 0, v_toCold_3863_);
lean_ctor_set(v___x_3870_, 1, v_currRecDepth_3864_);
lean_ctor_set(v___x_3870_, 2, v_ref_3869_);
lean_ctor_set_uint16(v___x_3870_, sizeof(void*)*3, v_optionFlags_3866_);
lean_ctor_set_uint8(v___x_3870_, sizeof(void*)*3 + 2, v_suppressElabErrors_3867_);
lean_ctor_set_uint8(v___x_3870_, sizeof(void*)*3 + 3, v_isRecordingDeps_3868_);
v___x_3871_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_3870_, v_a_3696_);
lean_dec_ref_known(v___x_3870_, 3);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_dec_ref_known(v___x_3871_, 1);
v___y_3751_ = v_a_3853_;
v___y_3752_ = v_k_3862_;
v___y_3753_ = v_a_3691_;
v___y_3754_ = v_a_3692_;
v___y_3755_ = v_a_3693_;
v___y_3756_ = v_a_3694_;
v___y_3757_ = v_a_3695_;
v___y_3758_ = v_a_3696_;
goto v___jp_3750_;
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_dec(v_a_3853_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3871_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3871_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
else
{
v___y_3751_ = v_a_3853_;
v___y_3752_ = v_k_3862_;
v___y_3753_ = v_a_3691_;
v___y_3754_ = v_a_3692_;
v___y_3755_ = v_a_3693_;
v___y_3756_ = v_a_3694_;
v___y_3757_ = v_a_3695_;
v___y_3758_ = v_a_3696_;
goto v___jp_3750_;
}
}
else
{
lean_object* v_toCold_3880_; lean_object* v_currRecDepth_3881_; lean_object* v_ref_3882_; uint16_t v_optionFlags_3883_; uint8_t v_suppressElabErrors_3884_; uint8_t v_isRecordingDeps_3885_; uint8_t v___x_3886_; lean_object* v_ref_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v_toCold_3880_ = lean_ctor_get(v_a_3695_, 0);
v_currRecDepth_3881_ = lean_ctor_get(v_a_3695_, 1);
v_ref_3882_ = lean_ctor_get(v_a_3695_, 2);
v_optionFlags_3883_ = lean_ctor_get_uint16(v_a_3695_, sizeof(void*)*3);
v_suppressElabErrors_3884_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3885_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*3 + 3);
v___x_3886_ = 0;
v_ref_3887_ = l_Lean_replaceRef(v_p_3685_, v_ref_3882_);
lean_dec(v_p_3685_);
lean_inc(v_currRecDepth_3881_);
lean_inc_ref(v_toCold_3880_);
v___x_3888_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3888_, 0, v_toCold_3880_);
lean_ctor_set(v___x_3888_, 1, v_currRecDepth_3881_);
lean_ctor_set(v___x_3888_, 2, v_ref_3887_);
lean_ctor_set_uint16(v___x_3888_, sizeof(void*)*3, v_optionFlags_3883_);
lean_ctor_set_uint8(v___x_3888_, sizeof(void*)*3 + 2, v_suppressElabErrors_3884_);
lean_ctor_set_uint8(v___x_3888_, sizeof(void*)*3 + 3, v_isRecordingDeps_3885_);
v___x_3889_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3684_, v_id_3687_, v_a_3853_, v_k_3862_, v_minIndexable_3688_, v___x_3886_, v___x_3854_, v_a_3693_, v_a_3694_, v___x_3888_, v_a_3696_);
lean_dec_ref_known(v___x_3888_, 3);
return v___x_3889_;
}
}
case 1:
{
lean_del_object(v___x_3860_);
lean_dec(v_id_3687_);
if (v_incremental_3690_ == 0)
{
uint8_t v_eager_3890_; 
v_eager_3890_ = lean_ctor_get_uint8(v_a_3858_, 0);
lean_dec_ref_known(v_a_3858_, 0);
v___y_3801_ = v_eager_3890_;
v___y_3802_ = v_a_3853_;
v___y_3803_ = v_a_3693_;
v___y_3804_ = v_a_3694_;
v___y_3805_ = v_a_3695_;
v___y_3806_ = v_a_3696_;
goto v___jp_3800_;
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_dec_ref_known(v_a_3858_, 0);
lean_dec(v_a_3853_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v___x_3891_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3892_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_3891_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
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
case 2:
{
uint8_t v___x_3901_; lean_object* v___x_3902_; 
lean_del_object(v___x_3860_);
v___x_3901_ = 0;
lean_inc(v_a_3853_);
v___x_3902_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3853_, v___x_3901_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref_known(v___x_3902_, 1);
if (lean_obj_tag(v_a_3903_) == 1)
{
lean_dec(v_a_3853_);
if (v_incremental_3690_ == 0)
{
lean_object* v_val_3904_; 
v_val_3904_ = lean_ctor_get(v_a_3903_, 0);
lean_inc(v_val_3904_);
lean_dec_ref_known(v_a_3903_, 1);
v___y_3843_ = v_val_3904_;
v___y_3844_ = v_a_3691_;
v___y_3845_ = v_a_3692_;
v___y_3846_ = v_a_3693_;
v___y_3847_ = v_a_3694_;
v___y_3848_ = v_a_3695_;
v___y_3849_ = v_a_3696_;
goto v___jp_3842_;
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec_ref_known(v_a_3903_, 1);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v___x_3905_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3906_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_3905_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3906_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3906_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
else
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec(v_a_3903_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v___x_3915_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_3916_ = l_Lean_MessageData_ofConstName(v_a_3853_, v___x_3901_);
v___x_3917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3915_);
lean_ctor_set(v___x_3917_, 1, v___x_3916_);
v___x_3918_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_3919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3917_);
lean_ctor_set(v___x_3919_, 1, v___x_3918_);
v___x_3920_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_3919_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3920_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3920_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec(v_a_3853_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v_a_3929_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3902_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3902_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
case 3:
{
lean_del_object(v___x_3860_);
v___y_3699_ = v___x_3854_;
v___y_3700_ = v_a_3853_;
v___y_3701_ = v_a_3691_;
v___y_3702_ = v_a_3692_;
v___y_3703_ = v_a_3693_;
v___y_3704_ = v_a_3694_;
v___y_3705_ = v_a_3695_;
v___y_3706_ = v_a_3696_;
goto v___jp_3698_;
}
case 4:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
lean_del_object(v___x_3860_);
lean_dec(v_a_3853_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v___x_3937_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_3938_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_3937_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3938_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3938_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
case 5:
{
lean_object* v_prio_3947_; lean_object* v___x_3948_; 
lean_del_object(v___x_3860_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
v_prio_3947_ = lean_ctor_get(v_a_3858_, 0);
lean_inc(v_prio_3947_);
lean_dec_ref_known(v_a_3858_, 1);
v___x_3948_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3688_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3972_; 
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3972_ == 0)
{
lean_object* v_unused_3973_; 
v_unused_3973_ = lean_ctor_get(v___x_3948_, 0);
lean_dec(v_unused_3973_);
v___x_3950_ = v___x_3948_;
v_isShared_3951_ = v_isSharedCheck_3972_;
goto v_resetjp_3949_;
}
else
{
lean_dec(v___x_3948_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3972_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v_config_3952_; lean_object* v_extensions_3953_; lean_object* v_extra_3954_; lean_object* v_extraInj_3955_; lean_object* v_extraFacts_3956_; lean_object* v_symPrios_3957_; lean_object* v_norm_3958_; lean_object* v_normProcs_3959_; lean_object* v_anchorRefs_x3f_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3971_; 
v_config_3952_ = lean_ctor_get(v_params_3684_, 0);
v_extensions_3953_ = lean_ctor_get(v_params_3684_, 1);
v_extra_3954_ = lean_ctor_get(v_params_3684_, 2);
v_extraInj_3955_ = lean_ctor_get(v_params_3684_, 3);
v_extraFacts_3956_ = lean_ctor_get(v_params_3684_, 4);
v_symPrios_3957_ = lean_ctor_get(v_params_3684_, 5);
v_norm_3958_ = lean_ctor_get(v_params_3684_, 6);
v_normProcs_3959_ = lean_ctor_get(v_params_3684_, 7);
v_anchorRefs_x3f_3960_ = lean_ctor_get(v_params_3684_, 8);
v_isSharedCheck_3971_ = !lean_is_exclusive(v_params_3684_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3962_ = v_params_3684_;
v_isShared_3963_ = v_isSharedCheck_3971_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_anchorRefs_x3f_3960_);
lean_inc(v_normProcs_3959_);
lean_inc(v_norm_3958_);
lean_inc(v_symPrios_3957_);
lean_inc(v_extraFacts_3956_);
lean_inc(v_extraInj_3955_);
lean_inc(v_extra_3954_);
lean_inc(v_extensions_3953_);
lean_inc(v_config_3952_);
lean_dec(v_params_3684_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3971_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3964_; lean_object* v___x_3966_; 
v___x_3964_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_3957_, v_a_3853_, v_prio_3947_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 5, v___x_3964_);
v___x_3966_ = v___x_3962_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_config_3952_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v_extensions_3953_);
lean_ctor_set(v_reuseFailAlloc_3970_, 2, v_extra_3954_);
lean_ctor_set(v_reuseFailAlloc_3970_, 3, v_extraInj_3955_);
lean_ctor_set(v_reuseFailAlloc_3970_, 4, v_extraFacts_3956_);
lean_ctor_set(v_reuseFailAlloc_3970_, 5, v___x_3964_);
lean_ctor_set(v_reuseFailAlloc_3970_, 6, v_norm_3958_);
lean_ctor_set(v_reuseFailAlloc_3970_, 7, v_normProcs_3959_);
lean_ctor_set(v_reuseFailAlloc_3970_, 8, v_anchorRefs_x3f_3960_);
v___x_3966_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
lean_object* v___x_3968_; 
if (v_isShared_3951_ == 0)
{
lean_ctor_set(v___x_3950_, 0, v___x_3966_);
v___x_3968_ = v___x_3950_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3966_);
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
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
lean_dec(v_prio_3947_);
lean_dec(v_a_3853_);
lean_dec_ref(v_params_3684_);
v_a_3974_ = lean_ctor_get(v___x_3948_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3948_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3948_);
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
case 6:
{
lean_object* v___x_3982_; 
lean_del_object(v___x_3860_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
v___x_3982_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3853_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_4007_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3985_ = v___x_3982_;
v_isShared_3986_ = v_isSharedCheck_4007_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_dec(v___x_3982_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_4007_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v_config_3987_; lean_object* v_extensions_3988_; lean_object* v_extra_3989_; lean_object* v_extraInj_3990_; lean_object* v_extraFacts_3991_; lean_object* v_symPrios_3992_; lean_object* v_norm_3993_; lean_object* v_normProcs_3994_; lean_object* v_anchorRefs_x3f_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4006_; 
v_config_3987_ = lean_ctor_get(v_params_3684_, 0);
v_extensions_3988_ = lean_ctor_get(v_params_3684_, 1);
v_extra_3989_ = lean_ctor_get(v_params_3684_, 2);
v_extraInj_3990_ = lean_ctor_get(v_params_3684_, 3);
v_extraFacts_3991_ = lean_ctor_get(v_params_3684_, 4);
v_symPrios_3992_ = lean_ctor_get(v_params_3684_, 5);
v_norm_3993_ = lean_ctor_get(v_params_3684_, 6);
v_normProcs_3994_ = lean_ctor_get(v_params_3684_, 7);
v_anchorRefs_x3f_3995_ = lean_ctor_get(v_params_3684_, 8);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_params_3684_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3997_ = v_params_3684_;
v_isShared_3998_ = v_isSharedCheck_4006_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_anchorRefs_x3f_3995_);
lean_inc(v_normProcs_3994_);
lean_inc(v_norm_3993_);
lean_inc(v_symPrios_3992_);
lean_inc(v_extraFacts_3991_);
lean_inc(v_extraInj_3990_);
lean_inc(v_extra_3989_);
lean_inc(v_extensions_3988_);
lean_inc(v_config_3987_);
lean_dec(v_params_3684_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4006_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_3999_; lean_object* v___x_4001_; 
v___x_3999_ = l_Lean_PersistentArray_push___redArg(v_extraInj_3990_, v_a_3983_);
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 3, v___x_3999_);
v___x_4001_ = v___x_3997_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_config_3987_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_extensions_3988_);
lean_ctor_set(v_reuseFailAlloc_4005_, 2, v_extra_3989_);
lean_ctor_set(v_reuseFailAlloc_4005_, 3, v___x_3999_);
lean_ctor_set(v_reuseFailAlloc_4005_, 4, v_extraFacts_3991_);
lean_ctor_set(v_reuseFailAlloc_4005_, 5, v_symPrios_3992_);
lean_ctor_set(v_reuseFailAlloc_4005_, 6, v_norm_3993_);
lean_ctor_set(v_reuseFailAlloc_4005_, 7, v_normProcs_3994_);
lean_ctor_set(v_reuseFailAlloc_4005_, 8, v_anchorRefs_x3f_3995_);
v___x_4001_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
lean_object* v___x_4003_; 
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 0, v___x_4001_);
v___x_4003_ = v___x_3985_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_4001_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec_ref(v_params_3684_);
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
case 7:
{
lean_object* v___x_4016_; lean_object* v___x_4018_; 
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
v___x_4016_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3684_, v_a_3853_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_4016_);
v___x_4018_ = v___x_3860_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4016_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
case 8:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_dec_ref_known(v_a_3858_, 0);
lean_del_object(v___x_3860_);
lean_dec(v_a_3853_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v___x_4020_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_4021_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4020_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_4021_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4021_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
case 9:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_del_object(v___x_3860_);
lean_dec(v_a_3853_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v___x_4030_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_4031_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4030_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_4031_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4031_);
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
case 10:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_dec_ref_known(v_a_3858_, 0);
lean_del_object(v___x_3860_);
lean_dec(v_a_3853_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v___x_4040_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_4041_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4040_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4041_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4041_);
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
default: 
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_del_object(v___x_3860_);
lean_dec(v_a_3853_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v___x_4050_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
v___x_4051_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4050_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_4051_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4051_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec(v_a_3853_);
lean_dec(v_id_3687_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v_a_4061_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_3857_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_3857_);
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
lean_dec(v_mod_x3f_3686_);
v___y_3699_ = v___x_3854_;
v___y_3700_ = v_a_3853_;
v___y_3701_ = v_a_3691_;
v___y_3702_ = v_a_3692_;
v___y_3703_ = v_a_3693_;
v___y_3704_ = v_a_3694_;
v___y_3705_ = v_a_3695_;
v___y_3706_ = v_a_3696_;
goto v___jp_3698_;
}
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
lean_dec(v_a_3853_);
lean_dec(v_id_3687_);
lean_dec(v_mod_x3f_3686_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v_a_4069_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_3855_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_3855_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
v___jp_4077_:
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4088_; 
v_a_4079_ = lean_ctor_get(v___y_4078_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___y_4078_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4081_ = v___y_4078_;
v_isShared_4082_ = v_isSharedCheck_4088_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___y_4078_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4088_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
if (lean_obj_tag(v_a_4079_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4085_; 
lean_dec(v_id_3687_);
lean_dec(v_mod_x3f_3686_);
lean_dec(v_p_3685_);
lean_dec_ref(v_params_3684_);
v_a_4083_ = lean_ctor_get(v_a_4079_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v_a_4079_, 1);
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 0, v_a_4083_);
v___x_4085_ = v___x_4081_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4083_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
else
{
lean_object* v_a_4087_; 
lean_del_object(v___x_4081_);
v_a_4087_ = lean_ctor_get(v_a_4079_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v_a_4079_, 1);
v_a_3853_ = v_a_4087_;
goto v___jp_3852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4168_, lean_object* v_p_4169_, lean_object* v_mod_x3f_4170_, lean_object* v_id_4171_, lean_object* v_minIndexable_4172_, lean_object* v_only_4173_, lean_object* v_incremental_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
uint8_t v_minIndexable_boxed_4182_; uint8_t v_only_boxed_4183_; uint8_t v_incremental_boxed_4184_; lean_object* v_res_4185_; 
v_minIndexable_boxed_4182_ = lean_unbox(v_minIndexable_4172_);
v_only_boxed_4183_ = lean_unbox(v_only_4173_);
v_incremental_boxed_4184_ = lean_unbox(v_incremental_4174_);
v_res_4185_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4168_, v_p_4169_, v_mod_x3f_4170_, v_id_4171_, v_minIndexable_boxed_4182_, v_only_boxed_4183_, v_incremental_boxed_4184_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
lean_dec(v_a_4178_);
lean_dec_ref(v_a_4177_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4186_, lean_object* v_id_4187_, uint8_t v_minIndexable_4188_, lean_object* v_as_4189_, lean_object* v_as_x27_4190_, lean_object* v_b_4191_, lean_object* v_a_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v___x_4200_; 
v___x_4200_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4186_, v_id_4187_, v_minIndexable_4188_, v_as_x27_4190_, v_b_4191_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4201_, lean_object* v_id_4202_, lean_object* v_minIndexable_4203_, lean_object* v_as_4204_, lean_object* v_as_x27_4205_, lean_object* v_b_4206_, lean_object* v_a_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
uint8_t v_minIndexable_boxed_4215_; lean_object* v_res_4216_; 
v_minIndexable_boxed_4215_ = lean_unbox(v_minIndexable_4203_);
v_res_4216_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4201_, v_id_4202_, v_minIndexable_boxed_4215_, v_as_4204_, v_as_x27_4205_, v_b_4206_, v_a_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v_as_x27_4205_);
lean_dec(v_as_4204_);
lean_dec(v_p_4201_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4217_, lean_object* v_as_x27_4218_, lean_object* v_b_4219_, lean_object* v_a_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4218_, v_b_4219_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4229_, lean_object* v_as_x27_4230_, lean_object* v_b_4231_, lean_object* v_a_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4229_, v_as_x27_4230_, v_b_4231_, v_a_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec(v_as_x27_4230_);
lean_dec(v_as_4229_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4241_, lean_object* v_ref_4242_, lean_object* v_msg_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v___x_4251_; 
v___x_4251_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4242_, v_msg_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4252_, lean_object* v_ref_4253_, lean_object* v_msg_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4252_, v_ref_4253_, v_msg_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v_ref_4253_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4263_, lean_object* v_id_4264_, uint8_t v_minIndexable_4265_, lean_object* v_as_4266_, lean_object* v_as_x27_4267_, lean_object* v_b_4268_, lean_object* v_a_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v___x_4277_; 
v___x_4277_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4263_, v_id_4264_, v_minIndexable_4265_, v_as_x27_4267_, v_b_4268_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4278_, lean_object* v_id_4279_, lean_object* v_minIndexable_4280_, lean_object* v_as_4281_, lean_object* v_as_x27_4282_, lean_object* v_b_4283_, lean_object* v_a_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
uint8_t v_minIndexable_boxed_4292_; lean_object* v_res_4293_; 
v_minIndexable_boxed_4292_ = lean_unbox(v_minIndexable_4280_);
v_res_4293_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4278_, v_id_4279_, v_minIndexable_boxed_4292_, v_as_4281_, v_as_x27_4282_, v_b_4283_, v_a_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v_as_x27_4282_);
lean_dec(v_as_4281_);
lean_dec(v_p_4278_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4294_, lean_object* v_t_4295_, lean_object* v_k_4296_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4295_, v_k_4296_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4298_, lean_object* v_t_4299_, lean_object* v_k_4300_){
_start:
{
lean_object* v_res_4301_; 
v_res_4301_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4298_, v_t_4299_, v_k_4300_);
lean_dec(v_k_4300_);
lean_dec(v_t_4299_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4302_, uint8_t v_skipAuxDecl_4303_, lean_object* v_auxDeclToFullName_4304_, lean_object* v___x_4305_, lean_object* v_givenNameView_4306_, lean_object* v_as_4307_, lean_object* v_i_4308_, lean_object* v_a_4309_){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4302_, v_skipAuxDecl_4303_, v_auxDeclToFullName_4304_, v___x_4305_, v_givenNameView_4306_, v_as_4307_, v_i_4308_);
return v___x_4310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4311_, lean_object* v_skipAuxDecl_4312_, lean_object* v_auxDeclToFullName_4313_, lean_object* v___x_4314_, lean_object* v_givenNameView_4315_, lean_object* v_as_4316_, lean_object* v_i_4317_, lean_object* v_a_4318_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4319_; lean_object* v_res_4320_; 
v_skipAuxDecl_boxed_4319_ = lean_unbox(v_skipAuxDecl_4312_);
v_res_4320_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4311_, v_skipAuxDecl_boxed_4319_, v_auxDeclToFullName_4313_, v___x_4314_, v_givenNameView_4315_, v_as_4316_, v_i_4317_, v_a_4318_);
lean_dec_ref(v_as_4316_);
lean_dec(v_auxDeclToFullName_4313_);
lean_dec(v_givenName_4311_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4321_, lean_object* v_givenName_4322_, lean_object* v_as_4323_, lean_object* v_i_4324_, lean_object* v_a_4325_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4321_, v_givenName_4322_, v_as_4323_, v_i_4324_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4327_, lean_object* v_givenName_4328_, lean_object* v_as_4329_, lean_object* v_i_4330_, lean_object* v_a_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4327_, v_givenName_4328_, v_as_4329_, v_i_4330_, v_a_4331_);
lean_dec_ref(v_as_4329_);
lean_dec(v_givenName_4328_);
lean_dec(v_localDecl_x3f_4327_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4333_, uint8_t v_skipAuxDecl_4334_, lean_object* v_auxDeclToFullName_4335_, lean_object* v___x_4336_, lean_object* v_givenNameView_4337_, lean_object* v_as_4338_, lean_object* v_i_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v___x_4341_; 
v___x_4341_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4333_, v_skipAuxDecl_4334_, v_auxDeclToFullName_4335_, v___x_4336_, v_givenNameView_4337_, v_as_4338_, v_i_4339_);
return v___x_4341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4342_, lean_object* v_skipAuxDecl_4343_, lean_object* v_auxDeclToFullName_4344_, lean_object* v___x_4345_, lean_object* v_givenNameView_4346_, lean_object* v_as_4347_, lean_object* v_i_4348_, lean_object* v_a_4349_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4350_; lean_object* v_res_4351_; 
v_skipAuxDecl_boxed_4350_ = lean_unbox(v_skipAuxDecl_4343_);
v_res_4351_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4342_, v_skipAuxDecl_boxed_4350_, v_auxDeclToFullName_4344_, v___x_4345_, v_givenNameView_4346_, v_as_4347_, v_i_4348_, v_a_4349_);
lean_dec_ref(v_as_4347_);
lean_dec(v_auxDeclToFullName_4344_);
lean_dec(v_givenName_4342_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4352_, lean_object* v_givenName_4353_, lean_object* v_as_4354_, lean_object* v_i_4355_, lean_object* v_a_4356_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4352_, v_givenName_4353_, v_as_4354_, v_i_4355_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4358_, lean_object* v_givenName_4359_, lean_object* v_as_4360_, lean_object* v_i_4361_, lean_object* v_a_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4358_, v_givenName_4359_, v_as_4360_, v_i_4361_, v_a_4362_);
lean_dec_ref(v_as_4360_);
lean_dec(v_givenName_4359_);
lean_dec(v_localDecl_x3f_4358_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4364_, v___y_4369_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec_ref(v_opt_4373_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4382_, lean_object* v_msgData_4383_, uint8_t v_severity_4384_, uint8_t v_isSilent_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v___x_4393_; 
v___x_4393_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4382_, v_msgData_4383_, v_severity_4384_, v_isSilent_4385_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4394_, lean_object* v_msgData_4395_, lean_object* v_severity_4396_, lean_object* v_isSilent_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
uint8_t v_severity_boxed_4405_; uint8_t v_isSilent_boxed_4406_; lean_object* v_res_4407_; 
v_severity_boxed_4405_ = lean_unbox(v_severity_4396_);
v_isSilent_boxed_4406_ = lean_unbox(v_isSilent_4397_);
v_res_4407_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4394_, v_msgData_4395_, v_severity_boxed_4405_, v_isSilent_boxed_4406_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
lean_dec(v_ref_4394_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4408_, uint8_t v___x_4409_, lean_object* v_b_4410_, lean_object* v_____r_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4419_ = lean_box(0);
v___x_4420_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4408_, v___x_4419_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v___x_4422_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc_n(v_a_4421_, 2);
lean_dec_ref_known(v___x_4420_, 1);
v___x_4422_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4421_, v___x_4409_, v___y_4412_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4422_) == 0)
{
uint8_t v___x_4423_; lean_object* v___x_4424_; 
lean_dec_ref_known(v___x_4422_, 1);
v___x_4423_ = 0;
lean_inc(v_a_4421_);
v___x_4424_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4421_, v___x_4423_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4484_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4427_ = v___x_4424_;
v_isShared_4428_ = v_isSharedCheck_4484_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4424_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4484_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
if (lean_obj_tag(v_a_4425_) == 1)
{
lean_object* v_val_4429_; lean_object* v___x_4430_; 
lean_del_object(v___x_4427_);
lean_dec(v_a_4421_);
v_val_4429_ = lean_ctor_get(v_a_4425_, 0);
lean_inc_n(v_val_4429_, 2);
lean_dec_ref_known(v_a_4425_, 1);
v___x_4430_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4429_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v___x_4431_; 
lean_dec_ref_known(v___x_4430_, 1);
v___x_4431_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4410_, v_val_4429_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4441_; 
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4434_ = v___x_4431_;
v_isShared_4435_ = v_isSharedCheck_4441_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4431_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4441_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4439_; 
v___x_4436_ = lean_box(0);
v___x_4437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4436_);
lean_ctor_set(v___x_4437_, 1, v_a_4432_);
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 0, v___x_4437_);
v___x_4439_ = v___x_4434_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
v_a_4442_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4431_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4431_);
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
else
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_dec(v_val_4429_);
lean_dec_ref(v_b_4410_);
v_a_4450_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4430_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4430_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
else
{
uint8_t v___x_4458_; 
lean_dec(v_a_4425_);
lean_inc(v_a_4421_);
v___x_4458_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4410_, v_a_4421_);
if (v___x_4458_ == 0)
{
lean_object* v___x_4459_; 
lean_del_object(v___x_4427_);
v___x_4459_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4410_, v_a_4421_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4469_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4462_ = v___x_4459_;
v_isShared_4463_ = v_isSharedCheck_4469_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4459_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4469_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4467_; 
v___x_4464_ = lean_box(0);
v___x_4465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4464_);
lean_ctor_set(v___x_4465_, 1, v_a_4460_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v___x_4465_);
v___x_4467_ = v___x_4462_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4465_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
v_a_4470_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4459_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4459_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
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
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4482_; 
v___x_4478_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4410_, v_a_4421_);
v___x_4479_ = lean_box(0);
v___x_4480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
lean_ctor_set(v___x_4480_, 1, v___x_4478_);
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v___x_4480_);
v___x_4482_ = v___x_4427_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
lean_dec(v_a_4421_);
lean_dec_ref(v_b_4410_);
v_a_4485_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4424_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4424_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
}
else
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
lean_dec(v_a_4421_);
lean_dec_ref(v_b_4410_);
v_a_4493_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4495_ = v___x_4422_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4422_);
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
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
lean_dec_ref(v_b_4410_);
v_a_4501_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4420_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4420_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4509_, lean_object* v___x_4510_, lean_object* v_b_4511_, lean_object* v_____r_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
uint8_t v___x_17514__boxed_4520_; lean_object* v_res_4521_; 
v___x_17514__boxed_4520_ = lean_unbox(v___x_4510_);
v_res_4521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4509_, v___x_17514__boxed_4520_, v_b_4511_, v_____r_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4525_, lean_object* v_b_4526_, lean_object* v_a_4527_, uint8_t v___x_4528_, uint8_t v_only_4529_, uint8_t v_incremental_4530_, lean_object* v_x_4531_, lean_object* v_mod_x3f_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4540_ = lean_unsigned_to_nat(1u);
v___x_4541_ = l_Lean_Syntax_getArg(v___x_4525_, v___x_4540_);
if (v___x_4528_ == 0)
{
lean_object* v___x_4602_; uint8_t v___x_4603_; 
v___x_4602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4541_);
v___x_4603_ = l_Lean_Syntax_isOfKind(v___x_4541_, v___x_4602_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; 
v___x_4604_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4526_, v_a_4527_, v_mod_x3f_4532_, v___x_4541_, v___x_4528_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
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
v___x_4543_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4526_, v_a_4527_, v_mod_x3f_4532_, v___x_4541_, v___x_4528_, v_only_4529_, v_incremental_4530_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
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
v___x_4571_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4526_, v_a_4527_, v_mod_x3f_4532_, v___x_4541_, v___x_4528_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
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
lean_dec(v_a_4527_);
lean_dec_ref(v_b_4526_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4623_, lean_object* v_b_4624_, lean_object* v_a_4625_, lean_object* v___x_4626_, lean_object* v_only_4627_, lean_object* v_incremental_4628_, lean_object* v_x_4629_, lean_object* v_mod_x3f_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
uint8_t v___x_17732__boxed_4638_; uint8_t v_only_boxed_4639_; uint8_t v_incremental_boxed_4640_; lean_object* v_res_4641_; 
v___x_17732__boxed_4638_ = lean_unbox(v___x_4626_);
v_only_boxed_4639_ = lean_unbox(v_only_4627_);
v_incremental_boxed_4640_ = lean_unbox(v_incremental_4628_);
v_res_4641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4623_, v_b_4624_, v_a_4625_, v___x_17732__boxed_4638_, v_only_boxed_4639_, v_incremental_boxed_4640_, v_x_4629_, v_mod_x3f_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___x_4623_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4642_, lean_object* v___x_4643_, lean_object* v_____r_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_){
_start:
{
lean_object* v___x_4652_; 
v___x_4652_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4642_, v___x_4643_, v___y_4649_, v___y_4650_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4662_; 
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4655_ = v___x_4652_;
v_isShared_4656_ = v_isSharedCheck_4662_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4652_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4662_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4660_; 
v___x_4657_ = lean_box(0);
v___x_4658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
lean_ctor_set(v___x_4658_, 1, v_a_4653_);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 0, v___x_4658_);
v___x_4660_ = v___x_4655_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4658_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
v_a_4663_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4652_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4652_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4671_, lean_object* v___x_4672_, lean_object* v_____r_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_){
_start:
{
lean_object* v_res_4681_; 
v_res_4681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4671_, v___x_4672_, v_____r_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___x_4672_);
return v_res_4681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4682_, lean_object* v_b_4683_, lean_object* v_a_4684_, uint8_t v___x_4685_, uint8_t v_only_4686_, uint8_t v_incremental_4687_, uint8_t v___x_4688_, lean_object* v_x_4689_, lean_object* v_mod_x3f_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4698_ = lean_unsigned_to_nat(2u);
v___x_4699_ = l_Lean_Syntax_getArg(v___x_4682_, v___x_4698_);
if (v___x_4688_ == 0)
{
lean_object* v___x_4760_; uint8_t v___x_4761_; 
v___x_4760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4699_);
v___x_4761_ = l_Lean_Syntax_isOfKind(v___x_4699_, v___x_4760_);
if (v___x_4761_ == 0)
{
lean_object* v___x_4762_; 
v___x_4762_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4683_, v_a_4684_, v_mod_x3f_4690_, v___x_4699_, v___x_4685_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
if (lean_obj_tag(v___x_4762_) == 0)
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4772_; 
v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4762_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4765_ = v___x_4762_;
v_isShared_4766_ = v_isSharedCheck_4772_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4762_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4772_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4770_; 
v___x_4767_ = lean_box(0);
v___x_4768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4768_, 0, v___x_4767_);
lean_ctor_set(v___x_4768_, 1, v_a_4763_);
if (v_isShared_4766_ == 0)
{
lean_ctor_set(v___x_4765_, 0, v___x_4768_);
v___x_4770_ = v___x_4765_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v___x_4768_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
else
{
lean_object* v_a_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4780_; 
v_a_4773_ = lean_ctor_get(v___x_4762_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4762_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4775_ = v___x_4762_;
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_a_4773_);
lean_dec(v___x_4762_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4778_; 
if (v_isShared_4776_ == 0)
{
v___x_4778_ = v___x_4775_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4773_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
else
{
goto v___jp_4720_;
}
}
else
{
goto v___jp_4720_;
}
v___jp_4700_:
{
lean_object* v___x_4701_; 
v___x_4701_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4683_, v_a_4684_, v_mod_x3f_4690_, v___x_4699_, v___x_4685_, v_only_4686_, v_incremental_4687_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4711_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4704_ = v___x_4701_;
v_isShared_4705_ = v_isSharedCheck_4711_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4701_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4711_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4709_; 
v___x_4706_ = lean_box(0);
v___x_4707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4706_);
lean_ctor_set(v___x_4707_, 1, v_a_4702_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 0, v___x_4707_);
v___x_4709_ = v___x_4704_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v___x_4707_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
else
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4719_; 
v_a_4712_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4714_ = v___x_4701_;
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4701_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4712_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
return v___x_4717_;
}
}
}
}
v___jp_4720_:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4721_ = l_Lean_TSyntax_getId(v___x_4699_);
v___x_4722_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4721_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
lean_inc(v_a_4723_);
lean_dec_ref_known(v___x_4722_, 1);
if (lean_obj_tag(v_a_4723_) == 1)
{
lean_object* v_val_4724_; lean_object* v_snd_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4750_; 
v_val_4724_ = lean_ctor_get(v_a_4723_, 0);
lean_inc(v_val_4724_);
lean_dec_ref_known(v_a_4723_, 1);
v_snd_4725_ = lean_ctor_get(v_val_4724_, 1);
v_isSharedCheck_4750_ = !lean_is_exclusive(v_val_4724_);
if (v_isSharedCheck_4750_ == 0)
{
lean_object* v_unused_4751_; 
v_unused_4751_ = lean_ctor_get(v_val_4724_, 0);
lean_dec(v_unused_4751_);
v___x_4727_ = v_val_4724_;
v_isShared_4728_ = v_isSharedCheck_4750_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_snd_4725_);
lean_dec(v_val_4724_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4750_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
if (lean_obj_tag(v_snd_4725_) == 1)
{
lean_object* v___x_4729_; 
lean_dec_ref_known(v_snd_4725_, 2);
v___x_4729_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4683_, v_a_4684_, v_mod_x3f_4690_, v___x_4699_, v___x_4685_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4741_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4732_ = v___x_4729_;
v_isShared_4733_ = v_isSharedCheck_4741_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4729_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4741_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4734_; lean_object* v___x_4736_; 
v___x_4734_ = lean_box(0);
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 1, v_a_4730_);
lean_ctor_set(v___x_4727_, 0, v___x_4734_);
v___x_4736_ = v___x_4727_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v___x_4734_);
lean_ctor_set(v_reuseFailAlloc_4740_, 1, v_a_4730_);
v___x_4736_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4738_; 
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 0, v___x_4736_);
v___x_4738_ = v___x_4732_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v___x_4736_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
else
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
lean_del_object(v___x_4727_);
v_a_4742_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4744_ = v___x_4729_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4729_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4747_; 
if (v_isShared_4745_ == 0)
{
v___x_4747_ = v___x_4744_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
else
{
lean_del_object(v___x_4727_);
lean_dec(v_snd_4725_);
goto v___jp_4700_;
}
}
}
else
{
lean_dec(v_a_4723_);
goto v___jp_4700_;
}
}
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
lean_dec(v___x_4699_);
lean_dec(v_mod_x3f_4690_);
lean_dec(v_a_4684_);
lean_dec_ref(v_b_4683_);
v_a_4752_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4722_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4722_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4781_, lean_object* v_b_4782_, lean_object* v_a_4783_, lean_object* v___x_4784_, lean_object* v_only_4785_, lean_object* v_incremental_4786_, lean_object* v___x_4787_, lean_object* v_x_4788_, lean_object* v_mod_x3f_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_){
_start:
{
uint8_t v___x_18001__boxed_4797_; uint8_t v_only_boxed_4798_; uint8_t v_incremental_boxed_4799_; uint8_t v___x_18002__boxed_4800_; lean_object* v_res_4801_; 
v___x_18001__boxed_4797_ = lean_unbox(v___x_4784_);
v_only_boxed_4798_ = lean_unbox(v_only_4785_);
v_incremental_boxed_4799_ = lean_unbox(v_incremental_4786_);
v___x_18002__boxed_4800_ = lean_unbox(v___x_4787_);
v_res_4801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4781_, v_b_4782_, v_a_4783_, v___x_18001__boxed_4797_, v_only_boxed_4798_, v_incremental_boxed_4799_, v___x_18002__boxed_4800_, v_x_4788_, v_mod_x3f_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
lean_dec(v___y_4793_);
lean_dec_ref(v___y_4792_);
lean_dec(v___y_4791_);
lean_dec_ref(v___y_4790_);
lean_dec(v___x_4781_);
return v_res_4801_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4810_ = l_Lean_stringToMessageData(v___x_4809_);
return v___x_4810_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13(void){
_start:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12));
v___x_4837_ = l_Lean_stringToMessageData(v___x_4836_);
return v___x_4837_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4843_ = l_Lean_stringToMessageData(v___x_4842_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4844_, uint8_t v_only_4845_, uint8_t v_incremental_4846_, lean_object* v_as_4847_, size_t v_sz_4848_, size_t v_i_4849_, lean_object* v_b_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_){
_start:
{
lean_object* v_snd_4859_; lean_object* v___y_4864_; uint8_t v___y_4865_; lean_object* v_a_4869_; lean_object* v___y_4873_; uint8_t v___x_4877_; 
v___x_4877_ = lean_usize_dec_lt(v_i_4849_, v_sz_4848_);
if (v___x_4877_ == 0)
{
lean_object* v___x_4878_; 
v___x_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4878_, 0, v_b_4850_);
return v___x_4878_;
}
else
{
lean_object* v_a_4879_; lean_object* v___x_4880_; uint8_t v___x_4881_; 
v_a_4879_ = lean_array_uget_borrowed(v_as_4847_, v_i_4849_);
v___x_4880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_4879_);
v___x_4881_ = l_Lean_Syntax_isOfKind(v_a_4879_, v___x_4880_);
if (v___x_4881_ == 0)
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4882_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4879_);
v___x_4883_ = l_Lean_MessageData_ofSyntax(v_a_4879_);
v___x_4884_ = l_Lean_indentD(v___x_4883_);
v___x_4885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4882_);
lean_ctor_set(v___x_4885_, 1, v___x_4884_);
v___x_4886_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4885_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_dec_ref_known(v___x_4886_, 1);
v_snd_4859_ = v_b_4850_;
goto v___jp_4858_;
}
else
{
lean_object* v_a_4887_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc(v_a_4887_);
lean_dec_ref_known(v___x_4886_, 1);
v_a_4869_ = v_a_4887_;
goto v___jp_4868_;
}
}
else
{
lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; uint8_t v___x_4891_; 
v___x_4888_ = lean_unsigned_to_nat(0u);
v___x_4889_ = l_Lean_Syntax_getArg(v_a_4879_, v___x_4888_);
v___x_4890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_4889_);
v___x_4891_ = l_Lean_Syntax_isOfKind(v___x_4889_, v___x_4890_);
if (v___x_4891_ == 0)
{
lean_object* v___x_4892_; uint8_t v___x_4893_; 
v___x_4892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_4889_);
v___x_4893_ = l_Lean_Syntax_isOfKind(v___x_4889_, v___x_4892_);
if (v___x_4893_ == 0)
{
lean_object* v___x_4894_; uint8_t v___x_4895_; 
v___x_4894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_4889_);
v___x_4895_ = l_Lean_Syntax_isOfKind(v___x_4889_, v___x_4894_);
if (v___x_4895_ == 0)
{
lean_object* v___x_4896_; uint8_t v___x_4897_; 
v___x_4896_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_4889_);
v___x_4897_ = l_Lean_Syntax_isOfKind(v___x_4889_, v___x_4896_);
if (v___x_4897_ == 0)
{
lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
lean_dec(v___x_4889_);
v___x_4898_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4879_);
v___x_4899_ = l_Lean_MessageData_ofSyntax(v_a_4879_);
v___x_4900_ = l_Lean_indentD(v___x_4899_);
v___x_4901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4901_, 0, v___x_4898_);
lean_ctor_set(v___x_4901_, 1, v___x_4900_);
v___x_4902_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4901_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4902_) == 0)
{
lean_dec_ref_known(v___x_4902_, 1);
v_snd_4859_ = v_b_4850_;
goto v___jp_4858_;
}
else
{
lean_object* v_a_4903_; 
v_a_4903_ = lean_ctor_get(v___x_4902_, 0);
lean_inc(v_a_4903_);
lean_dec_ref_known(v___x_4902_, 1);
v_a_4869_ = v_a_4903_;
goto v___jp_4868_;
}
}
else
{
lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4904_ = lean_unsigned_to_nat(1u);
v___x_4905_ = l_Lean_Syntax_getArg(v___x_4889_, v___x_4904_);
lean_dec(v___x_4889_);
if (v___x_4895_ == 0)
{
lean_object* v___x_4914_; uint8_t v___x_4915_; 
v___x_4914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15));
lean_inc(v___x_4905_);
v___x_4915_ = l_Lean_Syntax_isOfKind(v___x_4905_, v___x_4914_);
if (v___x_4915_ == 0)
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
lean_dec(v___x_4905_);
v___x_4916_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4879_);
v___x_4917_ = l_Lean_MessageData_ofSyntax(v_a_4879_);
v___x_4918_ = l_Lean_indentD(v___x_4917_);
v___x_4919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4916_);
lean_ctor_set(v___x_4919_, 1, v___x_4918_);
v___x_4920_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4919_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_dec_ref_known(v___x_4920_, 1);
v_snd_4859_ = v_b_4850_;
goto v___jp_4858_;
}
else
{
lean_object* v_a_4921_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref_known(v___x_4920_, 1);
v_a_4869_ = v_a_4921_;
goto v___jp_4868_;
}
}
else
{
goto v___jp_4906_;
}
}
else
{
goto v___jp_4906_;
}
v___jp_4906_:
{
if (v_only_4845_ == 0)
{
lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4907_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13);
v___x_4908_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_4905_, v___x_4907_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; lean_object* v___x_4910_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_a_4909_);
lean_dec_ref_known(v___x_4908_, 1);
lean_inc_ref(v_b_4850_);
v___x_4910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4850_, v___x_4905_, v_a_4909_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___x_4905_);
v___y_4873_ = v___x_4910_;
goto v___jp_4872_;
}
else
{
lean_object* v_a_4911_; 
lean_dec(v___x_4905_);
v_a_4911_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4908_, 1);
v_a_4869_ = v_a_4911_;
goto v___jp_4868_;
}
}
else
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4912_ = lean_box(0);
lean_inc_ref(v_b_4850_);
v___x_4913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4850_, v___x_4905_, v___x_4912_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___x_4905_);
v___y_4873_ = v___x_4913_;
goto v___jp_4872_;
}
}
}
}
else
{
lean_object* v___x_4922_; lean_object* v___x_4923_; uint8_t v___x_4924_; 
v___x_4922_ = lean_unsigned_to_nat(1u);
v___x_4923_ = l_Lean_Syntax_getArg(v___x_4889_, v___x_4922_);
v___x_4924_ = l_Lean_Syntax_isNone(v___x_4923_);
if (v___x_4924_ == 0)
{
uint8_t v___x_4925_; 
lean_inc(v___x_4923_);
v___x_4925_ = l_Lean_Syntax_matchesNull(v___x_4923_, v___x_4922_);
if (v___x_4925_ == 0)
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; 
lean_dec(v___x_4923_);
lean_dec(v___x_4889_);
v___x_4926_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4879_);
v___x_4927_ = l_Lean_MessageData_ofSyntax(v_a_4879_);
v___x_4928_ = l_Lean_indentD(v___x_4927_);
v___x_4929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4929_, 0, v___x_4926_);
lean_ctor_set(v___x_4929_, 1, v___x_4928_);
v___x_4930_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4929_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_dec_ref_known(v___x_4930_, 1);
v_snd_4859_ = v_b_4850_;
goto v___jp_4858_;
}
else
{
lean_object* v_a_4931_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___x_4930_, 1);
v_a_4869_ = v_a_4931_;
goto v___jp_4868_;
}
}
else
{
lean_object* v___x_4932_; 
v___x_4932_ = l_Lean_Syntax_getArg(v___x_4923_, v___x_4888_);
lean_dec(v___x_4923_);
if (v___x_4924_ == 0)
{
lean_object* v___x_4937_; uint8_t v___x_4938_; 
v___x_4937_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4932_);
v___x_4938_ = l_Lean_Syntax_isOfKind(v___x_4932_, v___x_4937_);
if (v___x_4938_ == 0)
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
lean_dec(v___x_4932_);
lean_dec(v___x_4889_);
v___x_4939_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4879_);
v___x_4940_ = l_Lean_MessageData_ofSyntax(v_a_4879_);
v___x_4941_ = l_Lean_indentD(v___x_4940_);
v___x_4942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4939_);
lean_ctor_set(v___x_4942_, 1, v___x_4941_);
v___x_4943_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4942_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_dec_ref_known(v___x_4943_, 1);
v_snd_4859_ = v_b_4850_;
goto v___jp_4858_;
}
else
{
lean_object* v_a_4944_; 
v_a_4944_ = lean_ctor_get(v___x_4943_, 0);
lean_inc(v_a_4944_);
lean_dec_ref_known(v___x_4943_, 1);
v_a_4869_ = v_a_4944_;
goto v___jp_4868_;
}
}
else
{
goto v___jp_4933_;
}
}
else
{
goto v___jp_4933_;
}
v___jp_4933_:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4934_ = lean_box(0);
v___x_4935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4932_);
lean_inc(v_a_4879_);
lean_inc_ref(v_b_4850_);
v___x_4936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4889_, v_b_4850_, v_a_4879_, v___x_4881_, v_only_4845_, v_incremental_4846_, v___x_4893_, v___x_4934_, v___x_4935_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___x_4889_);
v___y_4873_ = v___x_4936_;
goto v___jp_4872_;
}
}
}
else
{
lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
lean_dec(v___x_4923_);
v___x_4945_ = lean_box(0);
v___x_4946_ = lean_box(0);
lean_inc(v_a_4879_);
lean_inc_ref(v_b_4850_);
v___x_4947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4889_, v_b_4850_, v_a_4879_, v___x_4881_, v_only_4845_, v_incremental_4846_, v___x_4893_, v___x_4945_, v___x_4946_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___x_4889_);
v___y_4873_ = v___x_4947_;
goto v___jp_4872_;
}
}
}
else
{
lean_object* v___x_4948_; uint8_t v___x_4949_; 
v___x_4948_ = l_Lean_Syntax_getArg(v___x_4889_, v___x_4888_);
v___x_4949_ = l_Lean_Syntax_isNone(v___x_4948_);
if (v___x_4949_ == 0)
{
lean_object* v___x_4950_; uint8_t v___x_4951_; 
v___x_4950_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4948_);
v___x_4951_ = l_Lean_Syntax_matchesNull(v___x_4948_, v___x_4950_);
if (v___x_4951_ == 0)
{
lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
lean_dec(v___x_4948_);
lean_dec(v___x_4889_);
v___x_4952_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4879_);
v___x_4953_ = l_Lean_MessageData_ofSyntax(v_a_4879_);
v___x_4954_ = l_Lean_indentD(v___x_4953_);
v___x_4955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4952_);
lean_ctor_set(v___x_4955_, 1, v___x_4954_);
v___x_4956_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4955_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_dec_ref_known(v___x_4956_, 1);
v_snd_4859_ = v_b_4850_;
goto v___jp_4858_;
}
else
{
lean_object* v_a_4957_; 
v_a_4957_ = lean_ctor_get(v___x_4956_, 0);
lean_inc(v_a_4957_);
lean_dec_ref_known(v___x_4956_, 1);
v_a_4869_ = v_a_4957_;
goto v___jp_4868_;
}
}
else
{
lean_object* v___x_4958_; 
v___x_4958_ = l_Lean_Syntax_getArg(v___x_4948_, v___x_4888_);
lean_dec(v___x_4948_);
if (v___x_4949_ == 0)
{
lean_object* v___x_4963_; uint8_t v___x_4964_; 
v___x_4963_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4958_);
v___x_4964_ = l_Lean_Syntax_isOfKind(v___x_4958_, v___x_4963_);
if (v___x_4964_ == 0)
{
lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
lean_dec(v___x_4958_);
lean_dec(v___x_4889_);
v___x_4965_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4879_);
v___x_4966_ = l_Lean_MessageData_ofSyntax(v_a_4879_);
v___x_4967_ = l_Lean_indentD(v___x_4966_);
v___x_4968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4968_, 0, v___x_4965_);
lean_ctor_set(v___x_4968_, 1, v___x_4967_);
v___x_4969_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4968_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_dec_ref_known(v___x_4969_, 1);
v_snd_4859_ = v_b_4850_;
goto v___jp_4858_;
}
else
{
lean_object* v_a_4970_; 
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
lean_inc(v_a_4970_);
lean_dec_ref_known(v___x_4969_, 1);
v_a_4869_ = v_a_4970_;
goto v___jp_4868_;
}
}
else
{
goto v___jp_4959_;
}
}
else
{
goto v___jp_4959_;
}
v___jp_4959_:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4960_ = lean_box(0);
v___x_4961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4958_);
lean_inc(v_a_4879_);
lean_inc_ref(v_b_4850_);
v___x_4962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4889_, v_b_4850_, v_a_4879_, v___x_4891_, v_only_4845_, v_incremental_4846_, v___x_4960_, v___x_4961_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___x_4889_);
v___y_4873_ = v___x_4962_;
goto v___jp_4872_;
}
}
}
else
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
lean_dec(v___x_4948_);
v___x_4971_ = lean_box(0);
v___x_4972_ = lean_box(0);
lean_inc(v_a_4879_);
lean_inc_ref(v_b_4850_);
v___x_4973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4889_, v_b_4850_, v_a_4879_, v___x_4891_, v_only_4845_, v_incremental_4846_, v___x_4971_, v___x_4972_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec(v___x_4889_);
v___y_4873_ = v___x_4973_;
goto v___jp_4872_;
}
}
}
else
{
lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; uint8_t v___x_4977_; 
v___x_4974_ = lean_unsigned_to_nat(1u);
v___x_4975_ = l_Lean_Syntax_getArg(v___x_4889_, v___x_4974_);
lean_dec(v___x_4889_);
v___x_4976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4975_);
v___x_4977_ = l_Lean_Syntax_isOfKind(v___x_4975_, v___x_4976_);
if (v___x_4977_ == 0)
{
lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
lean_dec(v___x_4975_);
v___x_4978_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4879_);
v___x_4979_ = l_Lean_MessageData_ofSyntax(v_a_4879_);
v___x_4980_ = l_Lean_indentD(v___x_4979_);
v___x_4981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4978_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4981_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_dec_ref_known(v___x_4982_, 1);
v_snd_4859_ = v_b_4850_;
goto v___jp_4858_;
}
else
{
lean_object* v_a_4983_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
lean_inc(v_a_4983_);
lean_dec_ref_known(v___x_4982_, 1);
v_a_4869_ = v_a_4983_;
goto v___jp_4868_;
}
}
else
{
if (v_incremental_4846_ == 0)
{
lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4984_ = lean_box(0);
lean_inc_ref(v_b_4850_);
v___x_4985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4975_, v___x_4881_, v_b_4850_, v___x_4984_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
v___y_4873_ = v___x_4985_;
goto v___jp_4872_;
}
else
{
lean_object* v___x_4986_; lean_object* v___x_4987_; 
v___x_4986_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_4987_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_4879_, v___x_4986_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4987_) == 0)
{
lean_object* v_a_4988_; lean_object* v___x_4989_; 
v_a_4988_ = lean_ctor_get(v___x_4987_, 0);
lean_inc(v_a_4988_);
lean_dec_ref_known(v___x_4987_, 1);
lean_inc_ref(v_b_4850_);
v___x_4989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4975_, v___x_4881_, v_b_4850_, v_a_4988_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
v___y_4873_ = v___x_4989_;
goto v___jp_4872_;
}
else
{
lean_object* v_a_4990_; 
lean_dec(v___x_4975_);
v_a_4990_ = lean_ctor_get(v___x_4987_, 0);
lean_inc(v_a_4990_);
lean_dec_ref_known(v___x_4987_, 1);
v_a_4869_ = v_a_4990_;
goto v___jp_4868_;
}
}
}
}
}
}
v___jp_4858_:
{
size_t v___x_4860_; size_t v___x_4861_; 
v___x_4860_ = ((size_t)1ULL);
v___x_4861_ = lean_usize_add(v_i_4849_, v___x_4860_);
v_i_4849_ = v___x_4861_;
v_b_4850_ = v_snd_4859_;
goto _start;
}
v___jp_4863_:
{
if (v___y_4865_ == 0)
{
if (v_lax_4844_ == 0)
{
lean_object* v___x_4866_; 
lean_dec_ref(v_b_4850_);
v___x_4866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4866_, 0, v___y_4864_);
return v___x_4866_;
}
else
{
lean_dec_ref(v___y_4864_);
v_snd_4859_ = v_b_4850_;
goto v___jp_4858_;
}
}
else
{
lean_object* v___x_4867_; 
lean_dec_ref(v_b_4850_);
v___x_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4867_, 0, v___y_4864_);
return v___x_4867_;
}
}
v___jp_4868_:
{
uint8_t v___x_4870_; 
v___x_4870_ = l_Lean_Exception_isInterrupt(v_a_4869_);
if (v___x_4870_ == 0)
{
uint8_t v___x_4871_; 
lean_inc_ref(v_a_4869_);
v___x_4871_ = l_Lean_Exception_isRuntime(v_a_4869_);
v___y_4864_ = v_a_4869_;
v___y_4865_ = v___x_4871_;
goto v___jp_4863_;
}
else
{
v___y_4864_ = v_a_4869_;
v___y_4865_ = v___x_4870_;
goto v___jp_4863_;
}
}
v___jp_4872_:
{
if (lean_obj_tag(v___y_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v_snd_4875_; 
lean_dec_ref(v_b_4850_);
v_a_4874_ = lean_ctor_get(v___y_4873_, 0);
lean_inc(v_a_4874_);
lean_dec_ref_known(v___y_4873_, 1);
v_snd_4875_ = lean_ctor_get(v_a_4874_, 1);
lean_inc(v_snd_4875_);
lean_dec(v_a_4874_);
v_snd_4859_ = v_snd_4875_;
goto v___jp_4858_;
}
else
{
lean_object* v_a_4876_; 
v_a_4876_ = lean_ctor_get(v___y_4873_, 0);
lean_inc(v_a_4876_);
lean_dec_ref_known(v___y_4873_, 1);
v_a_4869_ = v_a_4876_;
goto v___jp_4868_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_4991_, lean_object* v_only_4992_, lean_object* v_incremental_4993_, lean_object* v_as_4994_, lean_object* v_sz_4995_, lean_object* v_i_4996_, lean_object* v_b_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
uint8_t v_lax_boxed_5005_; uint8_t v_only_boxed_5006_; uint8_t v_incremental_boxed_5007_; size_t v_sz_boxed_5008_; size_t v_i_boxed_5009_; lean_object* v_res_5010_; 
v_lax_boxed_5005_ = lean_unbox(v_lax_4991_);
v_only_boxed_5006_ = lean_unbox(v_only_4992_);
v_incremental_boxed_5007_ = lean_unbox(v_incremental_4993_);
v_sz_boxed_5008_ = lean_unbox_usize(v_sz_4995_);
lean_dec(v_sz_4995_);
v_i_boxed_5009_ = lean_unbox_usize(v_i_4996_);
lean_dec(v_i_4996_);
v_res_5010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_5005_, v_only_boxed_5006_, v_incremental_boxed_5007_, v_as_4994_, v_sz_boxed_5008_, v_i_boxed_5009_, v_b_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
lean_dec(v___y_5003_);
lean_dec_ref(v___y_5002_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
lean_dec(v___y_4999_);
lean_dec_ref(v___y_4998_);
lean_dec_ref(v_as_4994_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_5011_, lean_object* v_ps_5012_, uint8_t v_only_5013_, uint8_t v_lax_5014_, uint8_t v_incremental_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_){
_start:
{
size_t v_sz_5023_; size_t v___x_5024_; lean_object* v___x_5025_; 
v_sz_5023_ = lean_array_size(v_ps_5012_);
v___x_5024_ = ((size_t)0ULL);
v___x_5025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_5014_, v_only_5013_, v_incremental_5015_, v_ps_5012_, v_sz_5023_, v___x_5024_, v_params_5011_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_5026_, lean_object* v_ps_5027_, lean_object* v_only_5028_, lean_object* v_lax_5029_, lean_object* v_incremental_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_){
_start:
{
uint8_t v_only_boxed_5038_; uint8_t v_lax_boxed_5039_; uint8_t v_incremental_boxed_5040_; lean_object* v_res_5041_; 
v_only_boxed_5038_ = lean_unbox(v_only_5028_);
v_lax_boxed_5039_ = lean_unbox(v_lax_5029_);
v_incremental_boxed_5040_ = lean_unbox(v_incremental_5030_);
v_res_5041_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5026_, v_ps_5027_, v_only_boxed_5038_, v_lax_boxed_5039_, v_incremental_boxed_5040_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_);
lean_dec(v_a_5036_);
lean_dec_ref(v_a_5035_);
lean_dec(v_a_5034_);
lean_dec_ref(v_a_5033_);
lean_dec(v_a_5032_);
lean_dec_ref(v_a_5031_);
lean_dec_ref(v_ps_5027_);
return v_res_5041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_){
_start:
{
lean_object* v_origin_5053_; 
v_origin_5053_ = lean_ctor_get(v_thm_5042_, 5);
if (lean_obj_tag(v_origin_5053_) == 0)
{
lean_object* v_declName_5054_; lean_object* v___x_5055_; 
lean_inc_ref(v_origin_5053_);
lean_dec_ref(v_thm_5042_);
v_declName_5054_ = lean_ctor_get(v_origin_5053_, 0);
lean_inc(v_declName_5054_);
lean_dec_ref_known(v_origin_5053_, 1);
v___x_5055_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_5054_, v_a_5050_, v_a_5051_);
return v___x_5055_;
}
else
{
lean_object* v_proof_5056_; lean_object* v___x_5057_; 
v_proof_5056_ = lean_ctor_get(v_thm_5042_, 1);
lean_inc_ref(v_proof_5056_);
lean_dec_ref(v_thm_5042_);
v___x_5057_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_5056_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_);
return v___x_5057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_){
_start:
{
lean_object* v_res_5069_; 
v_res_5069_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_);
lean_dec(v_a_5067_);
lean_dec_ref(v_a_5066_);
lean_dec(v_a_5065_);
lean_dec_ref(v_a_5064_);
lean_dec(v_a_5063_);
lean_dec_ref(v_a_5062_);
lean_dec(v_a_5061_);
lean_dec_ref(v_a_5060_);
lean_dec(v_a_5059_);
return v_res_5069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_5070_, size_t v_sz_5071_, size_t v_i_5072_, lean_object* v_b_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
uint8_t v___x_5084_; 
v___x_5084_ = lean_usize_dec_lt(v_i_5072_, v_sz_5071_);
if (v___x_5084_ == 0)
{
lean_object* v___x_5085_; 
v___x_5085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5085_, 0, v_b_5073_);
return v___x_5085_;
}
else
{
lean_object* v_snd_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5112_; 
v_snd_5086_ = lean_ctor_get(v_b_5073_, 1);
v_isSharedCheck_5112_ = !lean_is_exclusive(v_b_5073_);
if (v_isSharedCheck_5112_ == 0)
{
lean_object* v_unused_5113_; 
v_unused_5113_ = lean_ctor_get(v_b_5073_, 0);
lean_dec(v_unused_5113_);
v___x_5088_ = v_b_5073_;
v_isShared_5089_ = v_isSharedCheck_5112_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_snd_5086_);
lean_dec(v_b_5073_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5112_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5090_; lean_object* v_a_5092_; lean_object* v_a_5099_; lean_object* v___x_5100_; 
v___x_5090_ = lean_box(0);
v_a_5099_ = lean_array_uget_borrowed(v_as_5070_, v_i_5072_);
lean_inc(v_a_5099_);
v___x_5100_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5099_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_object* v_a_5101_; uint8_t v___x_5102_; 
v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
lean_inc(v_a_5101_);
lean_dec_ref_known(v___x_5100_, 1);
v___x_5102_ = lean_unbox(v_a_5101_);
lean_dec(v_a_5101_);
if (v___x_5102_ == 0)
{
v_a_5092_ = v_snd_5086_;
goto v___jp_5091_;
}
else
{
lean_object* v___x_5103_; 
lean_inc(v_a_5099_);
v___x_5103_ = l_Lean_PersistentArray_push___redArg(v_snd_5086_, v_a_5099_);
v_a_5092_ = v___x_5103_;
goto v___jp_5091_;
}
}
else
{
lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5111_; 
lean_del_object(v___x_5088_);
lean_dec(v_snd_5086_);
v_a_5104_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_5100_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_5100_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5109_; 
if (v_isShared_5107_ == 0)
{
v___x_5109_ = v___x_5106_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5104_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
}
}
}
v___jp_5091_:
{
lean_object* v___x_5094_; 
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 1, v_a_5092_);
lean_ctor_set(v___x_5088_, 0, v___x_5090_);
v___x_5094_ = v___x_5088_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v___x_5090_);
lean_ctor_set(v_reuseFailAlloc_5098_, 1, v_a_5092_);
v___x_5094_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
size_t v___x_5095_; size_t v___x_5096_; 
v___x_5095_ = ((size_t)1ULL);
v___x_5096_ = lean_usize_add(v_i_5072_, v___x_5095_);
v_i_5072_ = v___x_5096_;
v_b_5073_ = v___x_5094_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5114_, lean_object* v_sz_5115_, lean_object* v_i_5116_, lean_object* v_b_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_){
_start:
{
size_t v_sz_boxed_5128_; size_t v_i_boxed_5129_; lean_object* v_res_5130_; 
v_sz_boxed_5128_ = lean_unbox_usize(v_sz_5115_);
lean_dec(v_sz_5115_);
v_i_boxed_5129_ = lean_unbox_usize(v_i_5116_);
lean_dec(v_i_5116_);
v_res_5130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5114_, v_sz_boxed_5128_, v_i_boxed_5129_, v_b_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
lean_dec(v___y_5126_);
lean_dec_ref(v___y_5125_);
lean_dec(v___y_5124_);
lean_dec_ref(v___y_5123_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec(v___y_5118_);
lean_dec_ref(v_as_5114_);
return v_res_5130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5131_, size_t v_sz_5132_, size_t v_i_5133_, lean_object* v_b_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_){
_start:
{
uint8_t v___x_5145_; 
v___x_5145_ = lean_usize_dec_lt(v_i_5133_, v_sz_5132_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; 
v___x_5146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5146_, 0, v_b_5134_);
return v___x_5146_;
}
else
{
lean_object* v_snd_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5173_; 
v_snd_5147_ = lean_ctor_get(v_b_5134_, 1);
v_isSharedCheck_5173_ = !lean_is_exclusive(v_b_5134_);
if (v_isSharedCheck_5173_ == 0)
{
lean_object* v_unused_5174_; 
v_unused_5174_ = lean_ctor_get(v_b_5134_, 0);
lean_dec(v_unused_5174_);
v___x_5149_ = v_b_5134_;
v_isShared_5150_ = v_isSharedCheck_5173_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_snd_5147_);
lean_dec(v_b_5134_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5173_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5151_; lean_object* v_a_5153_; lean_object* v_a_5160_; lean_object* v___x_5161_; 
v___x_5151_ = lean_box(0);
v_a_5160_ = lean_array_uget_borrowed(v_as_5131_, v_i_5133_);
lean_inc(v_a_5160_);
v___x_5161_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5160_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; uint8_t v___x_5163_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc(v_a_5162_);
lean_dec_ref_known(v___x_5161_, 1);
v___x_5163_ = lean_unbox(v_a_5162_);
lean_dec(v_a_5162_);
if (v___x_5163_ == 0)
{
v_a_5153_ = v_snd_5147_;
goto v___jp_5152_;
}
else
{
lean_object* v___x_5164_; 
lean_inc(v_a_5160_);
v___x_5164_ = l_Lean_PersistentArray_push___redArg(v_snd_5147_, v_a_5160_);
v_a_5153_ = v___x_5164_;
goto v___jp_5152_;
}
}
else
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
lean_del_object(v___x_5149_);
lean_dec(v_snd_5147_);
v_a_5165_ = lean_ctor_get(v___x_5161_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___x_5161_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5161_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
if (v_isShared_5168_ == 0)
{
v___x_5170_ = v___x_5167_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
return v___x_5170_;
}
}
}
v___jp_5152_:
{
lean_object* v___x_5155_; 
if (v_isShared_5150_ == 0)
{
lean_ctor_set(v___x_5149_, 1, v_a_5153_);
lean_ctor_set(v___x_5149_, 0, v___x_5151_);
v___x_5155_ = v___x_5149_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v___x_5151_);
lean_ctor_set(v_reuseFailAlloc_5159_, 1, v_a_5153_);
v___x_5155_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
size_t v___x_5156_; size_t v___x_5157_; lean_object* v___x_5158_; 
v___x_5156_ = ((size_t)1ULL);
v___x_5157_ = lean_usize_add(v_i_5133_, v___x_5156_);
v___x_5158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5131_, v_sz_5132_, v___x_5157_, v___x_5155_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_);
return v___x_5158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5175_, lean_object* v_sz_5176_, lean_object* v_i_5177_, lean_object* v_b_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_){
_start:
{
size_t v_sz_boxed_5189_; size_t v_i_boxed_5190_; lean_object* v_res_5191_; 
v_sz_boxed_5189_ = lean_unbox_usize(v_sz_5176_);
lean_dec(v_sz_5176_);
v_i_boxed_5190_ = lean_unbox_usize(v_i_5177_);
lean_dec(v_i_5177_);
v_res_5191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5175_, v_sz_boxed_5189_, v_i_boxed_5190_, v_b_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
lean_dec(v___y_5183_);
lean_dec_ref(v___y_5182_);
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
lean_dec(v___y_5179_);
lean_dec_ref(v_as_5175_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5192_, size_t v_sz_5193_, size_t v_i_5194_, lean_object* v_b_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_){
_start:
{
uint8_t v___x_5206_; 
v___x_5206_ = lean_usize_dec_lt(v_i_5194_, v_sz_5193_);
if (v___x_5206_ == 0)
{
lean_object* v___x_5207_; 
v___x_5207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5207_, 0, v_b_5195_);
return v___x_5207_;
}
else
{
lean_object* v_snd_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5234_; 
v_snd_5208_ = lean_ctor_get(v_b_5195_, 1);
v_isSharedCheck_5234_ = !lean_is_exclusive(v_b_5195_);
if (v_isSharedCheck_5234_ == 0)
{
lean_object* v_unused_5235_; 
v_unused_5235_ = lean_ctor_get(v_b_5195_, 0);
lean_dec(v_unused_5235_);
v___x_5210_ = v_b_5195_;
v_isShared_5211_ = v_isSharedCheck_5234_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_snd_5208_);
lean_dec(v_b_5195_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5234_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v___x_5212_; lean_object* v_a_5214_; lean_object* v_a_5221_; lean_object* v___x_5222_; 
v___x_5212_ = lean_box(0);
v_a_5221_ = lean_array_uget_borrowed(v_as_5192_, v_i_5194_);
lean_inc(v_a_5221_);
v___x_5222_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5221_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
if (lean_obj_tag(v___x_5222_) == 0)
{
lean_object* v_a_5223_; uint8_t v___x_5224_; 
v_a_5223_ = lean_ctor_get(v___x_5222_, 0);
lean_inc(v_a_5223_);
lean_dec_ref_known(v___x_5222_, 1);
v___x_5224_ = lean_unbox(v_a_5223_);
lean_dec(v_a_5223_);
if (v___x_5224_ == 0)
{
v_a_5214_ = v_snd_5208_;
goto v___jp_5213_;
}
else
{
lean_object* v___x_5225_; 
lean_inc(v_a_5221_);
v___x_5225_ = l_Lean_PersistentArray_push___redArg(v_snd_5208_, v_a_5221_);
v_a_5214_ = v___x_5225_;
goto v___jp_5213_;
}
}
else
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5233_; 
lean_del_object(v___x_5210_);
lean_dec(v_snd_5208_);
v_a_5226_ = lean_ctor_get(v___x_5222_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5222_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5228_ = v___x_5222_;
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___x_5222_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5231_; 
if (v_isShared_5229_ == 0)
{
v___x_5231_ = v___x_5228_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
v___x_5231_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
return v___x_5231_;
}
}
}
v___jp_5213_:
{
lean_object* v___x_5216_; 
if (v_isShared_5211_ == 0)
{
lean_ctor_set(v___x_5210_, 1, v_a_5214_);
lean_ctor_set(v___x_5210_, 0, v___x_5212_);
v___x_5216_ = v___x_5210_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5220_; 
v_reuseFailAlloc_5220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5220_, 0, v___x_5212_);
lean_ctor_set(v_reuseFailAlloc_5220_, 1, v_a_5214_);
v___x_5216_ = v_reuseFailAlloc_5220_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
size_t v___x_5217_; size_t v___x_5218_; 
v___x_5217_ = ((size_t)1ULL);
v___x_5218_ = lean_usize_add(v_i_5194_, v___x_5217_);
v_i_5194_ = v___x_5218_;
v_b_5195_ = v___x_5216_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5236_, lean_object* v_sz_5237_, lean_object* v_i_5238_, lean_object* v_b_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_){
_start:
{
size_t v_sz_boxed_5250_; size_t v_i_boxed_5251_; lean_object* v_res_5252_; 
v_sz_boxed_5250_ = lean_unbox_usize(v_sz_5237_);
lean_dec(v_sz_5237_);
v_i_boxed_5251_ = lean_unbox_usize(v_i_5238_);
lean_dec(v_i_5238_);
v_res_5252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5236_, v_sz_boxed_5250_, v_i_boxed_5251_, v_b_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v___y_5246_);
lean_dec_ref(v___y_5245_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
lean_dec(v___y_5240_);
lean_dec_ref(v_as_5236_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5253_, size_t v_sz_5254_, size_t v_i_5255_, lean_object* v_b_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_){
_start:
{
uint8_t v___x_5267_; 
v___x_5267_ = lean_usize_dec_lt(v_i_5255_, v_sz_5254_);
if (v___x_5267_ == 0)
{
lean_object* v___x_5268_; 
v___x_5268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5268_, 0, v_b_5256_);
return v___x_5268_;
}
else
{
lean_object* v_snd_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5295_; 
v_snd_5269_ = lean_ctor_get(v_b_5256_, 1);
v_isSharedCheck_5295_ = !lean_is_exclusive(v_b_5256_);
if (v_isSharedCheck_5295_ == 0)
{
lean_object* v_unused_5296_; 
v_unused_5296_ = lean_ctor_get(v_b_5256_, 0);
lean_dec(v_unused_5296_);
v___x_5271_ = v_b_5256_;
v_isShared_5272_ = v_isSharedCheck_5295_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_snd_5269_);
lean_dec(v_b_5256_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5295_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5273_; lean_object* v_a_5275_; lean_object* v_a_5282_; lean_object* v___x_5283_; 
v___x_5273_ = lean_box(0);
v_a_5282_ = lean_array_uget_borrowed(v_as_5253_, v_i_5255_);
lean_inc(v_a_5282_);
v___x_5283_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5282_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_);
if (lean_obj_tag(v___x_5283_) == 0)
{
lean_object* v_a_5284_; uint8_t v___x_5285_; 
v_a_5284_ = lean_ctor_get(v___x_5283_, 0);
lean_inc(v_a_5284_);
lean_dec_ref_known(v___x_5283_, 1);
v___x_5285_ = lean_unbox(v_a_5284_);
lean_dec(v_a_5284_);
if (v___x_5285_ == 0)
{
v_a_5275_ = v_snd_5269_;
goto v___jp_5274_;
}
else
{
lean_object* v___x_5286_; 
lean_inc(v_a_5282_);
v___x_5286_ = l_Lean_PersistentArray_push___redArg(v_snd_5269_, v_a_5282_);
v_a_5275_ = v___x_5286_;
goto v___jp_5274_;
}
}
else
{
lean_object* v_a_5287_; lean_object* v___x_5289_; uint8_t v_isShared_5290_; uint8_t v_isSharedCheck_5294_; 
lean_del_object(v___x_5271_);
lean_dec(v_snd_5269_);
v_a_5287_ = lean_ctor_get(v___x_5283_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5289_ = v___x_5283_;
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
else
{
lean_inc(v_a_5287_);
lean_dec(v___x_5283_);
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
v___jp_5274_:
{
lean_object* v___x_5277_; 
if (v_isShared_5272_ == 0)
{
lean_ctor_set(v___x_5271_, 1, v_a_5275_);
lean_ctor_set(v___x_5271_, 0, v___x_5273_);
v___x_5277_ = v___x_5271_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v___x_5273_);
lean_ctor_set(v_reuseFailAlloc_5281_, 1, v_a_5275_);
v___x_5277_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
size_t v___x_5278_; size_t v___x_5279_; lean_object* v___x_5280_; 
v___x_5278_ = ((size_t)1ULL);
v___x_5279_ = lean_usize_add(v_i_5255_, v___x_5278_);
v___x_5280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5253_, v_sz_5254_, v___x_5279_, v___x_5277_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_);
return v___x_5280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5297_, lean_object* v_sz_5298_, lean_object* v_i_5299_, lean_object* v_b_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_){
_start:
{
size_t v_sz_boxed_5311_; size_t v_i_boxed_5312_; lean_object* v_res_5313_; 
v_sz_boxed_5311_ = lean_unbox_usize(v_sz_5298_);
lean_dec(v_sz_5298_);
v_i_boxed_5312_ = lean_unbox_usize(v_i_5299_);
lean_dec(v_i_5299_);
v_res_5313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5297_, v_sz_boxed_5311_, v_i_boxed_5312_, v_b_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_);
lean_dec(v___y_5309_);
lean_dec_ref(v___y_5308_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v_as_5297_);
return v_res_5313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5314_, lean_object* v_n_5315_, lean_object* v_b_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_){
_start:
{
if (lean_obj_tag(v_n_5315_) == 0)
{
lean_object* v_cs_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; size_t v_sz_5330_; size_t v___x_5331_; lean_object* v___x_5332_; 
v_cs_5327_ = lean_ctor_get(v_n_5315_, 0);
v___x_5328_ = lean_box(0);
v___x_5329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5329_, 0, v___x_5328_);
lean_ctor_set(v___x_5329_, 1, v_b_5316_);
v_sz_5330_ = lean_array_size(v_cs_5327_);
v___x_5331_ = ((size_t)0ULL);
v___x_5332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5314_, v_cs_5327_, v_sz_5330_, v___x_5331_, v___x_5329_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_);
if (lean_obj_tag(v___x_5332_) == 0)
{
lean_object* v_a_5333_; lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5347_; 
v_a_5333_ = lean_ctor_get(v___x_5332_, 0);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5332_);
if (v_isSharedCheck_5347_ == 0)
{
v___x_5335_ = v___x_5332_;
v_isShared_5336_ = v_isSharedCheck_5347_;
goto v_resetjp_5334_;
}
else
{
lean_inc(v_a_5333_);
lean_dec(v___x_5332_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5347_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v_fst_5337_; 
v_fst_5337_ = lean_ctor_get(v_a_5333_, 0);
if (lean_obj_tag(v_fst_5337_) == 0)
{
lean_object* v_snd_5338_; lean_object* v___x_5339_; lean_object* v___x_5341_; 
v_snd_5338_ = lean_ctor_get(v_a_5333_, 1);
lean_inc(v_snd_5338_);
lean_dec(v_a_5333_);
v___x_5339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5339_, 0, v_snd_5338_);
if (v_isShared_5336_ == 0)
{
lean_ctor_set(v___x_5335_, 0, v___x_5339_);
v___x_5341_ = v___x_5335_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v___x_5339_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
return v___x_5341_;
}
}
else
{
lean_object* v_val_5343_; lean_object* v___x_5345_; 
lean_inc_ref(v_fst_5337_);
lean_dec(v_a_5333_);
v_val_5343_ = lean_ctor_get(v_fst_5337_, 0);
lean_inc(v_val_5343_);
lean_dec_ref_known(v_fst_5337_, 1);
if (v_isShared_5336_ == 0)
{
lean_ctor_set(v___x_5335_, 0, v_val_5343_);
v___x_5345_ = v___x_5335_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_val_5343_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
}
}
else
{
lean_object* v_a_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5355_; 
v_a_5348_ = lean_ctor_get(v___x_5332_, 0);
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5332_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5350_ = v___x_5332_;
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_a_5348_);
lean_dec(v___x_5332_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v___x_5353_; 
if (v_isShared_5351_ == 0)
{
v___x_5353_ = v___x_5350_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v_a_5348_);
v___x_5353_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
return v___x_5353_;
}
}
}
}
else
{
lean_object* v_vs_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; size_t v_sz_5359_; size_t v___x_5360_; lean_object* v___x_5361_; 
v_vs_5356_ = lean_ctor_get(v_n_5315_, 0);
v___x_5357_ = lean_box(0);
v___x_5358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5358_, 0, v___x_5357_);
lean_ctor_set(v___x_5358_, 1, v_b_5316_);
v_sz_5359_ = lean_array_size(v_vs_5356_);
v___x_5360_ = ((size_t)0ULL);
v___x_5361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5356_, v_sz_5359_, v___x_5360_, v___x_5358_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_);
if (lean_obj_tag(v___x_5361_) == 0)
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5376_; 
v_a_5362_ = lean_ctor_get(v___x_5361_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5361_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5364_ = v___x_5361_;
v_isShared_5365_ = v_isSharedCheck_5376_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___x_5361_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5376_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v_fst_5366_; 
v_fst_5366_ = lean_ctor_get(v_a_5362_, 0);
if (lean_obj_tag(v_fst_5366_) == 0)
{
lean_object* v_snd_5367_; lean_object* v___x_5368_; lean_object* v___x_5370_; 
v_snd_5367_ = lean_ctor_get(v_a_5362_, 1);
lean_inc(v_snd_5367_);
lean_dec(v_a_5362_);
v___x_5368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5368_, 0, v_snd_5367_);
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
else
{
lean_object* v_val_5372_; lean_object* v___x_5374_; 
lean_inc_ref(v_fst_5366_);
lean_dec(v_a_5362_);
v_val_5372_ = lean_ctor_get(v_fst_5366_, 0);
lean_inc(v_val_5372_);
lean_dec_ref_known(v_fst_5366_, 1);
if (v_isShared_5365_ == 0)
{
lean_ctor_set(v___x_5364_, 0, v_val_5372_);
v___x_5374_ = v___x_5364_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_val_5372_);
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
else
{
lean_object* v_a_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5384_; 
v_a_5377_ = lean_ctor_get(v___x_5361_, 0);
v_isSharedCheck_5384_ = !lean_is_exclusive(v___x_5361_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5379_ = v___x_5361_;
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_a_5377_);
lean_dec(v___x_5361_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5382_; 
if (v_isShared_5380_ == 0)
{
v___x_5382_ = v___x_5379_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5377_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5385_, lean_object* v_as_5386_, size_t v_sz_5387_, size_t v_i_5388_, lean_object* v_b_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_){
_start:
{
uint8_t v___x_5400_; 
v___x_5400_ = lean_usize_dec_lt(v_i_5388_, v_sz_5387_);
if (v___x_5400_ == 0)
{
lean_object* v___x_5401_; 
v___x_5401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5401_, 0, v_b_5389_);
return v___x_5401_;
}
else
{
lean_object* v_snd_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5436_; 
v_snd_5402_ = lean_ctor_get(v_b_5389_, 1);
v_isSharedCheck_5436_ = !lean_is_exclusive(v_b_5389_);
if (v_isSharedCheck_5436_ == 0)
{
lean_object* v_unused_5437_; 
v_unused_5437_ = lean_ctor_get(v_b_5389_, 0);
lean_dec(v_unused_5437_);
v___x_5404_ = v_b_5389_;
v_isShared_5405_ = v_isSharedCheck_5436_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_snd_5402_);
lean_dec(v_b_5389_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5436_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5406_; lean_object* v_a_5407_; lean_object* v___x_5408_; 
v___x_5406_ = lean_box(0);
v_a_5407_ = lean_array_uget_borrowed(v_as_5386_, v_i_5388_);
lean_inc(v_snd_5402_);
v___x_5408_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5385_, v_a_5407_, v_snd_5402_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_);
if (lean_obj_tag(v___x_5408_) == 0)
{
lean_object* v_a_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5427_; 
v_a_5409_ = lean_ctor_get(v___x_5408_, 0);
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5411_ = v___x_5408_;
v_isShared_5412_ = v_isSharedCheck_5427_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_a_5409_);
lean_dec(v___x_5408_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5427_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
if (lean_obj_tag(v_a_5409_) == 0)
{
lean_object* v___x_5413_; lean_object* v___x_5415_; 
v___x_5413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5413_, 0, v_a_5409_);
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 0, v___x_5413_);
v___x_5415_ = v___x_5404_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v___x_5413_);
lean_ctor_set(v_reuseFailAlloc_5419_, 1, v_snd_5402_);
v___x_5415_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
lean_object* v___x_5417_; 
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 0, v___x_5415_);
v___x_5417_ = v___x_5411_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v___x_5415_);
v___x_5417_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
return v___x_5417_;
}
}
}
else
{
lean_object* v_a_5420_; lean_object* v___x_5422_; 
lean_del_object(v___x_5411_);
lean_dec(v_snd_5402_);
v_a_5420_ = lean_ctor_get(v_a_5409_, 0);
lean_inc(v_a_5420_);
lean_dec_ref_known(v_a_5409_, 1);
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 1, v_a_5420_);
lean_ctor_set(v___x_5404_, 0, v___x_5406_);
v___x_5422_ = v___x_5404_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v___x_5406_);
lean_ctor_set(v_reuseFailAlloc_5426_, 1, v_a_5420_);
v___x_5422_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
size_t v___x_5423_; size_t v___x_5424_; 
v___x_5423_ = ((size_t)1ULL);
v___x_5424_ = lean_usize_add(v_i_5388_, v___x_5423_);
v_i_5388_ = v___x_5424_;
v_b_5389_ = v___x_5422_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5435_; 
lean_del_object(v___x_5404_);
lean_dec(v_snd_5402_);
v_a_5428_ = lean_ctor_get(v___x_5408_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5430_ = v___x_5408_;
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_a_5428_);
lean_dec(v___x_5408_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___x_5433_; 
if (v_isShared_5431_ == 0)
{
v___x_5433_ = v___x_5430_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_a_5428_);
v___x_5433_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
return v___x_5433_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5438_, lean_object* v_as_5439_, lean_object* v_sz_5440_, lean_object* v_i_5441_, lean_object* v_b_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_){
_start:
{
size_t v_sz_boxed_5453_; size_t v_i_boxed_5454_; lean_object* v_res_5455_; 
v_sz_boxed_5453_ = lean_unbox_usize(v_sz_5440_);
lean_dec(v_sz_5440_);
v_i_boxed_5454_ = lean_unbox_usize(v_i_5441_);
lean_dec(v_i_5441_);
v_res_5455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5438_, v_as_5439_, v_sz_boxed_5453_, v_i_boxed_5454_, v_b_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_);
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5450_);
lean_dec(v___y_5449_);
lean_dec_ref(v___y_5448_);
lean_dec(v___y_5447_);
lean_dec_ref(v___y_5446_);
lean_dec(v___y_5445_);
lean_dec_ref(v___y_5444_);
lean_dec(v___y_5443_);
lean_dec_ref(v_as_5439_);
lean_dec_ref(v_init_5438_);
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5456_, lean_object* v_n_5457_, lean_object* v_b_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_){
_start:
{
lean_object* v_res_5469_; 
v_res_5469_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5456_, v_n_5457_, v_b_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_);
lean_dec(v___y_5467_);
lean_dec_ref(v___y_5466_);
lean_dec(v___y_5465_);
lean_dec_ref(v___y_5464_);
lean_dec(v___y_5463_);
lean_dec_ref(v___y_5462_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
lean_dec(v___y_5459_);
lean_dec_ref(v_n_5457_);
lean_dec_ref(v_init_5456_);
return v_res_5469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5470_, lean_object* v_init_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_){
_start:
{
lean_object* v_root_5482_; lean_object* v_tail_5483_; lean_object* v___x_5484_; 
v_root_5482_ = lean_ctor_get(v_t_5470_, 0);
v_tail_5483_ = lean_ctor_get(v_t_5470_, 1);
lean_inc_ref(v_init_5471_);
v___x_5484_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5471_, v_root_5482_, v_init_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_);
lean_dec_ref(v_init_5471_);
if (lean_obj_tag(v___x_5484_) == 0)
{
lean_object* v_a_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5521_; 
v_a_5485_ = lean_ctor_get(v___x_5484_, 0);
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5484_);
if (v_isSharedCheck_5521_ == 0)
{
v___x_5487_ = v___x_5484_;
v_isShared_5488_ = v_isSharedCheck_5521_;
goto v_resetjp_5486_;
}
else
{
lean_inc(v_a_5485_);
lean_dec(v___x_5484_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5521_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
if (lean_obj_tag(v_a_5485_) == 0)
{
lean_object* v_a_5489_; lean_object* v___x_5491_; 
v_a_5489_ = lean_ctor_get(v_a_5485_, 0);
lean_inc(v_a_5489_);
lean_dec_ref_known(v_a_5485_, 1);
if (v_isShared_5488_ == 0)
{
lean_ctor_set(v___x_5487_, 0, v_a_5489_);
v___x_5491_ = v___x_5487_;
goto v_reusejp_5490_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_a_5489_);
v___x_5491_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5490_;
}
v_reusejp_5490_:
{
return v___x_5491_;
}
}
else
{
lean_object* v_a_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; size_t v_sz_5496_; size_t v___x_5497_; lean_object* v___x_5498_; 
lean_del_object(v___x_5487_);
v_a_5493_ = lean_ctor_get(v_a_5485_, 0);
lean_inc(v_a_5493_);
lean_dec_ref_known(v_a_5485_, 1);
v___x_5494_ = lean_box(0);
v___x_5495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5495_, 0, v___x_5494_);
lean_ctor_set(v___x_5495_, 1, v_a_5493_);
v_sz_5496_ = lean_array_size(v_tail_5483_);
v___x_5497_ = ((size_t)0ULL);
v___x_5498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5483_, v_sz_5496_, v___x_5497_, v___x_5495_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_);
if (lean_obj_tag(v___x_5498_) == 0)
{
lean_object* v_a_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5512_; 
v_a_5499_ = lean_ctor_get(v___x_5498_, 0);
v_isSharedCheck_5512_ = !lean_is_exclusive(v___x_5498_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5501_ = v___x_5498_;
v_isShared_5502_ = v_isSharedCheck_5512_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_a_5499_);
lean_dec(v___x_5498_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5512_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v_fst_5503_; 
v_fst_5503_ = lean_ctor_get(v_a_5499_, 0);
if (lean_obj_tag(v_fst_5503_) == 0)
{
lean_object* v_snd_5504_; lean_object* v___x_5506_; 
v_snd_5504_ = lean_ctor_get(v_a_5499_, 1);
lean_inc(v_snd_5504_);
lean_dec(v_a_5499_);
if (v_isShared_5502_ == 0)
{
lean_ctor_set(v___x_5501_, 0, v_snd_5504_);
v___x_5506_ = v___x_5501_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5507_; 
v_reuseFailAlloc_5507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5507_, 0, v_snd_5504_);
v___x_5506_ = v_reuseFailAlloc_5507_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
return v___x_5506_;
}
}
else
{
lean_object* v_val_5508_; lean_object* v___x_5510_; 
lean_inc_ref(v_fst_5503_);
lean_dec(v_a_5499_);
v_val_5508_ = lean_ctor_get(v_fst_5503_, 0);
lean_inc(v_val_5508_);
lean_dec_ref_known(v_fst_5503_, 1);
if (v_isShared_5502_ == 0)
{
lean_ctor_set(v___x_5501_, 0, v_val_5508_);
v___x_5510_ = v___x_5501_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v_val_5508_);
v___x_5510_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
return v___x_5510_;
}
}
}
}
else
{
lean_object* v_a_5513_; lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5520_; 
v_a_5513_ = lean_ctor_get(v___x_5498_, 0);
v_isSharedCheck_5520_ = !lean_is_exclusive(v___x_5498_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5515_ = v___x_5498_;
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
else
{
lean_inc(v_a_5513_);
lean_dec(v___x_5498_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
lean_object* v___x_5518_; 
if (v_isShared_5516_ == 0)
{
v___x_5518_ = v___x_5515_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5513_);
v___x_5518_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
return v___x_5518_;
}
}
}
}
}
}
else
{
lean_object* v_a_5522_; lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5529_; 
v_a_5522_ = lean_ctor_get(v___x_5484_, 0);
v_isSharedCheck_5529_ = !lean_is_exclusive(v___x_5484_);
if (v_isSharedCheck_5529_ == 0)
{
v___x_5524_ = v___x_5484_;
v_isShared_5525_ = v_isSharedCheck_5529_;
goto v_resetjp_5523_;
}
else
{
lean_inc(v_a_5522_);
lean_dec(v___x_5484_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5529_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v___x_5527_; 
if (v_isShared_5525_ == 0)
{
v___x_5527_ = v___x_5524_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_a_5522_);
v___x_5527_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
return v___x_5527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5530_, lean_object* v_init_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_){
_start:
{
lean_object* v_res_5542_; 
v_res_5542_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5530_, v_init_5531_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_, v___y_5540_);
lean_dec(v___y_5540_);
lean_dec_ref(v___y_5539_);
lean_dec(v___y_5538_);
lean_dec_ref(v___y_5537_);
lean_dec(v___y_5536_);
lean_dec_ref(v___y_5535_);
lean_dec(v___y_5534_);
lean_dec_ref(v___y_5533_);
lean_dec(v___y_5532_);
lean_dec_ref(v_t_5530_);
return v_res_5542_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; 
v___x_5543_ = lean_unsigned_to_nat(32u);
v___x_5544_ = lean_mk_empty_array_with_capacity(v___x_5543_);
v___x_5545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5545_, 0, v___x_5544_);
return v___x_5545_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v_result_5551_; 
v___x_5546_ = ((size_t)5ULL);
v___x_5547_ = lean_unsigned_to_nat(0u);
v___x_5548_ = lean_unsigned_to_nat(32u);
v___x_5549_ = lean_mk_empty_array_with_capacity(v___x_5548_);
v___x_5550_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5551_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5551_, 0, v___x_5550_);
lean_ctor_set(v_result_5551_, 1, v___x_5549_);
lean_ctor_set(v_result_5551_, 2, v___x_5547_);
lean_ctor_set(v_result_5551_, 3, v___x_5547_);
lean_ctor_set_usize(v_result_5551_, 4, v___x_5546_);
return v_result_5551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5552_, lean_object* v_a_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_){
_start:
{
lean_object* v_result_5563_; lean_object* v___x_5564_; 
v_result_5563_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5564_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5552_, v_result_5563_, v_a_5553_, v_a_5554_, v_a_5555_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_, v_a_5561_);
return v___x_5564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_){
_start:
{
lean_object* v_res_5576_; 
v_res_5576_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_, v_a_5574_);
lean_dec(v_a_5574_);
lean_dec_ref(v_a_5573_);
lean_dec(v_a_5572_);
lean_dec_ref(v_a_5571_);
lean_dec(v_a_5570_);
lean_dec_ref(v_a_5569_);
lean_dec(v_a_5568_);
lean_dec_ref(v_a_5567_);
lean_dec(v_a_5566_);
lean_dec_ref(v_thms_5565_);
return v_res_5576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_5579_, lean_object* v_newThms_5580_, lean_object* v_gmt_5581_, lean_object* v_numInstances_5582_, lean_object* v_numDelayedInstances_5583_, lean_object* v_num_5584_, lean_object* v_preInstances_5585_, lean_object* v_nextThmIdx_5586_, lean_object* v_matchEqNames_5587_, lean_object* v_delayedThmInsts_5588_, lean_object* v_nextDeclIdx_5589_, lean_object* v_enodeMap_5590_, lean_object* v_exprs_5591_, lean_object* v_parents_5592_, lean_object* v_congrTable_5593_, lean_object* v_appMap_5594_, lean_object* v_indicesFound_5595_, lean_object* v_toProcess_5596_, uint8_t v_inconsistent_5597_, lean_object* v_nextIdx_5598_, lean_object* v_newRawFacts_5599_, lean_object* v_facts_5600_, lean_object* v_extThms_5601_, lean_object* v_inj_5602_, lean_object* v_split_5603_, lean_object* v_clean_5604_, lean_object* v_sstates_5605_, lean_object* v_mvarId_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_){
_start:
{
lean_object* v___x_5617_; 
v___x_5617_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5579_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_);
if (lean_obj_tag(v___x_5617_) == 0)
{
lean_object* v_a_5618_; lean_object* v___x_5619_; 
v_a_5618_ = lean_ctor_get(v___x_5617_, 0);
lean_inc(v_a_5618_);
lean_dec_ref_known(v___x_5617_, 1);
v___x_5619_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_5580_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_);
if (lean_obj_tag(v___x_5619_) == 0)
{
lean_object* v_a_5620_; lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5631_; 
v_a_5620_ = lean_ctor_get(v___x_5619_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5619_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5622_ = v___x_5619_;
v_isShared_5623_ = v_isSharedCheck_5631_;
goto v_resetjp_5621_;
}
else
{
lean_inc(v_a_5620_);
lean_dec(v___x_5619_);
v___x_5622_ = lean_box(0);
v_isShared_5623_ = v_isSharedCheck_5631_;
goto v_resetjp_5621_;
}
v_resetjp_5621_:
{
lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5629_; 
v___x_5624_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_5625_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5625_, 0, v___x_5624_);
lean_ctor_set(v___x_5625_, 1, v_gmt_5581_);
lean_ctor_set(v___x_5625_, 2, v_a_5618_);
lean_ctor_set(v___x_5625_, 3, v_a_5620_);
lean_ctor_set(v___x_5625_, 4, v_numInstances_5582_);
lean_ctor_set(v___x_5625_, 5, v_numDelayedInstances_5583_);
lean_ctor_set(v___x_5625_, 6, v_num_5584_);
lean_ctor_set(v___x_5625_, 7, v_preInstances_5585_);
lean_ctor_set(v___x_5625_, 8, v_nextThmIdx_5586_);
lean_ctor_set(v___x_5625_, 9, v_matchEqNames_5587_);
lean_ctor_set(v___x_5625_, 10, v_delayedThmInsts_5588_);
v___x_5626_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_5626_, 0, v_nextDeclIdx_5589_);
lean_ctor_set(v___x_5626_, 1, v_enodeMap_5590_);
lean_ctor_set(v___x_5626_, 2, v_exprs_5591_);
lean_ctor_set(v___x_5626_, 3, v_parents_5592_);
lean_ctor_set(v___x_5626_, 4, v_congrTable_5593_);
lean_ctor_set(v___x_5626_, 5, v_appMap_5594_);
lean_ctor_set(v___x_5626_, 6, v_indicesFound_5595_);
lean_ctor_set(v___x_5626_, 7, v_toProcess_5596_);
lean_ctor_set(v___x_5626_, 8, v_nextIdx_5598_);
lean_ctor_set(v___x_5626_, 9, v_newRawFacts_5599_);
lean_ctor_set(v___x_5626_, 10, v_facts_5600_);
lean_ctor_set(v___x_5626_, 11, v_extThms_5601_);
lean_ctor_set(v___x_5626_, 12, v___x_5625_);
lean_ctor_set(v___x_5626_, 13, v_inj_5602_);
lean_ctor_set(v___x_5626_, 14, v_split_5603_);
lean_ctor_set(v___x_5626_, 15, v_clean_5604_);
lean_ctor_set(v___x_5626_, 16, v_sstates_5605_);
lean_ctor_set_uint8(v___x_5626_, sizeof(void*)*17, v_inconsistent_5597_);
v___x_5627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5627_, 0, v___x_5626_);
lean_ctor_set(v___x_5627_, 1, v_mvarId_5606_);
if (v_isShared_5623_ == 0)
{
lean_ctor_set(v___x_5622_, 0, v___x_5627_);
v___x_5629_ = v___x_5622_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v___x_5627_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
else
{
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
lean_dec(v_a_5618_);
lean_dec(v_mvarId_5606_);
lean_dec_ref(v_sstates_5605_);
lean_dec_ref(v_clean_5604_);
lean_dec_ref(v_split_5603_);
lean_dec_ref(v_inj_5602_);
lean_dec_ref(v_extThms_5601_);
lean_dec_ref(v_facts_5600_);
lean_dec_ref(v_newRawFacts_5599_);
lean_dec(v_nextIdx_5598_);
lean_dec_ref(v_toProcess_5596_);
lean_dec_ref(v_indicesFound_5595_);
lean_dec_ref(v_appMap_5594_);
lean_dec_ref(v_congrTable_5593_);
lean_dec_ref(v_parents_5592_);
lean_dec_ref(v_exprs_5591_);
lean_dec_ref(v_enodeMap_5590_);
lean_dec(v_nextDeclIdx_5589_);
lean_dec_ref(v_delayedThmInsts_5588_);
lean_dec_ref(v_matchEqNames_5587_);
lean_dec(v_nextThmIdx_5586_);
lean_dec_ref(v_preInstances_5585_);
lean_dec(v_num_5584_);
lean_dec(v_numDelayedInstances_5583_);
lean_dec(v_numInstances_5582_);
lean_dec(v_gmt_5581_);
v_a_5632_ = lean_ctor_get(v___x_5619_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5619_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5619_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5619_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5637_; 
if (v_isShared_5635_ == 0)
{
v___x_5637_ = v___x_5634_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_a_5632_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
}
else
{
lean_object* v_a_5640_; lean_object* v___x_5642_; uint8_t v_isShared_5643_; uint8_t v_isSharedCheck_5647_; 
lean_dec(v_mvarId_5606_);
lean_dec_ref(v_sstates_5605_);
lean_dec_ref(v_clean_5604_);
lean_dec_ref(v_split_5603_);
lean_dec_ref(v_inj_5602_);
lean_dec_ref(v_extThms_5601_);
lean_dec_ref(v_facts_5600_);
lean_dec_ref(v_newRawFacts_5599_);
lean_dec(v_nextIdx_5598_);
lean_dec_ref(v_toProcess_5596_);
lean_dec_ref(v_indicesFound_5595_);
lean_dec_ref(v_appMap_5594_);
lean_dec_ref(v_congrTable_5593_);
lean_dec_ref(v_parents_5592_);
lean_dec_ref(v_exprs_5591_);
lean_dec_ref(v_enodeMap_5590_);
lean_dec(v_nextDeclIdx_5589_);
lean_dec_ref(v_delayedThmInsts_5588_);
lean_dec_ref(v_matchEqNames_5587_);
lean_dec(v_nextThmIdx_5586_);
lean_dec_ref(v_preInstances_5585_);
lean_dec(v_num_5584_);
lean_dec(v_numDelayedInstances_5583_);
lean_dec(v_numInstances_5582_);
lean_dec(v_gmt_5581_);
v_a_5640_ = lean_ctor_get(v___x_5617_, 0);
v_isSharedCheck_5647_ = !lean_is_exclusive(v___x_5617_);
if (v_isSharedCheck_5647_ == 0)
{
v___x_5642_ = v___x_5617_;
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
else
{
lean_inc(v_a_5640_);
lean_dec(v___x_5617_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_5648_ = _args[0];
lean_object* v_newThms_5649_ = _args[1];
lean_object* v_gmt_5650_ = _args[2];
lean_object* v_numInstances_5651_ = _args[3];
lean_object* v_numDelayedInstances_5652_ = _args[4];
lean_object* v_num_5653_ = _args[5];
lean_object* v_preInstances_5654_ = _args[6];
lean_object* v_nextThmIdx_5655_ = _args[7];
lean_object* v_matchEqNames_5656_ = _args[8];
lean_object* v_delayedThmInsts_5657_ = _args[9];
lean_object* v_nextDeclIdx_5658_ = _args[10];
lean_object* v_enodeMap_5659_ = _args[11];
lean_object* v_exprs_5660_ = _args[12];
lean_object* v_parents_5661_ = _args[13];
lean_object* v_congrTable_5662_ = _args[14];
lean_object* v_appMap_5663_ = _args[15];
lean_object* v_indicesFound_5664_ = _args[16];
lean_object* v_toProcess_5665_ = _args[17];
lean_object* v_inconsistent_5666_ = _args[18];
lean_object* v_nextIdx_5667_ = _args[19];
lean_object* v_newRawFacts_5668_ = _args[20];
lean_object* v_facts_5669_ = _args[21];
lean_object* v_extThms_5670_ = _args[22];
lean_object* v_inj_5671_ = _args[23];
lean_object* v_split_5672_ = _args[24];
lean_object* v_clean_5673_ = _args[25];
lean_object* v_sstates_5674_ = _args[26];
lean_object* v_mvarId_5675_ = _args[27];
lean_object* v___y_5676_ = _args[28];
lean_object* v___y_5677_ = _args[29];
lean_object* v___y_5678_ = _args[30];
lean_object* v___y_5679_ = _args[31];
lean_object* v___y_5680_ = _args[32];
lean_object* v___y_5681_ = _args[33];
lean_object* v___y_5682_ = _args[34];
lean_object* v___y_5683_ = _args[35];
lean_object* v___y_5684_ = _args[36];
lean_object* v___y_5685_ = _args[37];
_start:
{
uint8_t v_inconsistent_boxed_5686_; lean_object* v_res_5687_; 
v_inconsistent_boxed_5686_ = lean_unbox(v_inconsistent_5666_);
v_res_5687_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_5648_, v_newThms_5649_, v_gmt_5650_, v_numInstances_5651_, v_numDelayedInstances_5652_, v_num_5653_, v_preInstances_5654_, v_nextThmIdx_5655_, v_matchEqNames_5656_, v_delayedThmInsts_5657_, v_nextDeclIdx_5658_, v_enodeMap_5659_, v_exprs_5660_, v_parents_5661_, v_congrTable_5662_, v_appMap_5663_, v_indicesFound_5664_, v_toProcess_5665_, v_inconsistent_boxed_5686_, v_nextIdx_5667_, v_newRawFacts_5668_, v_facts_5669_, v_extThms_5670_, v_inj_5671_, v_split_5672_, v_clean_5673_, v_sstates_5674_, v_mvarId_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
lean_dec(v___y_5684_);
lean_dec_ref(v___y_5683_);
lean_dec(v___y_5682_);
lean_dec_ref(v___y_5681_);
lean_dec(v___y_5680_);
lean_dec_ref(v___y_5679_);
lean_dec(v___y_5678_);
lean_dec_ref(v___y_5677_);
lean_dec(v___y_5676_);
lean_dec_ref(v_newThms_5649_);
lean_dec_ref(v_thms_5648_);
return v_res_5687_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5688_; 
v___x_5688_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_5688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_5689_, size_t v_i_5690_, lean_object* v_bs_5691_){
_start:
{
uint8_t v___x_5692_; 
v___x_5692_ = lean_usize_dec_lt(v_i_5690_, v_sz_5689_);
if (v___x_5692_ == 0)
{
return v_bs_5691_;
}
else
{
lean_object* v_v_5693_; lean_object* v_casesTypes_5694_; lean_object* v_extThms_5695_; lean_object* v_funCC_5696_; lean_object* v_inj_5697_; lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_5711_; 
v_v_5693_ = lean_array_uget(v_bs_5691_, v_i_5690_);
v_casesTypes_5694_ = lean_ctor_get(v_v_5693_, 0);
v_extThms_5695_ = lean_ctor_get(v_v_5693_, 1);
v_funCC_5696_ = lean_ctor_get(v_v_5693_, 2);
v_inj_5697_ = lean_ctor_get(v_v_5693_, 4);
v_isSharedCheck_5711_ = !lean_is_exclusive(v_v_5693_);
if (v_isSharedCheck_5711_ == 0)
{
lean_object* v_unused_5712_; 
v_unused_5712_ = lean_ctor_get(v_v_5693_, 3);
lean_dec(v_unused_5712_);
v___x_5699_ = v_v_5693_;
v_isShared_5700_ = v_isSharedCheck_5711_;
goto v_resetjp_5698_;
}
else
{
lean_inc(v_inj_5697_);
lean_inc(v_funCC_5696_);
lean_inc(v_extThms_5695_);
lean_inc(v_casesTypes_5694_);
lean_dec(v_v_5693_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_5711_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
lean_object* v___x_5701_; lean_object* v_bs_x27_5702_; lean_object* v___x_5703_; lean_object* v___x_5705_; 
v___x_5701_ = lean_unsigned_to_nat(0u);
v_bs_x27_5702_ = lean_array_uset(v_bs_5691_, v_i_5690_, v___x_5701_);
v___x_5703_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_5700_ == 0)
{
lean_ctor_set(v___x_5699_, 3, v___x_5703_);
v___x_5705_ = v___x_5699_;
goto v_reusejp_5704_;
}
else
{
lean_object* v_reuseFailAlloc_5710_; 
v_reuseFailAlloc_5710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5710_, 0, v_casesTypes_5694_);
lean_ctor_set(v_reuseFailAlloc_5710_, 1, v_extThms_5695_);
lean_ctor_set(v_reuseFailAlloc_5710_, 2, v_funCC_5696_);
lean_ctor_set(v_reuseFailAlloc_5710_, 3, v___x_5703_);
lean_ctor_set(v_reuseFailAlloc_5710_, 4, v_inj_5697_);
v___x_5705_ = v_reuseFailAlloc_5710_;
goto v_reusejp_5704_;
}
v_reusejp_5704_:
{
size_t v___x_5706_; size_t v___x_5707_; lean_object* v___x_5708_; 
v___x_5706_ = ((size_t)1ULL);
v___x_5707_ = lean_usize_add(v_i_5690_, v___x_5706_);
v___x_5708_ = lean_array_uset(v_bs_x27_5702_, v_i_5690_, v___x_5705_);
v_i_5690_ = v___x_5707_;
v_bs_5691_ = v___x_5708_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_5713_, lean_object* v_i_5714_, lean_object* v_bs_5715_){
_start:
{
size_t v_sz_boxed_5716_; size_t v_i_boxed_5717_; lean_object* v_res_5718_; 
v_sz_boxed_5716_ = lean_unbox_usize(v_sz_5713_);
lean_dec(v_sz_5713_);
v_i_boxed_5717_ = lean_unbox_usize(v_i_5714_);
lean_dec(v_i_5714_);
v_res_5718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_5716_, v_i_boxed_5717_, v_bs_5715_);
return v_res_5718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_5719_, lean_object* v_ps_5720_, uint8_t v_only_5721_, lean_object* v_k_5722_, lean_object* v_a_5723_, lean_object* v_a_5724_, lean_object* v_a_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_){
_start:
{
lean_object* v___y_5733_; lean_object* v___y_5734_; lean_object* v___y_5735_; lean_object* v___y_5736_; lean_object* v___y_5737_; lean_object* v___y_5738_; lean_object* v___y_5739_; lean_object* v___y_5740_; lean_object* v___y_5741_; uint8_t v___y_5754_; uint8_t v___y_5755_; lean_object* v_params_5756_; lean_object* v___y_5757_; lean_object* v___y_5758_; lean_object* v___y_5759_; lean_object* v___y_5760_; lean_object* v___y_5761_; lean_object* v___y_5762_; lean_object* v___y_5763_; lean_object* v___y_5764_; uint8_t v___y_5867_; 
if (v_only_5721_ == 0)
{
lean_object* v___x_5889_; lean_object* v___x_5890_; uint8_t v___x_5891_; 
v___x_5889_ = lean_array_get_size(v_ps_5720_);
v___x_5890_ = lean_unsigned_to_nat(0u);
v___x_5891_ = lean_nat_dec_eq(v___x_5889_, v___x_5890_);
if (v___x_5891_ == 0)
{
v___y_5867_ = v___x_5891_;
goto v___jp_5866_;
}
else
{
lean_object* v___x_5892_; 
lean_dec_ref(v_params_5719_);
lean_inc(v_a_5730_);
lean_inc_ref(v_a_5729_);
lean_inc(v_a_5728_);
lean_inc_ref(v_a_5727_);
lean_inc(v_a_5726_);
lean_inc_ref(v_a_5725_);
lean_inc(v_a_5724_);
lean_inc_ref(v_a_5723_);
v___x_5892_ = lean_apply_9(v_k_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_, v_a_5728_, v_a_5729_, v_a_5730_, lean_box(0));
return v___x_5892_;
}
}
else
{
uint8_t v___x_5893_; 
v___x_5893_ = 0;
v___y_5867_ = v___x_5893_;
goto v___jp_5866_;
}
v___jp_5732_:
{
lean_object* v___x_5742_; lean_object* v___x_5743_; 
v___x_5742_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_5742_, 0, v___y_5733_);
v___x_5743_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_5742_, v___y_5734_, v___y_5735_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
if (lean_obj_tag(v___x_5743_) == 0)
{
lean_object* v___x_5744_; 
lean_dec_ref_known(v___x_5743_, 1);
lean_inc(v___y_5741_);
lean_inc_ref(v___y_5740_);
lean_inc(v___y_5739_);
lean_inc_ref(v___y_5738_);
lean_inc(v___y_5737_);
lean_inc_ref(v___y_5736_);
lean_inc(v___y_5735_);
v___x_5744_ = lean_apply_9(v_k_5722_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, lean_box(0));
return v___x_5744_;
}
else
{
lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5752_; 
lean_dec_ref(v___y_5734_);
lean_dec_ref(v_k_5722_);
v_a_5745_ = lean_ctor_get(v___x_5743_, 0);
v_isSharedCheck_5752_ = !lean_is_exclusive(v___x_5743_);
if (v_isSharedCheck_5752_ == 0)
{
v___x_5747_ = v___x_5743_;
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_dec(v___x_5743_);
v___x_5747_ = lean_box(0);
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
v_resetjp_5746_:
{
lean_object* v___x_5750_; 
if (v_isShared_5748_ == 0)
{
v___x_5750_ = v___x_5747_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_a_5745_);
v___x_5750_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
return v___x_5750_;
}
}
}
}
v___jp_5753_:
{
lean_object* v___x_5765_; 
v___x_5765_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5756_, v_ps_5720_, v_only_5721_, v___y_5755_, v___y_5754_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_);
if (lean_obj_tag(v___x_5765_) == 0)
{
lean_object* v_a_5766_; lean_object* v_ctx_5767_; lean_object* v_anchorRefs_x3f_5768_; lean_object* v_toContext_5769_; lean_object* v_sctx_5770_; lean_object* v_methods_5771_; uint8_t v_sym_5772_; lean_object* v_simp_5773_; lean_object* v_simpMethods_5774_; lean_object* v_symSimpMethods_5775_; lean_object* v_symDSimpMethods_5776_; lean_object* v_config_5777_; uint8_t v_cheapCases_5778_; uint8_t v_reportMVarIssue_5779_; lean_object* v_splitSource_5780_; lean_object* v_ematchDiagSource_5781_; lean_object* v_symPrios_5782_; lean_object* v_extensions_5783_; uint8_t v_debug_5784_; uint8_t v_ematchDiag_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; 
v_a_5766_ = lean_ctor_get(v___x_5765_, 0);
lean_inc_n(v_a_5766_, 2);
lean_dec_ref_known(v___x_5765_, 1);
v_ctx_5767_ = lean_ctor_get(v___y_5757_, 1);
v_anchorRefs_x3f_5768_ = lean_ctor_get(v_a_5766_, 8);
v_toContext_5769_ = lean_ctor_get(v___y_5757_, 0);
v_sctx_5770_ = lean_ctor_get(v___y_5757_, 2);
v_methods_5771_ = lean_ctor_get(v___y_5757_, 3);
v_sym_5772_ = lean_ctor_get_uint8(v___y_5757_, sizeof(void*)*5);
v_simp_5773_ = lean_ctor_get(v_ctx_5767_, 0);
v_simpMethods_5774_ = lean_ctor_get(v_ctx_5767_, 1);
v_symSimpMethods_5775_ = lean_ctor_get(v_ctx_5767_, 2);
v_symDSimpMethods_5776_ = lean_ctor_get(v_ctx_5767_, 3);
v_config_5777_ = lean_ctor_get(v_ctx_5767_, 4);
v_cheapCases_5778_ = lean_ctor_get_uint8(v_ctx_5767_, sizeof(void*)*10);
v_reportMVarIssue_5779_ = lean_ctor_get_uint8(v_ctx_5767_, sizeof(void*)*10 + 1);
v_splitSource_5780_ = lean_ctor_get(v_ctx_5767_, 6);
v_ematchDiagSource_5781_ = lean_ctor_get(v_ctx_5767_, 7);
v_symPrios_5782_ = lean_ctor_get(v_ctx_5767_, 8);
v_extensions_5783_ = lean_ctor_get(v_ctx_5767_, 9);
v_debug_5784_ = lean_ctor_get_uint8(v_ctx_5767_, sizeof(void*)*10 + 2);
v_ematchDiag_5785_ = lean_ctor_get_uint8(v_ctx_5767_, sizeof(void*)*10 + 3);
lean_inc_ref(v_extensions_5783_);
lean_inc_ref(v_symPrios_5782_);
lean_inc(v_ematchDiagSource_5781_);
lean_inc(v_splitSource_5780_);
lean_inc(v_anchorRefs_x3f_5768_);
lean_inc_ref(v_config_5777_);
lean_inc_ref(v_symDSimpMethods_5776_);
lean_inc_ref(v_symSimpMethods_5775_);
lean_inc_ref(v_simpMethods_5774_);
lean_inc_ref(v_simp_5773_);
v___x_5786_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_5786_, 0, v_simp_5773_);
lean_ctor_set(v___x_5786_, 1, v_simpMethods_5774_);
lean_ctor_set(v___x_5786_, 2, v_symSimpMethods_5775_);
lean_ctor_set(v___x_5786_, 3, v_symDSimpMethods_5776_);
lean_ctor_set(v___x_5786_, 4, v_config_5777_);
lean_ctor_set(v___x_5786_, 5, v_anchorRefs_x3f_5768_);
lean_ctor_set(v___x_5786_, 6, v_splitSource_5780_);
lean_ctor_set(v___x_5786_, 7, v_ematchDiagSource_5781_);
lean_ctor_set(v___x_5786_, 8, v_symPrios_5782_);
lean_ctor_set(v___x_5786_, 9, v_extensions_5783_);
lean_ctor_set_uint8(v___x_5786_, sizeof(void*)*10, v_cheapCases_5778_);
lean_ctor_set_uint8(v___x_5786_, sizeof(void*)*10 + 1, v_reportMVarIssue_5779_);
lean_ctor_set_uint8(v___x_5786_, sizeof(void*)*10 + 2, v_debug_5784_);
lean_ctor_set_uint8(v___x_5786_, sizeof(void*)*10 + 3, v_ematchDiag_5785_);
lean_inc_ref(v_methods_5771_);
lean_inc_ref(v_sctx_5770_);
lean_inc_ref(v_toContext_5769_);
v___x_5787_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_5787_, 0, v_toContext_5769_);
lean_ctor_set(v___x_5787_, 1, v___x_5786_);
lean_ctor_set(v___x_5787_, 2, v_sctx_5770_);
lean_ctor_set(v___x_5787_, 3, v_methods_5771_);
lean_ctor_set(v___x_5787_, 4, v_a_5766_);
lean_ctor_set_uint8(v___x_5787_, sizeof(void*)*5, v_sym_5772_);
if (v_only_5721_ == 0)
{
v___y_5733_ = v_a_5766_;
v___y_5734_ = v___x_5787_;
v___y_5735_ = v___y_5758_;
v___y_5736_ = v___y_5759_;
v___y_5737_ = v___y_5760_;
v___y_5738_ = v___y_5761_;
v___y_5739_ = v___y_5762_;
v___y_5740_ = v___y_5763_;
v___y_5741_ = v___y_5764_;
goto v___jp_5732_;
}
else
{
lean_object* v___x_5788_; 
v___x_5788_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_5758_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_);
if (lean_obj_tag(v___x_5788_) == 0)
{
lean_object* v_a_5789_; lean_object* v_toGoalState_5790_; lean_object* v_ematch_5791_; lean_object* v_mvarId_5792_; lean_object* v___x_5794_; uint8_t v_isShared_5795_; uint8_t v_isSharedCheck_5848_; 
v_a_5789_ = lean_ctor_get(v___x_5788_, 0);
lean_inc(v_a_5789_);
lean_dec_ref_known(v___x_5788_, 1);
v_toGoalState_5790_ = lean_ctor_get(v_a_5789_, 0);
lean_inc_ref(v_toGoalState_5790_);
v_ematch_5791_ = lean_ctor_get(v_toGoalState_5790_, 12);
lean_inc_ref(v_ematch_5791_);
v_mvarId_5792_ = lean_ctor_get(v_a_5789_, 1);
v_isSharedCheck_5848_ = !lean_is_exclusive(v_a_5789_);
if (v_isSharedCheck_5848_ == 0)
{
lean_object* v_unused_5849_; 
v_unused_5849_ = lean_ctor_get(v_a_5789_, 0);
lean_dec(v_unused_5849_);
v___x_5794_ = v_a_5789_;
v_isShared_5795_ = v_isSharedCheck_5848_;
goto v_resetjp_5793_;
}
else
{
lean_inc(v_mvarId_5792_);
lean_dec(v_a_5789_);
v___x_5794_ = lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5848_;
goto v_resetjp_5793_;
}
v_resetjp_5793_:
{
lean_object* v_nextDeclIdx_5796_; lean_object* v_enodeMap_5797_; lean_object* v_exprs_5798_; lean_object* v_parents_5799_; lean_object* v_congrTable_5800_; lean_object* v_appMap_5801_; lean_object* v_indicesFound_5802_; lean_object* v_toProcess_5803_; uint8_t v_inconsistent_5804_; lean_object* v_nextIdx_5805_; lean_object* v_newRawFacts_5806_; lean_object* v_facts_5807_; lean_object* v_extThms_5808_; lean_object* v_inj_5809_; lean_object* v_split_5810_; lean_object* v_clean_5811_; lean_object* v_sstates_5812_; lean_object* v_gmt_5813_; lean_object* v_thms_5814_; lean_object* v_newThms_5815_; lean_object* v_numInstances_5816_; lean_object* v_numDelayedInstances_5817_; lean_object* v_num_5818_; lean_object* v_preInstances_5819_; lean_object* v_nextThmIdx_5820_; lean_object* v_matchEqNames_5821_; lean_object* v_delayedThmInsts_5822_; lean_object* v___x_5823_; lean_object* v___f_5824_; lean_object* v___x_5825_; 
v_nextDeclIdx_5796_ = lean_ctor_get(v_toGoalState_5790_, 0);
lean_inc(v_nextDeclIdx_5796_);
v_enodeMap_5797_ = lean_ctor_get(v_toGoalState_5790_, 1);
lean_inc_ref(v_enodeMap_5797_);
v_exprs_5798_ = lean_ctor_get(v_toGoalState_5790_, 2);
lean_inc_ref(v_exprs_5798_);
v_parents_5799_ = lean_ctor_get(v_toGoalState_5790_, 3);
lean_inc_ref(v_parents_5799_);
v_congrTable_5800_ = lean_ctor_get(v_toGoalState_5790_, 4);
lean_inc_ref(v_congrTable_5800_);
v_appMap_5801_ = lean_ctor_get(v_toGoalState_5790_, 5);
lean_inc_ref(v_appMap_5801_);
v_indicesFound_5802_ = lean_ctor_get(v_toGoalState_5790_, 6);
lean_inc_ref(v_indicesFound_5802_);
v_toProcess_5803_ = lean_ctor_get(v_toGoalState_5790_, 7);
lean_inc_ref(v_toProcess_5803_);
v_inconsistent_5804_ = lean_ctor_get_uint8(v_toGoalState_5790_, sizeof(void*)*17);
v_nextIdx_5805_ = lean_ctor_get(v_toGoalState_5790_, 8);
lean_inc(v_nextIdx_5805_);
v_newRawFacts_5806_ = lean_ctor_get(v_toGoalState_5790_, 9);
lean_inc_ref(v_newRawFacts_5806_);
v_facts_5807_ = lean_ctor_get(v_toGoalState_5790_, 10);
lean_inc_ref(v_facts_5807_);
v_extThms_5808_ = lean_ctor_get(v_toGoalState_5790_, 11);
lean_inc_ref(v_extThms_5808_);
v_inj_5809_ = lean_ctor_get(v_toGoalState_5790_, 13);
lean_inc_ref(v_inj_5809_);
v_split_5810_ = lean_ctor_get(v_toGoalState_5790_, 14);
lean_inc_ref(v_split_5810_);
v_clean_5811_ = lean_ctor_get(v_toGoalState_5790_, 15);
lean_inc_ref(v_clean_5811_);
v_sstates_5812_ = lean_ctor_get(v_toGoalState_5790_, 16);
lean_inc_ref(v_sstates_5812_);
lean_dec_ref(v_toGoalState_5790_);
v_gmt_5813_ = lean_ctor_get(v_ematch_5791_, 1);
lean_inc(v_gmt_5813_);
v_thms_5814_ = lean_ctor_get(v_ematch_5791_, 2);
lean_inc_ref(v_thms_5814_);
v_newThms_5815_ = lean_ctor_get(v_ematch_5791_, 3);
lean_inc_ref(v_newThms_5815_);
v_numInstances_5816_ = lean_ctor_get(v_ematch_5791_, 4);
lean_inc(v_numInstances_5816_);
v_numDelayedInstances_5817_ = lean_ctor_get(v_ematch_5791_, 5);
lean_inc(v_numDelayedInstances_5817_);
v_num_5818_ = lean_ctor_get(v_ematch_5791_, 6);
lean_inc(v_num_5818_);
v_preInstances_5819_ = lean_ctor_get(v_ematch_5791_, 7);
lean_inc_ref(v_preInstances_5819_);
v_nextThmIdx_5820_ = lean_ctor_get(v_ematch_5791_, 8);
lean_inc(v_nextThmIdx_5820_);
v_matchEqNames_5821_ = lean_ctor_get(v_ematch_5791_, 9);
lean_inc_ref(v_matchEqNames_5821_);
v_delayedThmInsts_5822_ = lean_ctor_get(v_ematch_5791_, 10);
lean_inc_ref(v_delayedThmInsts_5822_);
lean_dec_ref(v_ematch_5791_);
v___x_5823_ = lean_box(v_inconsistent_5804_);
v___f_5824_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 38, 28);
lean_closure_set(v___f_5824_, 0, v_thms_5814_);
lean_closure_set(v___f_5824_, 1, v_newThms_5815_);
lean_closure_set(v___f_5824_, 2, v_gmt_5813_);
lean_closure_set(v___f_5824_, 3, v_numInstances_5816_);
lean_closure_set(v___f_5824_, 4, v_numDelayedInstances_5817_);
lean_closure_set(v___f_5824_, 5, v_num_5818_);
lean_closure_set(v___f_5824_, 6, v_preInstances_5819_);
lean_closure_set(v___f_5824_, 7, v_nextThmIdx_5820_);
lean_closure_set(v___f_5824_, 8, v_matchEqNames_5821_);
lean_closure_set(v___f_5824_, 9, v_delayedThmInsts_5822_);
lean_closure_set(v___f_5824_, 10, v_nextDeclIdx_5796_);
lean_closure_set(v___f_5824_, 11, v_enodeMap_5797_);
lean_closure_set(v___f_5824_, 12, v_exprs_5798_);
lean_closure_set(v___f_5824_, 13, v_parents_5799_);
lean_closure_set(v___f_5824_, 14, v_congrTable_5800_);
lean_closure_set(v___f_5824_, 15, v_appMap_5801_);
lean_closure_set(v___f_5824_, 16, v_indicesFound_5802_);
lean_closure_set(v___f_5824_, 17, v_toProcess_5803_);
lean_closure_set(v___f_5824_, 18, v___x_5823_);
lean_closure_set(v___f_5824_, 19, v_nextIdx_5805_);
lean_closure_set(v___f_5824_, 20, v_newRawFacts_5806_);
lean_closure_set(v___f_5824_, 21, v_facts_5807_);
lean_closure_set(v___f_5824_, 22, v_extThms_5808_);
lean_closure_set(v___f_5824_, 23, v_inj_5809_);
lean_closure_set(v___f_5824_, 24, v_split_5810_);
lean_closure_set(v___f_5824_, 25, v_clean_5811_);
lean_closure_set(v___f_5824_, 26, v_sstates_5812_);
lean_closure_set(v___f_5824_, 27, v_mvarId_5792_);
v___x_5825_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_5824_, v___x_5787_, v___y_5758_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_);
if (lean_obj_tag(v___x_5825_) == 0)
{
lean_object* v_a_5826_; lean_object* v___x_5827_; lean_object* v___x_5829_; 
v_a_5826_ = lean_ctor_get(v___x_5825_, 0);
lean_inc(v_a_5826_);
lean_dec_ref_known(v___x_5825_, 1);
v___x_5827_ = lean_box(0);
if (v_isShared_5795_ == 0)
{
lean_ctor_set_tag(v___x_5794_, 1);
lean_ctor_set(v___x_5794_, 1, v___x_5827_);
lean_ctor_set(v___x_5794_, 0, v_a_5826_);
v___x_5829_ = v___x_5794_;
goto v_reusejp_5828_;
}
else
{
lean_object* v_reuseFailAlloc_5839_; 
v_reuseFailAlloc_5839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5839_, 0, v_a_5826_);
lean_ctor_set(v_reuseFailAlloc_5839_, 1, v___x_5827_);
v___x_5829_ = v_reuseFailAlloc_5839_;
goto v_reusejp_5828_;
}
v_reusejp_5828_:
{
lean_object* v___x_5830_; 
v___x_5830_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_5829_, v___y_5758_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_);
if (lean_obj_tag(v___x_5830_) == 0)
{
lean_dec_ref_known(v___x_5830_, 1);
v___y_5733_ = v_a_5766_;
v___y_5734_ = v___x_5787_;
v___y_5735_ = v___y_5758_;
v___y_5736_ = v___y_5759_;
v___y_5737_ = v___y_5760_;
v___y_5738_ = v___y_5761_;
v___y_5739_ = v___y_5762_;
v___y_5740_ = v___y_5763_;
v___y_5741_ = v___y_5764_;
goto v___jp_5732_;
}
else
{
lean_object* v_a_5831_; lean_object* v___x_5833_; uint8_t v_isShared_5834_; uint8_t v_isSharedCheck_5838_; 
lean_dec_ref_known(v___x_5787_, 5);
lean_dec(v_a_5766_);
lean_dec_ref(v_k_5722_);
v_a_5831_ = lean_ctor_get(v___x_5830_, 0);
v_isSharedCheck_5838_ = !lean_is_exclusive(v___x_5830_);
if (v_isSharedCheck_5838_ == 0)
{
v___x_5833_ = v___x_5830_;
v_isShared_5834_ = v_isSharedCheck_5838_;
goto v_resetjp_5832_;
}
else
{
lean_inc(v_a_5831_);
lean_dec(v___x_5830_);
v___x_5833_ = lean_box(0);
v_isShared_5834_ = v_isSharedCheck_5838_;
goto v_resetjp_5832_;
}
v_resetjp_5832_:
{
lean_object* v___x_5836_; 
if (v_isShared_5834_ == 0)
{
v___x_5836_ = v___x_5833_;
goto v_reusejp_5835_;
}
else
{
lean_object* v_reuseFailAlloc_5837_; 
v_reuseFailAlloc_5837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5837_, 0, v_a_5831_);
v___x_5836_ = v_reuseFailAlloc_5837_;
goto v_reusejp_5835_;
}
v_reusejp_5835_:
{
return v___x_5836_;
}
}
}
}
}
else
{
lean_object* v_a_5840_; lean_object* v___x_5842_; uint8_t v_isShared_5843_; uint8_t v_isSharedCheck_5847_; 
lean_del_object(v___x_5794_);
lean_dec_ref_known(v___x_5787_, 5);
lean_dec(v_a_5766_);
lean_dec_ref(v_k_5722_);
v_a_5840_ = lean_ctor_get(v___x_5825_, 0);
v_isSharedCheck_5847_ = !lean_is_exclusive(v___x_5825_);
if (v_isSharedCheck_5847_ == 0)
{
v___x_5842_ = v___x_5825_;
v_isShared_5843_ = v_isSharedCheck_5847_;
goto v_resetjp_5841_;
}
else
{
lean_inc(v_a_5840_);
lean_dec(v___x_5825_);
v___x_5842_ = lean_box(0);
v_isShared_5843_ = v_isSharedCheck_5847_;
goto v_resetjp_5841_;
}
v_resetjp_5841_:
{
lean_object* v___x_5845_; 
if (v_isShared_5843_ == 0)
{
v___x_5845_ = v___x_5842_;
goto v_reusejp_5844_;
}
else
{
lean_object* v_reuseFailAlloc_5846_; 
v_reuseFailAlloc_5846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5846_, 0, v_a_5840_);
v___x_5845_ = v_reuseFailAlloc_5846_;
goto v_reusejp_5844_;
}
v_reusejp_5844_:
{
return v___x_5845_;
}
}
}
}
}
else
{
lean_object* v_a_5850_; lean_object* v___x_5852_; uint8_t v_isShared_5853_; uint8_t v_isSharedCheck_5857_; 
lean_dec_ref_known(v___x_5787_, 5);
lean_dec(v_a_5766_);
lean_dec_ref(v_k_5722_);
v_a_5850_ = lean_ctor_get(v___x_5788_, 0);
v_isSharedCheck_5857_ = !lean_is_exclusive(v___x_5788_);
if (v_isSharedCheck_5857_ == 0)
{
v___x_5852_ = v___x_5788_;
v_isShared_5853_ = v_isSharedCheck_5857_;
goto v_resetjp_5851_;
}
else
{
lean_inc(v_a_5850_);
lean_dec(v___x_5788_);
v___x_5852_ = lean_box(0);
v_isShared_5853_ = v_isSharedCheck_5857_;
goto v_resetjp_5851_;
}
v_resetjp_5851_:
{
lean_object* v___x_5855_; 
if (v_isShared_5853_ == 0)
{
v___x_5855_ = v___x_5852_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5856_; 
v_reuseFailAlloc_5856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5856_, 0, v_a_5850_);
v___x_5855_ = v_reuseFailAlloc_5856_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
return v___x_5855_;
}
}
}
}
}
else
{
lean_object* v_a_5858_; lean_object* v___x_5860_; uint8_t v_isShared_5861_; uint8_t v_isSharedCheck_5865_; 
lean_dec_ref(v_k_5722_);
v_a_5858_ = lean_ctor_get(v___x_5765_, 0);
v_isSharedCheck_5865_ = !lean_is_exclusive(v___x_5765_);
if (v_isSharedCheck_5865_ == 0)
{
v___x_5860_ = v___x_5765_;
v_isShared_5861_ = v_isSharedCheck_5865_;
goto v_resetjp_5859_;
}
else
{
lean_inc(v_a_5858_);
lean_dec(v___x_5765_);
v___x_5860_ = lean_box(0);
v_isShared_5861_ = v_isSharedCheck_5865_;
goto v_resetjp_5859_;
}
v_resetjp_5859_:
{
lean_object* v___x_5863_; 
if (v_isShared_5861_ == 0)
{
v___x_5863_ = v___x_5860_;
goto v_reusejp_5862_;
}
else
{
lean_object* v_reuseFailAlloc_5864_; 
v_reuseFailAlloc_5864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5864_, 0, v_a_5858_);
v___x_5863_ = v_reuseFailAlloc_5864_;
goto v_reusejp_5862_;
}
v_reusejp_5862_:
{
return v___x_5863_;
}
}
}
}
v___jp_5866_:
{
uint8_t v___x_5868_; 
v___x_5868_ = 1;
if (v_only_5721_ == 0)
{
v___y_5754_ = v___x_5868_;
v___y_5755_ = v___y_5867_;
v_params_5756_ = v_params_5719_;
v___y_5757_ = v_a_5723_;
v___y_5758_ = v_a_5724_;
v___y_5759_ = v_a_5725_;
v___y_5760_ = v_a_5726_;
v___y_5761_ = v_a_5727_;
v___y_5762_ = v_a_5728_;
v___y_5763_ = v_a_5729_;
v___y_5764_ = v_a_5730_;
goto v___jp_5753_;
}
else
{
lean_object* v_config_5869_; lean_object* v_extensions_5870_; lean_object* v_extra_5871_; lean_object* v_extraInj_5872_; lean_object* v_extraFacts_5873_; lean_object* v_symPrios_5874_; lean_object* v_norm_5875_; lean_object* v_normProcs_5876_; lean_object* v___x_5878_; uint8_t v_isShared_5879_; uint8_t v_isSharedCheck_5887_; 
v_config_5869_ = lean_ctor_get(v_params_5719_, 0);
v_extensions_5870_ = lean_ctor_get(v_params_5719_, 1);
v_extra_5871_ = lean_ctor_get(v_params_5719_, 2);
v_extraInj_5872_ = lean_ctor_get(v_params_5719_, 3);
v_extraFacts_5873_ = lean_ctor_get(v_params_5719_, 4);
v_symPrios_5874_ = lean_ctor_get(v_params_5719_, 5);
v_norm_5875_ = lean_ctor_get(v_params_5719_, 6);
v_normProcs_5876_ = lean_ctor_get(v_params_5719_, 7);
v_isSharedCheck_5887_ = !lean_is_exclusive(v_params_5719_);
if (v_isSharedCheck_5887_ == 0)
{
lean_object* v_unused_5888_; 
v_unused_5888_ = lean_ctor_get(v_params_5719_, 8);
lean_dec(v_unused_5888_);
v___x_5878_ = v_params_5719_;
v_isShared_5879_ = v_isSharedCheck_5887_;
goto v_resetjp_5877_;
}
else
{
lean_inc(v_normProcs_5876_);
lean_inc(v_norm_5875_);
lean_inc(v_symPrios_5874_);
lean_inc(v_extraFacts_5873_);
lean_inc(v_extraInj_5872_);
lean_inc(v_extra_5871_);
lean_inc(v_extensions_5870_);
lean_inc(v_config_5869_);
lean_dec(v_params_5719_);
v___x_5878_ = lean_box(0);
v_isShared_5879_ = v_isSharedCheck_5887_;
goto v_resetjp_5877_;
}
v_resetjp_5877_:
{
size_t v_sz_5880_; size_t v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v_params_5885_; 
v_sz_5880_ = lean_array_size(v_extensions_5870_);
v___x_5881_ = ((size_t)0ULL);
v___x_5882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_5880_, v___x_5881_, v_extensions_5870_);
v___x_5883_ = lean_box(0);
if (v_isShared_5879_ == 0)
{
lean_ctor_set(v___x_5878_, 8, v___x_5883_);
lean_ctor_set(v___x_5878_, 1, v___x_5882_);
v_params_5885_ = v___x_5878_;
goto v_reusejp_5884_;
}
else
{
lean_object* v_reuseFailAlloc_5886_; 
v_reuseFailAlloc_5886_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5886_, 0, v_config_5869_);
lean_ctor_set(v_reuseFailAlloc_5886_, 1, v___x_5882_);
lean_ctor_set(v_reuseFailAlloc_5886_, 2, v_extra_5871_);
lean_ctor_set(v_reuseFailAlloc_5886_, 3, v_extraInj_5872_);
lean_ctor_set(v_reuseFailAlloc_5886_, 4, v_extraFacts_5873_);
lean_ctor_set(v_reuseFailAlloc_5886_, 5, v_symPrios_5874_);
lean_ctor_set(v_reuseFailAlloc_5886_, 6, v_norm_5875_);
lean_ctor_set(v_reuseFailAlloc_5886_, 7, v_normProcs_5876_);
lean_ctor_set(v_reuseFailAlloc_5886_, 8, v___x_5883_);
v_params_5885_ = v_reuseFailAlloc_5886_;
goto v_reusejp_5884_;
}
v_reusejp_5884_:
{
v___y_5754_ = v___x_5868_;
v___y_5755_ = v___y_5867_;
v_params_5756_ = v_params_5885_;
v___y_5757_ = v_a_5723_;
v___y_5758_ = v_a_5724_;
v___y_5759_ = v_a_5725_;
v___y_5760_ = v_a_5726_;
v___y_5761_ = v_a_5727_;
v___y_5762_ = v_a_5728_;
v___y_5763_ = v_a_5729_;
v___y_5764_ = v_a_5730_;
goto v___jp_5753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_5894_, lean_object* v_ps_5895_, lean_object* v_only_5896_, lean_object* v_k_5897_, lean_object* v_a_5898_, lean_object* v_a_5899_, lean_object* v_a_5900_, lean_object* v_a_5901_, lean_object* v_a_5902_, lean_object* v_a_5903_, lean_object* v_a_5904_, lean_object* v_a_5905_, lean_object* v_a_5906_){
_start:
{
uint8_t v_only_boxed_5907_; lean_object* v_res_5908_; 
v_only_boxed_5907_ = lean_unbox(v_only_5896_);
v_res_5908_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5894_, v_ps_5895_, v_only_boxed_5907_, v_k_5897_, v_a_5898_, v_a_5899_, v_a_5900_, v_a_5901_, v_a_5902_, v_a_5903_, v_a_5904_, v_a_5905_);
lean_dec(v_a_5905_);
lean_dec_ref(v_a_5904_);
lean_dec(v_a_5903_);
lean_dec_ref(v_a_5902_);
lean_dec(v_a_5901_);
lean_dec_ref(v_a_5900_);
lean_dec(v_a_5899_);
lean_dec_ref(v_a_5898_);
lean_dec_ref(v_ps_5895_);
return v_res_5908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_5909_, lean_object* v_params_5910_, lean_object* v_ps_5911_, uint8_t v_only_5912_, lean_object* v_k_5913_, lean_object* v_a_5914_, lean_object* v_a_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_, lean_object* v_a_5921_){
_start:
{
lean_object* v___x_5923_; 
v___x_5923_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5910_, v_ps_5911_, v_only_5912_, v_k_5913_, v_a_5914_, v_a_5915_, v_a_5916_, v_a_5917_, v_a_5918_, v_a_5919_, v_a_5920_, v_a_5921_);
return v___x_5923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_5924_, lean_object* v_params_5925_, lean_object* v_ps_5926_, lean_object* v_only_5927_, lean_object* v_k_5928_, lean_object* v_a_5929_, lean_object* v_a_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_, lean_object* v_a_5933_, lean_object* v_a_5934_, lean_object* v_a_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_){
_start:
{
uint8_t v_only_boxed_5938_; lean_object* v_res_5939_; 
v_only_boxed_5938_ = lean_unbox(v_only_5927_);
v_res_5939_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_5924_, v_params_5925_, v_ps_5926_, v_only_boxed_5938_, v_k_5928_, v_a_5929_, v_a_5930_, v_a_5931_, v_a_5932_, v_a_5933_, v_a_5934_, v_a_5935_, v_a_5936_);
lean_dec(v_a_5936_);
lean_dec_ref(v_a_5935_);
lean_dec(v_a_5934_);
lean_dec_ref(v_a_5933_);
lean_dec(v_a_5932_);
lean_dec_ref(v_a_5931_);
lean_dec(v_a_5930_);
lean_dec_ref(v_a_5929_);
lean_dec_ref(v_ps_5926_);
return v_res_5939_;
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
