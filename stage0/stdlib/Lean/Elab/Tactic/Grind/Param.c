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
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_Grind_grindExt;
lean_object* l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_find___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AsyncConstantInfo_toConstantVal(lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_assertExtra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Grind_getPreservedParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Grind_getPreservedParams___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_getPreservedParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_getPreservedParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_getPreservedParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_394_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_394_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_394_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_394_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
if (lean_obj_tag(v_a_360_) == 1)
{
lean_object* v_val_364_; lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_val_364_ = lean_ctor_get(v_a_360_, 0);
lean_inc(v_val_364_);
lean_dec_ref_known(v_a_360_, 1);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_array_get_size(v_val_364_);
v___x_380_ = lean_nat_dec_lt(v___x_378_, v___x_379_);
if (v___x_380_ == 0)
{
lean_dec(v_declName_347_);
goto v___jp_365_;
}
else
{
if (v___x_380_ == 0)
{
lean_dec(v_declName_347_);
goto v___jp_365_;
}
else
{
size_t v___x_381_; size_t v___x_382_; uint8_t v___x_383_; 
v___x_381_ = ((size_t)0ULL);
v___x_382_ = lean_usize_of_nat(v___x_379_);
v___x_383_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_346_, v___x_358_, v_val_364_, v___x_381_, v___x_382_);
if (v___x_383_ == 0)
{
lean_dec(v_declName_347_);
goto v___jp_365_;
}
else
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_347_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_dec_ref_known(v___x_384_, 1);
goto v___jp_365_;
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_val_364_);
lean_del_object(v___x_362_);
lean_dec_ref(v_params_346_);
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
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
size_t v___x_372_; size_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_372_ = ((size_t)0ULL);
v___x_373_ = lean_usize_of_nat(v___x_367_);
v___x_374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_val_364_, v___x_372_, v___x_373_, v_params_346_);
lean_dec(v_val_364_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_374_);
v___x_376_ = v___x_362_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_object* v___x_393_; 
lean_del_object(v___x_362_);
lean_dec(v_a_360_);
lean_dec_ref(v_params_346_);
v___x_393_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_347_, v_a_350_, v_a_351_);
return v___x_393_;
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec(v_declName_347_);
lean_dec_ref(v_params_346_);
v_a_395_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_359_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_359_);
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
else
{
uint8_t v___x_403_; 
lean_inc(v_declName_347_);
v___x_403_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_346_, v_declName_347_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
lean_inc(v_declName_347_);
v___x_404_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_347_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_dec_ref_known(v___x_404_, 1);
goto v___jp_353_;
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_declName_347_);
lean_dec_ref(v_params_346_);
v_a_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_404_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch___boxed(lean_object* v_params_413_, lean_object* v_declName_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_params_413_, v_declName_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(lean_object* v_params_421_, lean_object* v_declName_422_){
_start:
{
lean_object* v_config_423_; lean_object* v_extensions_424_; lean_object* v_extra_425_; lean_object* v_extraInj_426_; lean_object* v_extraFacts_427_; lean_object* v_symPrios_428_; lean_object* v_norm_429_; lean_object* v_normProcs_430_; lean_object* v_anchorRefs_x3f_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_config_423_ = lean_ctor_get(v_params_421_, 0);
v_extensions_424_ = lean_ctor_get(v_params_421_, 1);
v_extra_425_ = lean_ctor_get(v_params_421_, 2);
v_extraInj_426_ = lean_ctor_get(v_params_421_, 3);
v_extraFacts_427_ = lean_ctor_get(v_params_421_, 4);
v_symPrios_428_ = lean_ctor_get(v_params_421_, 5);
v_norm_429_ = lean_ctor_get(v_params_421_, 6);
v_normProcs_430_ = lean_ctor_get(v_params_421_, 7);
v_anchorRefs_x3f_431_ = lean_ctor_get(v_params_421_, 8);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_array_get_size(v_extensions_424_);
v___x_434_ = lean_nat_dec_lt(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_dec(v_declName_422_);
return v_params_421_;
}
else
{
lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_459_; 
lean_inc(v_anchorRefs_x3f_431_);
lean_inc_ref(v_normProcs_430_);
lean_inc_ref(v_norm_429_);
lean_inc_ref(v_symPrios_428_);
lean_inc_ref(v_extraFacts_427_);
lean_inc_ref(v_extraInj_426_);
lean_inc_ref(v_extra_425_);
lean_inc_ref(v_extensions_424_);
lean_inc_ref(v_config_423_);
v_isSharedCheck_459_ = !lean_is_exclusive(v_params_421_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; lean_object* v_unused_461_; lean_object* v_unused_462_; lean_object* v_unused_463_; lean_object* v_unused_464_; lean_object* v_unused_465_; lean_object* v_unused_466_; lean_object* v_unused_467_; lean_object* v_unused_468_; 
v_unused_460_ = lean_ctor_get(v_params_421_, 8);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_params_421_, 7);
lean_dec(v_unused_461_);
v_unused_462_ = lean_ctor_get(v_params_421_, 6);
lean_dec(v_unused_462_);
v_unused_463_ = lean_ctor_get(v_params_421_, 5);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_params_421_, 4);
lean_dec(v_unused_464_);
v_unused_465_ = lean_ctor_get(v_params_421_, 3);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_params_421_, 2);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_params_421_, 1);
lean_dec(v_unused_467_);
v_unused_468_ = lean_ctor_get(v_params_421_, 0);
lean_dec(v_unused_468_);
v___x_436_ = v_params_421_;
v_isShared_437_ = v_isSharedCheck_459_;
goto v_resetjp_435_;
}
else
{
lean_dec(v_params_421_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_459_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_v_438_; lean_object* v_casesTypes_439_; lean_object* v_extThms_440_; lean_object* v_funCC_441_; lean_object* v_ematch_442_; lean_object* v_inj_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_458_; 
v_v_438_ = lean_array_fget(v_extensions_424_, v___x_432_);
v_casesTypes_439_ = lean_ctor_get(v_v_438_, 0);
v_extThms_440_ = lean_ctor_get(v_v_438_, 1);
v_funCC_441_ = lean_ctor_get(v_v_438_, 2);
v_ematch_442_ = lean_ctor_get(v_v_438_, 3);
v_inj_443_ = lean_ctor_get(v_v_438_, 4);
v_isSharedCheck_458_ = !lean_is_exclusive(v_v_438_);
if (v_isSharedCheck_458_ == 0)
{
v___x_445_ = v_v_438_;
v_isShared_446_ = v_isSharedCheck_458_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_inj_443_);
lean_inc(v_ematch_442_);
lean_inc(v_funCC_441_);
lean_inc(v_extThms_440_);
lean_inc(v_casesTypes_439_);
lean_dec(v_v_438_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_458_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v_xs_x27_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_447_ = lean_box(0);
v_xs_x27_448_ = lean_array_fset(v_extensions_424_, v___x_432_, v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v_declName_422_);
v___x_450_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_inj_443_, v___x_449_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 4, v___x_450_);
v___x_452_ = v___x_445_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_casesTypes_439_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_extThms_440_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v_funCC_441_);
lean_ctor_set(v_reuseFailAlloc_457_, 3, v_ematch_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 4, v___x_450_);
v___x_452_ = v_reuseFailAlloc_457_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = lean_array_fset(v_xs_x27_448_, v___x_432_, v___x_452_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_453_);
v___x_455_ = v___x_436_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_config_423_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_extra_425_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_extraInj_426_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v_extraFacts_427_);
lean_ctor_set(v_reuseFailAlloc_456_, 5, v_symPrios_428_);
lean_ctor_set(v_reuseFailAlloc_456_, 6, v_norm_429_);
lean_ctor_set(v_reuseFailAlloc_456_, 7, v_normProcs_430_);
lean_ctor_set(v_reuseFailAlloc_456_, 8, v_anchorRefs_x3f_431_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(lean_object* v_origin_469_, lean_object* v_as_470_, size_t v_sz_471_, size_t v_i_472_, lean_object* v_b_473_){
_start:
{
lean_object* v_a_475_; uint8_t v___x_479_; 
v___x_479_ = lean_usize_dec_lt(v_i_472_, v_sz_471_);
if (v___x_479_ == 0)
{
return v_b_473_;
}
else
{
lean_object* v_a_480_; lean_object* v_ematch_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_a_480_ = lean_array_uget_borrowed(v_as_470_, v_i_472_);
v_ematch_481_ = lean_ctor_get(v_a_480_, 3);
v___x_482_ = l_Lean_Meta_Grind_EMatchTheorems_getKindsFor(v_ematch_481_, v_origin_469_);
v___x_483_ = l_List_isEmpty___redArg(v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = l_List_appendTR___redArg(v_b_473_, v___x_482_);
v_a_475_ = v___x_484_;
goto v___jp_474_;
}
else
{
lean_dec(v___x_482_);
v_a_475_ = v_b_473_;
goto v___jp_474_;
}
}
v___jp_474_:
{
size_t v___x_476_; size_t v___x_477_; 
v___x_476_ = ((size_t)1ULL);
v___x_477_ = lean_usize_add(v_i_472_, v___x_476_);
v_i_472_ = v___x_477_;
v_b_473_ = v_a_475_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0___boxed(lean_object* v_origin_485_, lean_object* v_as_486_, lean_object* v_sz_487_, lean_object* v_i_488_, lean_object* v_b_489_){
_start:
{
size_t v_sz_boxed_490_; size_t v_i_boxed_491_; lean_object* v_res_492_; 
v_sz_boxed_490_ = lean_unbox_usize(v_sz_487_);
lean_dec(v_sz_487_);
v_i_boxed_491_ = lean_unbox_usize(v_i_488_);
lean_dec(v_i_488_);
v_res_492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_485_, v_as_486_, v_sz_boxed_490_, v_i_boxed_491_, v_b_489_);
lean_dec_ref(v_as_486_);
lean_dec_ref(v_origin_485_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(lean_object* v_s_493_, lean_object* v_origin_494_){
_start:
{
lean_object* v_result_495_; size_t v_sz_496_; size_t v___x_497_; lean_object* v___x_498_; 
v_result_495_ = lean_box(0);
v_sz_496_ = lean_array_size(v_s_493_);
v___x_497_ = ((size_t)0ULL);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_494_, v_s_493_, v_sz_496_, v___x_497_, v_result_495_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor___boxed(lean_object* v_s_499_, lean_object* v_origin_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_499_, v_origin_500_);
lean_dec_ref(v_origin_500_);
lean_dec_ref(v_s_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(lean_object* v_upperBound_502_, lean_object* v_s_503_, lean_object* v_origin_504_, lean_object* v_a_505_, lean_object* v_b_506_){
_start:
{
lean_object* v_a_508_; uint8_t v___x_512_; 
v___x_512_ = lean_nat_dec_lt(v_a_505_, v_upperBound_502_);
if (v___x_512_ == 0)
{
lean_dec(v_a_505_);
return v_b_506_;
}
else
{
lean_object* v___x_513_; lean_object* v_ematch_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_513_ = lean_array_fget_borrowed(v_s_503_, v_a_505_);
v_ematch_514_ = lean_ctor_get(v___x_513_, 3);
v___x_515_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_ematch_514_, v_origin_504_);
v___x_516_ = l_List_isEmpty___redArg(v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
v___x_517_ = l_List_appendTR___redArg(v_b_506_, v___x_515_);
v_a_508_ = v___x_517_;
goto v___jp_507_;
}
else
{
lean_dec(v___x_515_);
v_a_508_ = v_b_506_;
goto v___jp_507_;
}
}
v___jp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_nat_add(v_a_505_, v___x_509_);
lean_dec(v_a_505_);
v_a_505_ = v___x_510_;
v_b_506_ = v_a_508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg___boxed(lean_object* v_upperBound_518_, lean_object* v_s_519_, lean_object* v_origin_520_, lean_object* v_a_521_, lean_object* v_b_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v_upperBound_518_, v_s_519_, v_origin_520_, v_a_521_, v_b_522_);
lean_dec_ref(v_origin_520_);
lean_dec_ref(v_s_519_);
lean_dec(v_upperBound_518_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find(lean_object* v_s_524_, lean_object* v_origin_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_r_528_; lean_object* v___x_529_; 
v___x_526_ = lean_array_get_size(v_s_524_);
v___x_527_ = lean_unsigned_to_nat(0u);
v_r_528_ = lean_box(0);
v___x_529_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v___x_526_, v_s_524_, v_origin_525_, v___x_527_, v_r_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find___boxed(lean_object* v_s_530_, lean_object* v_origin_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Meta_Grind_ExtensionStateArray_find(v_s_530_, v_origin_531_);
lean_dec_ref(v_origin_531_);
lean_dec_ref(v_s_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(lean_object* v_upperBound_533_, lean_object* v_s_534_, lean_object* v_origin_535_, lean_object* v_inst_536_, lean_object* v_R_537_, lean_object* v_a_538_, lean_object* v_b_539_, lean_object* v_c_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v_upperBound_533_, v_s_534_, v_origin_535_, v_a_538_, v_b_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___boxed(lean_object* v_upperBound_542_, lean_object* v_s_543_, lean_object* v_origin_544_, lean_object* v_inst_545_, lean_object* v_R_546_, lean_object* v_a_547_, lean_object* v_b_548_, lean_object* v_c_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(v_upperBound_542_, v_s_543_, v_origin_544_, v_inst_545_, v_R_546_, v_a_547_, v_b_548_, v_c_549_);
lean_dec_ref(v_origin_544_);
lean_dec_ref(v_s_543_);
lean_dec(v_upperBound_542_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(lean_object* v_msgData_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; lean_object* v_env_558_; uint8_t v___x_559_; lean_object* v_env_560_; lean_object* v___x_561_; lean_object* v_toCold_562_; lean_object* v_mctx_563_; lean_object* v_lctx_564_; lean_object* v_options_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_557_ = lean_st_ref_get(v___y_555_);
v_env_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc_ref(v_env_558_);
lean_dec(v___x_557_);
v___x_559_ = 0;
v_env_560_ = l_Lean_Environment_setRecordingDeps(v_env_558_, v___x_559_);
v___x_561_ = lean_st_ref_get(v___y_553_);
v_toCold_562_ = lean_ctor_get(v___y_554_, 0);
v_mctx_563_ = lean_ctor_get(v___x_561_, 0);
lean_inc_ref(v_mctx_563_);
lean_dec(v___x_561_);
v_lctx_564_ = lean_ctor_get(v___y_552_, 2);
v_options_565_ = lean_ctor_get(v_toCold_562_, 2);
lean_inc_ref(v_options_565_);
lean_inc_ref(v_lctx_564_);
v___x_566_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_566_, 0, v_env_560_);
lean_ctor_set(v___x_566_, 1, v_mctx_563_);
lean_ctor_set(v___x_566_, 2, v_lctx_564_);
lean_ctor_set(v___x_566_, 3, v_options_565_);
v___x_567_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v_msgData_551_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_msgData_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msgData_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
return v_res_575_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_576_, lean_object* v_opt_577_){
_start:
{
lean_object* v_name_578_; lean_object* v_defValue_579_; lean_object* v_map_580_; lean_object* v___x_581_; 
v_name_578_ = lean_ctor_get(v_opt_577_, 0);
v_defValue_579_ = lean_ctor_get(v_opt_577_, 1);
v_map_580_ = lean_ctor_get(v_opts_576_, 0);
v___x_581_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_580_, v_name_578_);
if (lean_obj_tag(v___x_581_) == 0)
{
uint8_t v___x_582_; 
v___x_582_ = lean_unbox(v_defValue_579_);
return v___x_582_;
}
else
{
lean_object* v_val_583_; 
v_val_583_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_val_583_);
lean_dec_ref_known(v___x_581_, 1);
if (lean_obj_tag(v_val_583_) == 1)
{
uint8_t v_v_584_; 
v_v_584_ = lean_ctor_get_uint8(v_val_583_, 0);
lean_dec_ref_known(v_val_583_, 0);
return v_v_584_;
}
else
{
uint8_t v___x_585_; 
lean_dec(v_val_583_);
v___x_585_ = lean_unbox(v_defValue_579_);
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_586_, lean_object* v_opt_587_){
_start:
{
uint8_t v_res_588_; lean_object* v_r_589_; 
v_res_588_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_opts_586_, v_opt_587_);
lean_dec_ref(v_opt_587_);
lean_dec_ref(v_opts_586_);
v_r_589_ = lean_box(v_res_588_);
return v_r_589_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_598_, lean_object* v_x_599_){
_start:
{
if (lean_obj_tag(v_x_599_) == 1)
{
lean_object* v_pre_600_; 
v_pre_600_ = lean_ctor_get(v_x_599_, 0);
switch(lean_obj_tag(v_pre_600_))
{
case 1:
{
lean_object* v_pre_601_; 
v_pre_601_ = lean_ctor_get(v_pre_600_, 0);
switch(lean_obj_tag(v_pre_601_))
{
case 0:
{
lean_object* v_str_602_; lean_object* v_str_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_str_602_ = lean_ctor_get(v_x_599_, 1);
v_str_603_ = lean_ctor_get(v_pre_600_, 1);
v___x_604_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_605_ = lean_string_dec_eq(v_str_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_607_ = lean_string_dec_eq(v_str_603_, v___x_606_);
if (v___x_607_ == 0)
{
return v___x_607_;
}
else
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_609_ = lean_string_dec_eq(v_str_602_, v___x_608_);
if (v___x_609_ == 0)
{
return v___x_609_;
}
else
{
return v_suppressElabErrors_598_;
}
}
}
else
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_611_ = lean_string_dec_eq(v_str_602_, v___x_610_);
if (v___x_611_ == 0)
{
return v___x_611_;
}
else
{
return v_suppressElabErrors_598_;
}
}
}
case 1:
{
lean_object* v_pre_612_; 
v_pre_612_ = lean_ctor_get(v_pre_601_, 0);
if (lean_obj_tag(v_pre_612_) == 0)
{
lean_object* v_str_613_; lean_object* v_str_614_; lean_object* v_str_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_str_613_ = lean_ctor_get(v_x_599_, 1);
v_str_614_ = lean_ctor_get(v_pre_600_, 1);
v_str_615_ = lean_ctor_get(v_pre_601_, 1);
v___x_616_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_617_ = lean_string_dec_eq(v_str_615_, v___x_616_);
if (v___x_617_ == 0)
{
return v___x_617_;
}
else
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_619_ = lean_string_dec_eq(v_str_614_, v___x_618_);
if (v___x_619_ == 0)
{
return v___x_619_;
}
else
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_621_ = lean_string_dec_eq(v_str_613_, v___x_620_);
if (v___x_621_ == 0)
{
return v___x_621_;
}
else
{
return v_suppressElabErrors_598_;
}
}
}
}
else
{
uint8_t v___x_622_; 
v___x_622_ = 0;
return v___x_622_;
}
}
default: 
{
uint8_t v___x_623_; 
v___x_623_ = 0;
return v___x_623_;
}
}
}
case 0:
{
lean_object* v_str_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_str_624_ = lean_ctor_get(v_x_599_, 1);
v___x_625_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_626_ = lean_string_dec_eq(v_str_624_, v___x_625_);
if (v___x_626_ == 0)
{
return v___x_626_;
}
else
{
return v_suppressElabErrors_598_;
}
}
default: 
{
uint8_t v___x_627_; 
v___x_627_ = 0;
return v___x_627_;
}
}
}
else
{
uint8_t v___x_628_; 
v___x_628_ = 0;
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_629_, lean_object* v_x_630_){
_start:
{
uint8_t v_suppressElabErrors_boxed_631_; uint8_t v_res_632_; lean_object* v_r_633_; 
v_suppressElabErrors_boxed_631_ = lean_unbox(v_suppressElabErrors_629_);
v_res_632_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_631_, v_x_630_);
lean_dec(v_x_630_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* v_ref_635_, lean_object* v_msgData_636_, uint8_t v_severity_637_, uint8_t v_isSilent_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___y_645_; uint8_t v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; uint8_t v___y_651_; lean_object* v_toCold_652_; lean_object* v___y_653_; lean_object* v___y_682_; lean_object* v___y_683_; uint8_t v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; lean_object* v___y_687_; uint8_t v___y_688_; lean_object* v___y_689_; lean_object* v___y_709_; lean_object* v___y_710_; uint8_t v___y_711_; uint8_t v___y_712_; lean_object* v___y_713_; uint8_t v___y_714_; lean_object* v___y_715_; uint8_t v___y_719_; uint8_t v___y_720_; uint8_t v___x_730_; uint8_t v___y_732_; uint8_t v___x_738_; 
v___x_730_ = 2;
v___x_738_ = l_Lean_instBEqMessageSeverity_beq(v_severity_637_, v___x_730_);
if (v___x_738_ == 0)
{
v___y_732_ = v___x_738_;
goto v___jp_731_;
}
else
{
uint8_t v___x_739_; 
lean_inc_ref(v_msgData_636_);
v___x_739_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_636_);
if (v___x_739_ == 0)
{
v___y_732_ = v___x_739_;
goto v___jp_731_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec_ref(v_msgData_636_);
v___x_740_ = lean_box(0);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
}
v___jp_644_:
{
lean_object* v_currNamespace_654_; lean_object* v_openDecls_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v_env_660_; lean_object* v_nextMacroScope_661_; lean_object* v_ngen_662_; lean_object* v_auxDeclNGen_663_; lean_object* v_traceState_664_; lean_object* v_cache_665_; lean_object* v_recordedDeps_666_; lean_object* v_messages_667_; lean_object* v_infoState_668_; lean_object* v_snapshotTasks_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_680_; 
v_currNamespace_654_ = lean_ctor_get(v_toCold_652_, 4);
v_openDecls_655_ = lean_ctor_get(v_toCold_652_, 5);
lean_inc(v_openDecls_655_);
lean_inc(v_currNamespace_654_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_currNamespace_654_);
lean_ctor_set(v___x_656_, 1, v_openDecls_655_);
v___x_657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___y_648_);
lean_inc_ref(v___y_650_);
lean_inc_ref(v___y_649_);
v___x_658_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_658_, 0, v___y_649_);
lean_ctor_set(v___x_658_, 1, v___y_647_);
lean_ctor_set(v___x_658_, 2, v___y_645_);
lean_ctor_set(v___x_658_, 3, v___y_650_);
lean_ctor_set(v___x_658_, 4, v___x_657_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*5, v___y_651_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*5 + 1, v___y_646_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*5 + 2, v_isSilent_638_);
v___x_659_ = lean_st_ref_take(v___y_653_);
v_env_660_ = lean_ctor_get(v___x_659_, 0);
v_nextMacroScope_661_ = lean_ctor_get(v___x_659_, 1);
v_ngen_662_ = lean_ctor_get(v___x_659_, 2);
v_auxDeclNGen_663_ = lean_ctor_get(v___x_659_, 3);
v_traceState_664_ = lean_ctor_get(v___x_659_, 4);
v_cache_665_ = lean_ctor_get(v___x_659_, 5);
v_recordedDeps_666_ = lean_ctor_get(v___x_659_, 6);
v_messages_667_ = lean_ctor_get(v___x_659_, 7);
v_infoState_668_ = lean_ctor_get(v___x_659_, 8);
v_snapshotTasks_669_ = lean_ctor_get(v___x_659_, 9);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_680_ == 0)
{
v___x_671_ = v___x_659_;
v_isShared_672_ = v_isSharedCheck_680_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_snapshotTasks_669_);
lean_inc(v_infoState_668_);
lean_inc(v_messages_667_);
lean_inc(v_recordedDeps_666_);
lean_inc(v_cache_665_);
lean_inc(v_traceState_664_);
lean_inc(v_auxDeclNGen_663_);
lean_inc(v_ngen_662_);
lean_inc(v_nextMacroScope_661_);
lean_inc(v_env_660_);
lean_dec(v___x_659_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_680_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_673_ = lean_box(0);
v___x_674_ = l_Lean_MessageLog_add(v___x_658_, v_messages_667_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 7, v___x_674_);
v___x_676_ = v___x_671_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_env_660_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_nextMacroScope_661_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_ngen_662_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_auxDeclNGen_663_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_traceState_664_);
lean_ctor_set(v_reuseFailAlloc_679_, 5, v_cache_665_);
lean_ctor_set(v_reuseFailAlloc_679_, 6, v_recordedDeps_666_);
lean_ctor_set(v_reuseFailAlloc_679_, 7, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_679_, 8, v_infoState_668_);
lean_ctor_set(v_reuseFailAlloc_679_, 9, v_snapshotTasks_669_);
v___x_676_ = v_reuseFailAlloc_679_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_st_ref_put(v___y_653_, v___x_676_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_673_);
return v___x_678_;
}
}
}
v___jp_681_:
{
lean_object* v_fileName_690_; lean_object* v_fileMap_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_707_; 
v_fileName_690_ = lean_ctor_get(v___y_685_, 0);
v_fileMap_691_ = lean_ctor_get(v___y_685_, 1);
v___x_692_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_636_);
v___x_693_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_692_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_707_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_707_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_707_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
lean_inc_ref_n(v_fileMap_691_, 2);
v___x_698_ = l_Lean_FileMap_toPosition(v_fileMap_691_, v___y_687_);
lean_dec(v___y_687_);
v___x_699_ = l_Lean_FileMap_toPosition(v_fileMap_691_, v___y_689_);
lean_dec(v___y_689_);
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
v___x_701_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_686_ == 0)
{
lean_del_object(v___x_696_);
lean_dec_ref(v___y_682_);
v___y_645_ = v___x_700_;
v___y_646_ = v___y_684_;
v___y_647_ = v___x_698_;
v___y_648_ = v_a_694_;
v___y_649_ = v_fileName_690_;
v___y_650_ = v___x_701_;
v___y_651_ = v___y_688_;
v_toCold_652_ = v___y_683_;
v___y_653_ = v___y_642_;
goto v___jp_644_;
}
else
{
uint8_t v___x_702_; 
lean_inc(v_a_694_);
v___x_702_ = l_Lean_MessageData_hasTag(v___y_682_, v_a_694_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_705_; 
lean_dec_ref_known(v___x_700_, 1);
lean_dec_ref(v___x_698_);
lean_dec(v_a_694_);
v___x_703_ = lean_box(0);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_703_);
v___x_705_ = v___x_696_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
else
{
lean_del_object(v___x_696_);
v___y_645_ = v___x_700_;
v___y_646_ = v___y_684_;
v___y_647_ = v___x_698_;
v___y_648_ = v_a_694_;
v___y_649_ = v_fileName_690_;
v___y_650_ = v___x_701_;
v___y_651_ = v___y_688_;
v_toCold_652_ = v___y_683_;
v___y_653_ = v___y_642_;
goto v___jp_644_;
}
}
}
}
v___jp_708_:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Syntax_getTailPos_x3f(v___y_713_, v___y_714_);
lean_dec(v___y_713_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_inc(v___y_715_);
v___y_682_ = v___y_709_;
v___y_683_ = v___y_710_;
v___y_684_ = v___y_712_;
v___y_685_ = v___y_710_;
v___y_686_ = v___y_711_;
v___y_687_ = v___y_715_;
v___y_688_ = v___y_714_;
v___y_689_ = v___y_715_;
goto v___jp_681_;
}
else
{
lean_object* v_val_717_; 
v_val_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_val_717_);
lean_dec_ref_known(v___x_716_, 1);
v___y_682_ = v___y_709_;
v___y_683_ = v___y_710_;
v___y_684_ = v___y_712_;
v___y_685_ = v___y_710_;
v___y_686_ = v___y_711_;
v___y_687_ = v___y_715_;
v___y_688_ = v___y_714_;
v___y_689_ = v_val_717_;
goto v___jp_681_;
}
}
v___jp_718_:
{
lean_object* v_toCold_721_; lean_object* v_ref_722_; uint8_t v_suppressElabErrors_723_; lean_object* v___x_724_; lean_object* v___f_725_; lean_object* v_ref_726_; lean_object* v___x_727_; 
v_toCold_721_ = lean_ctor_get(v___y_641_, 0);
v_ref_722_ = lean_ctor_get(v___y_641_, 2);
v_suppressElabErrors_723_ = lean_ctor_get_uint8(v___y_641_, sizeof(void*)*3 + 2);
v___x_724_ = lean_box(v_suppressElabErrors_723_);
v___f_725_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_725_, 0, v___x_724_);
v_ref_726_ = l_Lean_replaceRef(v_ref_635_, v_ref_722_);
v___x_727_ = l_Lean_Syntax_getPos_x3f(v_ref_726_, v___y_719_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v___x_728_; 
v___x_728_ = lean_unsigned_to_nat(0u);
v___y_709_ = v___f_725_;
v___y_710_ = v_toCold_721_;
v___y_711_ = v_suppressElabErrors_723_;
v___y_712_ = v___y_720_;
v___y_713_ = v_ref_726_;
v___y_714_ = v___y_719_;
v___y_715_ = v___x_728_;
goto v___jp_708_;
}
else
{
lean_object* v_val_729_; 
v_val_729_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_val_729_);
lean_dec_ref_known(v___x_727_, 1);
v___y_709_ = v___f_725_;
v___y_710_ = v_toCold_721_;
v___y_711_ = v_suppressElabErrors_723_;
v___y_712_ = v___y_720_;
v___y_713_ = v_ref_726_;
v___y_714_ = v___y_719_;
v___y_715_ = v_val_729_;
goto v___jp_708_;
}
}
v___jp_731_:
{
uint8_t v___x_733_; uint8_t v___x_734_; 
v___x_733_ = 1;
v___x_734_ = l_Lean_instBEqMessageSeverity_beq(v_severity_637_, v___x_733_);
if (v___x_734_ == 0)
{
v___y_719_ = v___y_732_;
v___y_720_ = v_severity_637_;
goto v___jp_718_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_735_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_641_);
v___x_736_ = l_Lean_warningAsError;
v___x_737_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_735_, v___x_736_);
lean_dec_ref(v___x_735_);
if (v___x_737_ == 0)
{
v___y_719_ = v___y_732_;
v___y_720_ = v_severity_637_;
goto v___jp_718_;
}
else
{
v___y_719_ = v___y_732_;
v___y_720_ = v___x_730_;
goto v___jp_718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_742_, lean_object* v_msgData_743_, lean_object* v_severity_744_, lean_object* v_isSilent_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
uint8_t v_severity_boxed_751_; uint8_t v_isSilent_boxed_752_; lean_object* v_res_753_; 
v_severity_boxed_751_ = lean_unbox(v_severity_744_);
v_isSilent_boxed_752_ = lean_unbox(v_isSilent_745_);
v_res_753_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_742_, v_msgData_743_, v_severity_boxed_751_, v_isSilent_boxed_752_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v_ref_742_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object* v_msgData_754_, uint8_t v_severity_755_, uint8_t v_isSilent_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_ref_762_; lean_object* v___x_763_; 
v_ref_762_ = lean_ctor_get(v___y_759_, 2);
v___x_763_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_762_, v_msgData_754_, v_severity_755_, v_isSilent_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object* v_msgData_764_, lean_object* v_severity_765_, lean_object* v_isSilent_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
uint8_t v_severity_boxed_772_; uint8_t v_isSilent_boxed_773_; lean_object* v_res_774_; 
v_severity_boxed_772_ = lean_unbox(v_severity_765_);
v_isSilent_boxed_773_ = lean_unbox(v_isSilent_766_);
v_res_774_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_764_, v_severity_boxed_772_, v_isSilent_boxed_773_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object* v_msgData_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
uint8_t v___x_781_; uint8_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = 1;
v___x_782_ = 0;
v___x_783_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_775_, v___x_781_, v___x_782_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object* v_msgData_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v_msgData_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_790_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0));
v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
if (lean_obj_tag(v_a_794_) == 0)
{
lean_object* v___x_796_; 
v___x_796_ = l_List_reverse___redArg(v_a_795_);
return v___x_796_;
}
else
{
lean_object* v_head_797_; lean_object* v_tail_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_811_; 
v_head_797_ = lean_ctor_get(v_a_794_, 0);
v_tail_798_ = lean_ctor_get(v_a_794_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_a_794_);
if (v_isSharedCheck_811_ == 0)
{
v___x_800_ = v_a_794_;
v_isShared_801_ = v_isSharedCheck_811_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_tail_798_);
lean_inc(v_head_797_);
lean_dec(v_a_794_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_811_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint8_t v_minIndexable_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v_minIndexable_802_ = 0;
v___x_803_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_804_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_797_, v_minIndexable_802_);
lean_dec(v_head_797_);
v___x_805_ = l_Lean_stringToMessageData(v___x_804_);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_803_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v_a_795_);
lean_ctor_set(v___x_800_, 0, v___x_806_);
v___x_808_ = v___x_800_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_a_795_);
v___x_808_ = v_reuseFailAlloc_810_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
v_a_794_ = v_tail_798_;
v_a_795_ = v___x_808_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
if (lean_obj_tag(v_a_812_) == 0)
{
lean_object* v___x_814_; 
v___x_814_ = l_List_reverse___redArg(v_a_813_);
return v___x_814_;
}
else
{
lean_object* v_head_815_; lean_object* v_tail_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
v_head_815_ = lean_ctor_get(v_a_812_, 0);
v_tail_816_ = lean_ctor_get(v_a_812_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_a_812_);
if (v_isSharedCheck_824_ == 0)
{
v___x_818_ = v_a_812_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_tail_816_);
lean_inc(v_head_815_);
lean_dec(v_a_812_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v_a_813_);
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_head_815_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_a_813_);
v___x_821_ = v_reuseFailAlloc_823_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
v_a_812_ = v_tail_816_;
v_a_813_ = v___x_821_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0));
v___x_827_ = l_Lean_stringToMessageData(v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2));
v___x_830_ = l_Lean_stringToMessageData(v___x_829_);
return v___x_830_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4));
v___x_833_ = l_Lean_stringToMessageData(v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object* v_s_834_, lean_object* v_declName_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_kinds_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v_ks_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_inc(v_declName_835_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v_declName_835_);
v___x_867_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_834_, v___x_866_);
lean_dec_ref_known(v___x_866_, 1);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_dec(v_declName_835_);
v___x_868_ = lean_box(0);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
else
{
lean_object* v_head_870_; lean_object* v_tail_871_; uint8_t v_minIndexable_872_; uint8_t v_gen_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; 
v_head_870_ = lean_ctor_get(v___x_867_, 0);
v_tail_871_ = lean_ctor_get(v___x_867_, 1);
v_minIndexable_872_ = 0;
if (lean_obj_tag(v_tail_871_) == 0)
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_893_; 
lean_inc(v_head_870_);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; lean_object* v_unused_895_; 
v_unused_894_ = lean_ctor_get(v___x_867_, 1);
lean_dec(v_unused_894_);
v_unused_895_ = lean_ctor_get(v___x_867_, 0);
lean_dec(v_unused_895_);
v___x_885_ = v___x_867_;
v_isShared_886_ = v_isSharedCheck_893_;
goto v_resetjp_884_;
}
else
{
lean_dec(v___x_867_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_893_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_887_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_888_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_870_, v_minIndexable_872_);
lean_dec(v_head_870_);
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 7);
lean_ctor_set(v___x_885_, 1, v___x_889_);
lean_ctor_set(v___x_885_, 0, v___x_887_);
v___x_891_ = v___x_885_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
v_kinds_842_ = v___x_891_;
v___y_843_ = v_a_836_;
v___y_844_ = v_a_837_;
v___y_845_ = v_a_838_;
v___y_846_ = v_a_839_;
goto v___jp_841_;
}
}
}
else
{
lean_object* v_head_896_; 
v_head_896_ = lean_ctor_get(v_tail_871_, 0);
switch(lean_obj_tag(v_head_896_))
{
case 1:
{
lean_object* v_tail_897_; 
v_tail_897_ = lean_ctor_get(v_tail_871_, 1);
if (lean_obj_tag(v_tail_897_) == 0)
{
if (lean_obj_tag(v_head_870_) == 0)
{
uint8_t v_gen_898_; 
lean_inc_ref(v_head_870_);
lean_dec_ref_known(v___x_867_, 2);
v_gen_898_ = lean_ctor_get_uint8(v_head_870_, 0);
lean_dec_ref_known(v_head_870_, 0);
v_gen_874_ = v_gen_898_;
v___y_875_ = v_a_836_;
v___y_876_ = v_a_837_;
v___y_877_ = v_a_838_;
v___y_878_ = v_a_839_;
goto v___jp_873_;
}
else
{
v_ks_857_ = v___x_867_;
v___y_858_ = v_a_836_;
v___y_859_ = v_a_837_;
v___y_860_ = v_a_838_;
v___y_861_ = v_a_839_;
goto v___jp_856_;
}
}
else
{
v_ks_857_ = v___x_867_;
v___y_858_ = v_a_836_;
v___y_859_ = v_a_837_;
v___y_860_ = v_a_838_;
v___y_861_ = v_a_839_;
goto v___jp_856_;
}
}
case 0:
{
lean_object* v_tail_899_; 
v_tail_899_ = lean_ctor_get(v_tail_871_, 1);
if (lean_obj_tag(v_tail_899_) == 0)
{
if (lean_obj_tag(v_head_870_) == 1)
{
uint8_t v_gen_900_; 
lean_inc_ref(v_head_870_);
lean_dec_ref_known(v___x_867_, 2);
v_gen_900_ = lean_ctor_get_uint8(v_head_870_, 0);
lean_dec_ref_known(v_head_870_, 0);
v_gen_874_ = v_gen_900_;
v___y_875_ = v_a_836_;
v___y_876_ = v_a_837_;
v___y_877_ = v_a_838_;
v___y_878_ = v_a_839_;
goto v___jp_873_;
}
else
{
v_ks_857_ = v___x_867_;
v___y_858_ = v_a_836_;
v___y_859_ = v_a_837_;
v___y_860_ = v_a_838_;
v___y_861_ = v_a_839_;
goto v___jp_856_;
}
}
else
{
v_ks_857_ = v___x_867_;
v___y_858_ = v_a_836_;
v___y_859_ = v_a_837_;
v___y_860_ = v_a_838_;
v___y_861_ = v_a_839_;
goto v___jp_856_;
}
}
default: 
{
v_ks_857_ = v___x_867_;
v___y_858_ = v_a_836_;
v___y_859_ = v_a_837_;
v___y_860_ = v_a_838_;
v___y_861_ = v_a_839_;
goto v___jp_856_;
}
}
}
v___jp_873_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_879_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_880_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_880_, 0, v_gen_874_);
v___x_881_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v___x_880_, v_minIndexable_872_);
lean_dec_ref_known(v___x_880_, 0);
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_879_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v_kinds_842_ = v___x_883_;
v___y_843_ = v___y_875_;
v___y_844_ = v___y_876_;
v___y_845_ = v___y_877_;
v___y_846_ = v___y_878_;
goto v___jp_841_;
}
}
v___jp_841_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_847_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1);
v___x_848_ = l_Lean_MessageData_ofName(v_declName_835_);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
lean_ctor_set(v___x_852_, 1, v_kinds_842_);
v___x_853_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v___x_854_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
return v___x_855_;
}
v___jp_856_:
{
lean_object* v___x_862_; lean_object* v_ks_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_862_ = lean_box(0);
v_ks_863_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(v_ks_857_, v___x_862_);
v___x_864_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(v_ks_863_, v___x_862_);
v___x_865_ = l_Lean_MessageData_ofList(v___x_864_);
v_kinds_842_ = v___x_865_;
v___y_843_ = v___y_858_;
v___y_844_ = v___y_859_;
v___y_845_ = v___y_860_;
v___y_846_ = v___y_861_;
goto v___jp_841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object* v_s_901_, lean_object* v_declName_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_s_901_, v_declName_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec_ref(v_s_901_);
return v_res_908_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_909_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_912_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_913_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
lean_ctor_set(v___x_915_, 2, v___x_914_);
lean_ctor_set(v___x_915_, 3, v___x_914_);
lean_ctor_set(v___x_915_, 4, v___x_913_);
lean_ctor_set(v___x_915_, 5, v___x_913_);
lean_ctor_set(v___x_915_, 6, v___x_913_);
lean_ctor_set(v___x_915_, 7, v___x_913_);
lean_ctor_set(v___x_915_, 8, v___x_913_);
lean_ctor_set(v___x_915_, 9, v___x_913_);
lean_ctor_set(v___x_915_, 10, v___x_913_);
lean_ctor_set(v___x_915_, 11, v___x_912_);
return v___x_915_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_unsigned_to_nat(32u);
v___x_917_ = lean_mk_empty_array_with_capacity(v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_919_ = ((size_t)5ULL);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_unsigned_to_nat(32u);
v___x_922_ = lean_mk_empty_array_with_capacity(v___x_921_);
v___x_923_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3);
v___x_924_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_922_);
lean_ctor_set(v___x_924_, 2, v___x_920_);
lean_ctor_set(v___x_924_, 3, v___x_920_);
lean_ctor_set_usize(v___x_924_, 4, v___x_919_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_925_ = lean_box(1);
v___x_926_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4);
v___x_927_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_928_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___x_926_);
lean_ctor_set(v___x_928_, 2, v___x_925_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object* v_msgData_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; lean_object* v_toCold_934_; lean_object* v_env_935_; lean_object* v_options_936_; uint8_t v___x_937_; lean_object* v_env_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_933_ = lean_st_ref_get(v___y_931_);
v_toCold_934_ = lean_ctor_get(v___y_930_, 0);
v_env_935_ = lean_ctor_get(v___x_933_, 0);
lean_inc_ref(v_env_935_);
lean_dec(v___x_933_);
v_options_936_ = lean_ctor_get(v_toCold_934_, 2);
v___x_937_ = 0;
v_env_938_ = l_Lean_Environment_setRecordingDeps(v_env_935_, v___x_937_);
v___x_939_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_940_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_936_);
v___x_941_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_941_, 0, v_env_938_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
lean_ctor_set(v___x_941_, 2, v___x_940_);
lean_ctor_set(v___x_941_, 3, v_options_936_);
v___x_942_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v_msgData_929_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object* v_msgData_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msgData_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object* v_msg_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_ref_953_; lean_object* v___x_954_; lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_963_; 
v_ref_953_ = lean_ctor_get(v___y_950_, 2);
v___x_954_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msg_949_, v___y_950_, v___y_951_);
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_963_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
lean_inc(v_ref_953_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v_ref_953_);
lean_ctor_set(v___x_959_, 1, v_a_955_);
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 1);
lean_ctor_set(v___x_957_, 0, v___x_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object* v_msg_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_968_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object* v_s_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_986_; lean_object* v_env_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_986_ = lean_st_ref_get(v_a_984_);
v_env_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc_ref(v_env_987_);
lean_dec(v___x_986_);
v___x_988_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
v___x_989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5));
lean_inc_ref(v_s_982_);
v___x_990_ = l_Lean_Parser_runParserCategory(v_env_987_, v___x_988_, v_s_982_, v___x_989_);
if (lean_obj_tag(v___x_990_) == 1)
{
lean_object* v_a_991_; lean_object* v___x_992_; 
lean_dec_ref(v_s_982_);
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = l_Lean_Meta_Grind_getAttrKindCore(v_a_991_, v_a_983_, v_a_984_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec_ref(v___x_990_);
v___x_993_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7);
v___x_994_ = l_Lean_stringToMessageData(v_s_982_);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_995_, v_a_983_, v_a_984_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object* v_s_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(v_s_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object* v_00_u03b1_1002_, lean_object* v_msg_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_1003_, v___y_1004_, v___y_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object* v_00_u03b1_1008_, lean_object* v_msg_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(v_00_u03b1_1008_, v_msg_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object* v_msg_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_ref_1020_; lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_ref_1020_ = lean_ctor_get(v___y_1017_, 2);
v___x_1021_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_inc(v_ref_1020_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_ref_1020_);
lean_ctor_set(v___x_1026_, 1, v_a_1022_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 1);
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object* v_msg_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0));
v___x_1040_ = l_Lean_stringToMessageData(v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t v_minIndexable_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
if (v_minIndexable_1041_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1);
v___x_1050_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1049_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object* v_minIndexable_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
uint8_t v_minIndexable_boxed_1057_; lean_object* v_res_1058_; 
v_minIndexable_boxed_1057_ = lean_unbox(v_minIndexable_1051_);
v_res_1058_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_boxed_1057_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object* v_00_u03b1_1059_, lean_object* v_msg_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object* v_00_u03b1_1067_, lean_object* v_msg_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(v_00_u03b1_1067_, v_msg_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1074_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_1080_ = l_Lean_stringToMessageData(v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1096_, lean_object* v_declHint_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v_env_1102_; uint8_t v___x_1103_; 
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_st_ref_get(v___y_1098_);
v_env_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc_ref(v_env_1102_);
lean_dec(v___x_1101_);
v___x_1103_ = l_Lean_Name_isAnonymous(v_declHint_1097_);
if (v___x_1103_ == 0)
{
uint8_t v_isExporting_1104_; 
v_isExporting_1104_ = lean_ctor_get_uint8(v_env_1102_, sizeof(void*)*13);
if (v_isExporting_1104_ == 0)
{
lean_object* v___x_1105_; 
lean_dec_ref(v_env_1102_);
lean_dec(v_declHint_1097_);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v_msg_1096_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
lean_inc_ref(v_env_1102_);
v___x_1106_ = l_Lean_Environment_setExporting(v_env_1102_, v___x_1103_);
lean_inc(v_declHint_1097_);
lean_inc_ref(v___x_1106_);
v___x_1107_ = l_Lean_Environment_contains(v___x_1106_, v_declHint_1097_, v_isExporting_1104_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; 
lean_dec_ref(v___x_1106_);
lean_dec_ref(v_env_1102_);
lean_dec(v_declHint_1097_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_msg_1096_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v_c_1114_; lean_object* v___x_1115_; 
v___x_1109_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_1110_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
v___x_1111_ = l_Lean_Options_empty;
v___x_1112_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1106_);
lean_ctor_set(v___x_1112_, 1, v___x_1109_);
lean_ctor_set(v___x_1112_, 2, v___x_1110_);
lean_ctor_set(v___x_1112_, 3, v___x_1111_);
lean_inc(v_declHint_1097_);
v___x_1113_ = l_Lean_MessageData_ofConstName(v_declHint_1097_, v___x_1103_);
v_c_1114_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1114_, 0, v___x_1112_);
lean_ctor_set(v_c_1114_, 1, v___x_1113_);
v___x_1115_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1102_, v_declHint_1097_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec_ref(v_env_1102_);
lean_dec(v_declHint_1097_);
v___x_1116_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_c_1114_);
v___x_1118_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = l_Lean_MessageData_note(v___x_1119_);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_msg_1096_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
return v___x_1122_;
}
else
{
lean_object* v_val_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1157_; 
v_val_1123_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1125_ = v___x_1115_;
v_isShared_1126_ = v_isSharedCheck_1157_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_val_1123_);
lean_dec(v___x_1115_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1157_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v_moduleNames_1128_; lean_object* v_mod_1129_; uint8_t v___x_1130_; 
v___x_1127_ = l_Lean_Environment_header(v_env_1102_);
lean_dec_ref(v_env_1102_);
v_moduleNames_1128_ = lean_ctor_get(v___x_1127_, 4);
lean_inc_ref(v_moduleNames_1128_);
lean_dec_ref(v___x_1127_);
v_mod_1129_ = lean_array_get(v___x_1100_, v_moduleNames_1128_, v_val_1123_);
lean_dec(v_val_1123_);
lean_dec_ref(v_moduleNames_1128_);
v___x_1130_ = l_Lean_isPrivateName(v_declHint_1097_);
lean_dec(v_declHint_1097_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v_c_1114_);
v___x_1133_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_MessageData_ofName(v_mod_1129_);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_MessageData_note(v___x_1138_);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_msg_1096_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1140_);
v___x_1142_ = v___x_1125_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v_c_1114_);
v___x_1146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = l_Lean_MessageData_ofName(v_mod_1129_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_MessageData_note(v___x_1151_);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_msg_1096_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1153_);
v___x_1155_ = v___x_1125_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1158_; 
lean_dec_ref(v_env_1102_);
lean_dec(v_declHint_1097_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_msg_1096_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1159_, lean_object* v_declHint_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1159_, v_declHint_1160_, v___y_1161_);
lean_dec(v___y_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1164_, lean_object* v_declHint_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1181_; 
v___x_1171_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1164_, v_declHint_1165_, v___y_1169_);
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1176_ = l_Lean_unknownIdentifierMessageTag;
v___x_1177_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v_a_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1177_);
v___x_1179_ = v___x_1174_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1182_, lean_object* v_declHint_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1182_, v_declHint_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1190_, lean_object* v_msg_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_toCold_1197_; lean_object* v_currRecDepth_1198_; lean_object* v_ref_1199_; uint16_t v_optionFlags_1200_; uint8_t v_suppressElabErrors_1201_; uint8_t v_isRecordingDeps_1202_; lean_object* v_ref_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_toCold_1197_ = lean_ctor_get(v___y_1194_, 0);
v_currRecDepth_1198_ = lean_ctor_get(v___y_1194_, 1);
v_ref_1199_ = lean_ctor_get(v___y_1194_, 2);
v_optionFlags_1200_ = lean_ctor_get_uint16(v___y_1194_, sizeof(void*)*3);
v_suppressElabErrors_1201_ = lean_ctor_get_uint8(v___y_1194_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1202_ = lean_ctor_get_uint8(v___y_1194_, sizeof(void*)*3 + 3);
v_ref_1203_ = l_Lean_replaceRef(v_ref_1190_, v_ref_1199_);
lean_inc(v_currRecDepth_1198_);
lean_inc_ref(v_toCold_1197_);
v___x_1204_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1204_, 0, v_toCold_1197_);
lean_ctor_set(v___x_1204_, 1, v_currRecDepth_1198_);
lean_ctor_set(v___x_1204_, 2, v_ref_1203_);
lean_ctor_set_uint16(v___x_1204_, sizeof(void*)*3, v_optionFlags_1200_);
lean_ctor_set_uint8(v___x_1204_, sizeof(void*)*3 + 2, v_suppressElabErrors_1201_);
lean_ctor_set_uint8(v___x_1204_, sizeof(void*)*3 + 3, v_isRecordingDeps_1202_);
v___x_1205_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1191_, v___y_1192_, v___y_1193_, v___x_1204_, v___y_1195_);
lean_dec_ref_known(v___x_1204_, 3);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1206_, lean_object* v_msg_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1206_, v_msg_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v_ref_1206_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1214_, lean_object* v_msg_1215_, lean_object* v_declHint_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; lean_object* v_a_1223_; lean_object* v___x_1224_; 
v___x_1222_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1215_, v_declHint_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref(v___x_1222_);
v___x_1224_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1214_, v_a_1223_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1225_, lean_object* v_msg_1226_, lean_object* v_declHint_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1225_, v_msg_1226_, v_declHint_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v_ref_1225_);
return v_res_1233_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1236_ = l_Lean_stringToMessageData(v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1237_, lean_object* v_constName_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1244_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1245_ = 0;
lean_inc(v_constName_1238_);
v___x_1246_ = l_Lean_MessageData_ofConstName(v_constName_1238_, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1244_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1237_, v___x_1249_, v_constName_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1251_, lean_object* v_constName_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1251_, v_constName_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v_ref_1251_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_constName_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_ref_1265_; lean_object* v___x_1266_; 
v_ref_1265_ = lean_ctor_get(v___y_1262_, 2);
v___x_1266_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1265_, v_constName_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* v_constName_1274_, uint8_t v_skipRealize_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; lean_object* v_env_1282_; lean_object* v___x_1283_; 
v___x_1281_ = lean_st_ref_get(v___y_1279_);
v_env_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc_ref(v_env_1282_);
lean_dec(v___x_1281_);
lean_inc(v_constName_1274_);
v___x_1283_ = l_Lean_Environment_findAsync_x3f(v_env_1282_, v_constName_1274_, v_skipRealize_1275_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1274_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1284_;
}
else
{
lean_object* v_val_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_constName_1274_);
v_val_1285_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1283_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_val_1285_);
lean_dec(v___x_1283_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set_tag(v___x_1287_, 0);
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_val_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* v_constName_1293_, lean_object* v_skipRealize_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v_skipRealize_boxed_1300_; lean_object* v_res_1301_; 
v_skipRealize_boxed_1300_ = lean_unbox(v_skipRealize_1294_);
v_res_1301_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1293_, v_skipRealize_boxed_1300_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* v_declName_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v_env_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1305_ = lean_st_ref_get(v___y_1303_);
v_env_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc_ref(v_env_1306_);
lean_dec(v___x_1305_);
v___x_1307_ = l_Lean_getReducibilityStatusCore(v_env_1306_, v_declName_1302_);
v___x_1308_ = lean_box(v___x_1307_);
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_declName_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1310_, v___y_1311_);
lean_dec(v___y_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* v_declName_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1336_; 
v___x_1320_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1314_, v___y_1318_);
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1336_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1336_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_unbox(v_a_1321_);
lean_dec(v_a_1321_);
if (v___x_1325_ == 0)
{
uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1326_ = 1;
v___x_1327_ = lean_box(v___x_1326_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1327_);
v___x_1329_ = v___x_1323_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
else
{
uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1331_ = 0;
v___x_1332_ = lean_box(v___x_1331_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1332_);
v___x_1334_ = v___x_1323_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* v_declName_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1343_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
v___x_1349_ = l_Lean_stringToMessageData(v___x_1348_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
v___x_1355_ = l_Lean_stringToMessageData(v___x_1354_);
return v___x_1355_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
v___x_1358_ = l_Lean_stringToMessageData(v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* v_params_1359_, lean_object* v_id_1360_, lean_object* v_declName_1361_, lean_object* v_kind_1362_, uint8_t v_minIndexable_1363_, uint8_t v_suggest_1364_, uint8_t v_warn_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v___y_1372_; lean_object* v_thm_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; uint8_t v___x_1427_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___x_1624_; 
v___x_1427_ = 0;
lean_inc(v_declName_1361_);
v___x_1624_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1361_, v___x_1427_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; uint8_t v_kind_1626_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v_kind_1626_ = lean_ctor_get_uint8(v_a_1625_, sizeof(void*)*3);
lean_dec(v_a_1625_);
switch(v_kind_1626_)
{
case 1:
{
v___y_1555_ = v_a_1366_;
v___y_1556_ = v_a_1367_;
v___y_1557_ = v_a_1368_;
v___y_1558_ = v_a_1369_;
goto v___jp_1554_;
}
case 2:
{
v___y_1555_ = v_a_1366_;
v___y_1556_ = v_a_1367_;
v___y_1557_ = v_a_1368_;
v___y_1558_ = v_a_1369_;
goto v___jp_1554_;
}
case 6:
{
v___y_1555_ = v_a_1366_;
v___y_1556_ = v_a_1367_;
v___y_1557_ = v_a_1368_;
v___y_1558_ = v_a_1369_;
goto v___jp_1554_;
}
case 0:
{
lean_object* v___x_1627_; 
lean_dec(v_id_1360_);
lean_inc(v_declName_1361_);
v___x_1627_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1361_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; uint8_t v___x_1629_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1627_, 1);
v___x_1629_ = lean_unbox(v_a_1628_);
lean_dec(v_a_1628_);
if (v___x_1629_ == 0)
{
v___y_1485_ = v_a_1366_;
v___y_1486_ = v_a_1367_;
v___y_1487_ = v_a_1368_;
v___y_1488_ = v_a_1369_;
goto v___jp_1484_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_kind_1362_);
lean_dec_ref(v_params_1359_);
v___x_1630_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1631_ = l_Lean_MessageData_ofConstName(v_declName_1361_, v___x_1427_);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1634_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v_kind_1362_);
lean_dec(v_declName_1361_);
lean_dec_ref(v_params_1359_);
v_a_1644_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1627_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1627_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
default: 
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec(v_kind_1362_);
lean_dec(v_id_1360_);
lean_dec_ref(v_params_1359_);
v___x_1652_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1653_ = l_Lean_MessageData_ofConstName(v_declName_1361_, v___x_1427_);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1656_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
return v___x_1657_;
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_kind_1362_);
lean_dec(v_declName_1361_);
lean_dec(v_id_1360_);
lean_dec_ref(v_params_1359_);
v_a_1658_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1624_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1624_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
v___jp_1371_:
{
lean_object* v_config_1373_; lean_object* v_extensions_1374_; lean_object* v_extra_1375_; lean_object* v_extraInj_1376_; lean_object* v_extraFacts_1377_; lean_object* v_symPrios_1378_; lean_object* v_norm_1379_; lean_object* v_normProcs_1380_; lean_object* v_anchorRefs_x3f_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1390_; 
v_config_1373_ = lean_ctor_get(v_params_1359_, 0);
v_extensions_1374_ = lean_ctor_get(v_params_1359_, 1);
v_extra_1375_ = lean_ctor_get(v_params_1359_, 2);
v_extraInj_1376_ = lean_ctor_get(v_params_1359_, 3);
v_extraFacts_1377_ = lean_ctor_get(v_params_1359_, 4);
v_symPrios_1378_ = lean_ctor_get(v_params_1359_, 5);
v_norm_1379_ = lean_ctor_get(v_params_1359_, 6);
v_normProcs_1380_ = lean_ctor_get(v_params_1359_, 7);
v_anchorRefs_x3f_1381_ = lean_ctor_get(v_params_1359_, 8);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_params_1359_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1383_ = v_params_1359_;
v_isShared_1384_ = v_isSharedCheck_1390_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_anchorRefs_x3f_1381_);
lean_inc(v_normProcs_1380_);
lean_inc(v_norm_1379_);
lean_inc(v_symPrios_1378_);
lean_inc(v_extraFacts_1377_);
lean_inc(v_extraInj_1376_);
lean_inc(v_extra_1375_);
lean_inc(v_extensions_1374_);
lean_inc(v_config_1373_);
lean_dec(v_params_1359_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1390_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = l_Lean_PersistentArray_push___redArg(v_extra_1375_, v___y_1372_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 2, v___x_1385_);
v___x_1387_ = v___x_1383_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_config_1373_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_extensions_1374_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v_extraInj_1376_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v_extraFacts_1377_);
lean_ctor_set(v_reuseFailAlloc_1389_, 5, v_symPrios_1378_);
lean_ctor_set(v_reuseFailAlloc_1389_, 6, v_norm_1379_);
lean_ctor_set(v_reuseFailAlloc_1389_, 7, v_normProcs_1380_);
lean_ctor_set(v_reuseFailAlloc_1389_, 8, v_anchorRefs_x3f_1381_);
v___x_1387_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
}
}
v___jp_1391_:
{
if (v_warn_1365_ == 0)
{
lean_dec(v_declName_1361_);
v___y_1372_ = v_thm_1392_;
goto v___jp_1371_;
}
else
{
lean_object* v_extensions_1397_; lean_object* v_patterns_1398_; lean_object* v_origin_1399_; lean_object* v_cnstrs_1400_; uint8_t v___x_1401_; 
v_extensions_1397_ = lean_ctor_get(v_params_1359_, 1);
v_patterns_1398_ = lean_ctor_get(v_thm_1392_, 3);
v_origin_1399_ = lean_ctor_get(v_thm_1392_, 5);
v_cnstrs_1400_ = lean_ctor_get(v_thm_1392_, 7);
v___x_1401_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1397_, v_origin_1399_, v_patterns_1398_, v_cnstrs_1400_);
if (v___x_1401_ == 0)
{
lean_dec(v_declName_1361_);
v___y_1372_ = v_thm_1392_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1402_; 
v___x_1402_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1397_, v_declName_1361_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_dec_ref_known(v___x_1402_, 1);
v___y_1372_ = v_thm_1392_;
goto v___jp_1371_;
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec_ref(v_thm_1392_);
lean_dec_ref(v_params_1359_);
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
}
v___jp_1411_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1423_ = l_Lean_PersistentArray_push___redArg(v___y_1421_, v___y_1415_);
v___x_1424_ = l_Lean_PersistentArray_push___redArg(v___x_1423_, v___y_1417_);
v___x_1425_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1425_, 0, v___y_1422_);
lean_ctor_set(v___x_1425_, 1, v___y_1416_);
lean_ctor_set(v___x_1425_, 2, v___x_1424_);
lean_ctor_set(v___x_1425_, 3, v___y_1418_);
lean_ctor_set(v___x_1425_, 4, v___y_1419_);
lean_ctor_set(v___x_1425_, 5, v___y_1420_);
lean_ctor_set(v___x_1425_, 6, v___y_1413_);
lean_ctor_set(v___x_1425_, 7, v___y_1412_);
lean_ctor_set(v___x_1425_, 8, v___y_1414_);
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
v___jp_1428_:
{
lean_object* v___x_1433_; 
v___x_1433_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1363_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1434_; 
lean_dec_ref_known(v___x_1433_, 1);
lean_inc(v_declName_1361_);
v___x_1434_ = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(v_declName_1361_, v___x_1427_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1467_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1467_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1467_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
if (lean_obj_tag(v_a_1435_) == 1)
{
lean_object* v_val_1439_; lean_object* v_config_1440_; lean_object* v_extensions_1441_; lean_object* v_extra_1442_; lean_object* v_extraInj_1443_; lean_object* v_extraFacts_1444_; lean_object* v_symPrios_1445_; lean_object* v_norm_1446_; lean_object* v_normProcs_1447_; lean_object* v_anchorRefs_x3f_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_declName_1361_);
v_val_1439_ = lean_ctor_get(v_a_1435_, 0);
lean_inc(v_val_1439_);
lean_dec_ref_known(v_a_1435_, 1);
v_config_1440_ = lean_ctor_get(v_params_1359_, 0);
v_extensions_1441_ = lean_ctor_get(v_params_1359_, 1);
v_extra_1442_ = lean_ctor_get(v_params_1359_, 2);
v_extraInj_1443_ = lean_ctor_get(v_params_1359_, 3);
v_extraFacts_1444_ = lean_ctor_get(v_params_1359_, 4);
v_symPrios_1445_ = lean_ctor_get(v_params_1359_, 5);
v_norm_1446_ = lean_ctor_get(v_params_1359_, 6);
v_normProcs_1447_ = lean_ctor_get(v_params_1359_, 7);
v_anchorRefs_x3f_1448_ = lean_ctor_get(v_params_1359_, 8);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_params_1359_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1450_ = v_params_1359_;
v_isShared_1451_ = v_isSharedCheck_1460_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_anchorRefs_x3f_1448_);
lean_inc(v_normProcs_1447_);
lean_inc(v_norm_1446_);
lean_inc(v_symPrios_1445_);
lean_inc(v_extraFacts_1444_);
lean_inc(v_extraInj_1443_);
lean_inc(v_extra_1442_);
lean_inc(v_extensions_1441_);
lean_inc(v_config_1440_);
lean_dec(v_params_1359_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1460_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1452_ = l_Lean_Array_toPArray_x27___redArg(v_val_1439_);
lean_dec(v_val_1439_);
v___x_1453_ = l_Lean_PersistentArray_append___redArg(v_extra_1442_, v___x_1452_);
lean_dec_ref(v___x_1452_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 2, v___x_1453_);
v___x_1455_ = v___x_1450_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_config_1440_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_extensions_1441_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v_extraInj_1443_);
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v_extraFacts_1444_);
lean_ctor_set(v_reuseFailAlloc_1459_, 5, v_symPrios_1445_);
lean_ctor_set(v_reuseFailAlloc_1459_, 6, v_norm_1446_);
lean_ctor_set(v_reuseFailAlloc_1459_, 7, v_normProcs_1447_);
lean_ctor_set(v_reuseFailAlloc_1459_, 8, v_anchorRefs_x3f_1448_);
v___x_1455_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1457_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1455_);
v___x_1457_ = v___x_1437_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
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
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_del_object(v___x_1437_);
lean_dec(v_a_1435_);
lean_dec_ref(v_params_1359_);
v___x_1461_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__1, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
v___x_1462_ = l_Lean_MessageData_ofConstName(v_declName_1361_, v___x_1427_);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1465_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
return v___x_1466_;
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_declName_1361_);
lean_dec_ref(v_params_1359_);
v_a_1468_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1434_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1434_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec(v_declName_1361_);
lean_dec_ref(v_params_1359_);
v_a_1476_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1433_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1433_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
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
v___jp_1484_:
{
uint8_t v___x_1489_; 
v___x_1489_ = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(v_kind_1362_);
if (v___x_1489_ == 0)
{
uint8_t v___x_1490_; 
v___x_1490_ = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(v_kind_1362_);
lean_dec(v_kind_1362_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec_ref(v_params_1359_);
v___x_1491_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1492_ = l_Lean_MessageData_ofConstName(v_declName_1361_, v___x_1427_);
v___x_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1491_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__5, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1495_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
else
{
v___y_1429_ = v___y_1485_;
v___y_1430_ = v___y_1486_;
v___y_1431_ = v___y_1487_;
v___y_1432_ = v___y_1488_;
goto v___jp_1428_;
}
}
else
{
lean_dec(v_kind_1362_);
v___y_1429_ = v___y_1485_;
v___y_1430_ = v___y_1486_;
v___y_1431_ = v___y_1487_;
v___y_1432_ = v___y_1488_;
goto v___jp_1428_;
}
}
v___jp_1505_:
{
lean_object* v_symPrios_1510_; lean_object* v___x_1511_; 
v_symPrios_1510_ = lean_ctor_get(v_params_1359_, 5);
lean_inc_ref(v_symPrios_1510_);
lean_inc(v_declName_1361_);
v___x_1511_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1361_, v_kind_1362_, v_symPrios_1510_, v___x_1427_, v_minIndexable_1363_, v___y_1506_, v___y_1508_, v___y_1507_, v___y_1509_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v_thm_1392_ = v_a_1512_;
v___y_1393_ = v___y_1506_;
v___y_1394_ = v___y_1508_;
v___y_1395_ = v___y_1507_;
v___y_1396_ = v___y_1509_;
goto v___jp_1391_;
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_declName_1361_);
lean_dec_ref(v_params_1359_);
v_a_1513_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1511_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1511_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
v___jp_1521_:
{
if (v_suggest_1364_ == 0)
{
lean_dec(v_id_1360_);
v___y_1506_ = v___y_1522_;
v___y_1507_ = v___y_1524_;
v___y_1508_ = v___y_1523_;
v___y_1509_ = v___y_1525_;
goto v___jp_1505_;
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1526_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1524_);
v___x_1527_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1528_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_1526_, v___x_1527_);
lean_dec_ref(v___x_1526_);
if (v___x_1528_ == 0)
{
lean_object* v_symPrios_1529_; lean_object* v___x_1530_; 
lean_dec(v_kind_1362_);
v_symPrios_1529_ = lean_ctor_get(v_params_1359_, 5);
lean_inc_ref(v_symPrios_1529_);
lean_inc(v_declName_1361_);
v___x_1530_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1360_, v_declName_1361_, v_symPrios_1529_, v_minIndexable_1363_, v_suggest_1364_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v_thm_1392_ = v_a_1531_;
v___y_1393_ = v___y_1522_;
v___y_1394_ = v___y_1523_;
v___y_1395_ = v___y_1524_;
v___y_1396_ = v___y_1525_;
goto v___jp_1391_;
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_declName_1361_);
lean_dec_ref(v_params_1359_);
v_a_1532_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1530_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1530_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
else
{
lean_dec(v_id_1360_);
v___y_1506_ = v___y_1522_;
v___y_1507_ = v___y_1524_;
v___y_1508_ = v___y_1523_;
v___y_1509_ = v___y_1525_;
goto v___jp_1505_;
}
}
}
v___jp_1540_:
{
lean_object* v___x_1545_; 
v___x_1545_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1363_, v___y_1542_, v___y_1544_, v___y_1541_, v___y_1543_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_dec_ref_known(v___x_1545_, 1);
v___y_1522_ = v___y_1542_;
v___y_1523_ = v___y_1544_;
v___y_1524_ = v___y_1541_;
v___y_1525_ = v___y_1543_;
goto v___jp_1521_;
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_kind_1362_);
lean_dec(v_declName_1361_);
lean_dec(v_id_1360_);
lean_dec_ref(v_params_1359_);
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
}
v___jp_1554_:
{
if (lean_obj_tag(v_kind_1362_) == 2)
{
uint8_t v_gen_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v_id_1360_);
v_gen_1559_ = lean_ctor_get_uint8(v_kind_1362_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_kind_1362_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1561_ = v_kind_1362_;
v_isShared_1562_ = v_isSharedCheck_1623_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v_kind_1362_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1623_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1363_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_config_1564_; lean_object* v_extensions_1565_; lean_object* v_extra_1566_; lean_object* v_extraInj_1567_; lean_object* v_extraFacts_1568_; lean_object* v_symPrios_1569_; lean_object* v_norm_1570_; lean_object* v_normProcs_1571_; lean_object* v_anchorRefs_x3f_1572_; lean_object* v___x_1574_; 
lean_dec_ref_known(v___x_1563_, 1);
v_config_1564_ = lean_ctor_get(v_params_1359_, 0);
lean_inc_ref(v_config_1564_);
v_extensions_1565_ = lean_ctor_get(v_params_1359_, 1);
lean_inc_ref(v_extensions_1565_);
v_extra_1566_ = lean_ctor_get(v_params_1359_, 2);
lean_inc_ref(v_extra_1566_);
v_extraInj_1567_ = lean_ctor_get(v_params_1359_, 3);
lean_inc_ref(v_extraInj_1567_);
v_extraFacts_1568_ = lean_ctor_get(v_params_1359_, 4);
lean_inc_ref(v_extraFacts_1568_);
v_symPrios_1569_ = lean_ctor_get(v_params_1359_, 5);
lean_inc_ref(v_symPrios_1569_);
v_norm_1570_ = lean_ctor_get(v_params_1359_, 6);
lean_inc_ref(v_norm_1570_);
v_normProcs_1571_ = lean_ctor_get(v_params_1359_, 7);
lean_inc_ref(v_normProcs_1571_);
v_anchorRefs_x3f_1572_ = lean_ctor_get(v_params_1359_, 8);
lean_inc(v_anchorRefs_x3f_1572_);
lean_dec_ref(v_params_1359_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set_tag(v___x_1561_, 0);
v___x_1574_ = v___x_1561_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_1614_, 0, v_gen_1559_);
v___x_1574_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; 
lean_inc_ref(v_symPrios_1569_);
lean_inc(v_declName_1361_);
v___x_1575_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1361_, v___x_1574_, v_symPrios_1569_, v___x_1427_, v___x_1427_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v___x_1577_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1577_, 0, v_gen_1559_);
lean_inc_ref(v_symPrios_1569_);
lean_inc(v_declName_1361_);
v___x_1578_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1361_, v___x_1577_, v_symPrios_1569_, v___x_1427_, v___x_1427_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1578_) == 0)
{
if (v_warn_1365_ == 0)
{
lean_object* v_a_1579_; 
lean_dec(v_declName_1361_);
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v___y_1412_ = v_normProcs_1571_;
v___y_1413_ = v_norm_1570_;
v___y_1414_ = v_anchorRefs_x3f_1572_;
v___y_1415_ = v_a_1576_;
v___y_1416_ = v_extensions_1565_;
v___y_1417_ = v_a_1579_;
v___y_1418_ = v_extraInj_1567_;
v___y_1419_ = v_extraFacts_1568_;
v___y_1420_ = v_symPrios_1569_;
v___y_1421_ = v_extra_1566_;
v___y_1422_ = v_config_1564_;
goto v___jp_1411_;
}
else
{
lean_object* v_a_1580_; lean_object* v_patterns_1581_; lean_object* v_origin_1582_; lean_object* v_cnstrs_1583_; uint8_t v___x_1584_; 
v_a_1580_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1578_, 1);
v_patterns_1581_ = lean_ctor_get(v_a_1576_, 3);
v_origin_1582_ = lean_ctor_get(v_a_1576_, 5);
v_cnstrs_1583_ = lean_ctor_get(v_a_1576_, 7);
v___x_1584_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1565_, v_origin_1582_, v_patterns_1581_, v_cnstrs_1583_);
if (v___x_1584_ == 0)
{
lean_dec(v_declName_1361_);
v___y_1412_ = v_normProcs_1571_;
v___y_1413_ = v_norm_1570_;
v___y_1414_ = v_anchorRefs_x3f_1572_;
v___y_1415_ = v_a_1576_;
v___y_1416_ = v_extensions_1565_;
v___y_1417_ = v_a_1580_;
v___y_1418_ = v_extraInj_1567_;
v___y_1419_ = v_extraFacts_1568_;
v___y_1420_ = v_symPrios_1569_;
v___y_1421_ = v_extra_1566_;
v___y_1422_ = v_config_1564_;
goto v___jp_1411_;
}
else
{
lean_object* v_patterns_1585_; lean_object* v_origin_1586_; lean_object* v_cnstrs_1587_; uint8_t v___x_1588_; 
v_patterns_1585_ = lean_ctor_get(v_a_1580_, 3);
v_origin_1586_ = lean_ctor_get(v_a_1580_, 5);
v_cnstrs_1587_ = lean_ctor_get(v_a_1580_, 7);
v___x_1588_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1565_, v_origin_1586_, v_patterns_1585_, v_cnstrs_1587_);
if (v___x_1588_ == 0)
{
lean_dec(v_declName_1361_);
v___y_1412_ = v_normProcs_1571_;
v___y_1413_ = v_norm_1570_;
v___y_1414_ = v_anchorRefs_x3f_1572_;
v___y_1415_ = v_a_1576_;
v___y_1416_ = v_extensions_1565_;
v___y_1417_ = v_a_1580_;
v___y_1418_ = v_extraInj_1567_;
v___y_1419_ = v_extraFacts_1568_;
v___y_1420_ = v_symPrios_1569_;
v___y_1421_ = v_extra_1566_;
v___y_1422_ = v_config_1564_;
goto v___jp_1411_;
}
else
{
lean_object* v___x_1589_; 
v___x_1589_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1565_, v_declName_1361_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_dec_ref_known(v___x_1589_, 1);
v___y_1412_ = v_normProcs_1571_;
v___y_1413_ = v_norm_1570_;
v___y_1414_ = v_anchorRefs_x3f_1572_;
v___y_1415_ = v_a_1576_;
v___y_1416_ = v_extensions_1565_;
v___y_1417_ = v_a_1580_;
v___y_1418_ = v_extraInj_1567_;
v___y_1419_ = v_extraFacts_1568_;
v___y_1420_ = v_symPrios_1569_;
v___y_1421_ = v_extra_1566_;
v___y_1422_ = v_config_1564_;
goto v___jp_1411_;
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v_a_1580_);
lean_dec(v_a_1576_);
lean_dec(v_anchorRefs_x3f_1572_);
lean_dec_ref(v_normProcs_1571_);
lean_dec_ref(v_norm_1570_);
lean_dec_ref(v_symPrios_1569_);
lean_dec_ref(v_extraFacts_1568_);
lean_dec_ref(v_extraInj_1567_);
lean_dec_ref(v_extra_1566_);
lean_dec_ref(v_extensions_1565_);
lean_dec_ref(v_config_1564_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_a_1576_);
lean_dec(v_anchorRefs_x3f_1572_);
lean_dec_ref(v_normProcs_1571_);
lean_dec_ref(v_norm_1570_);
lean_dec_ref(v_symPrios_1569_);
lean_dec_ref(v_extraFacts_1568_);
lean_dec_ref(v_extraInj_1567_);
lean_dec_ref(v_extra_1566_);
lean_dec_ref(v_extensions_1565_);
lean_dec_ref(v_config_1564_);
lean_dec(v_declName_1361_);
v_a_1598_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1578_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1578_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v_anchorRefs_x3f_1572_);
lean_dec_ref(v_normProcs_1571_);
lean_dec_ref(v_norm_1570_);
lean_dec_ref(v_symPrios_1569_);
lean_dec_ref(v_extraFacts_1568_);
lean_dec_ref(v_extraInj_1567_);
lean_dec_ref(v_extra_1566_);
lean_dec_ref(v_extensions_1565_);
lean_dec_ref(v_config_1564_);
lean_dec(v_declName_1361_);
v_a_1606_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1575_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1575_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_del_object(v___x_1561_);
lean_dec(v_declName_1361_);
lean_dec_ref(v_params_1359_);
v_a_1615_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1563_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1563_);
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
else
{
switch(lean_obj_tag(v_kind_1362_))
{
case 0:
{
v___y_1541_ = v___y_1557_;
v___y_1542_ = v___y_1555_;
v___y_1543_ = v___y_1558_;
v___y_1544_ = v___y_1556_;
goto v___jp_1540_;
}
case 1:
{
v___y_1541_ = v___y_1557_;
v___y_1542_ = v___y_1555_;
v___y_1543_ = v___y_1558_;
v___y_1544_ = v___y_1556_;
goto v___jp_1540_;
}
default: 
{
v___y_1522_ = v___y_1555_;
v___y_1523_ = v___y_1556_;
v___y_1524_ = v___y_1557_;
v___y_1525_ = v___y_1558_;
goto v___jp_1521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object* v_params_1666_, lean_object* v_id_1667_, lean_object* v_declName_1668_, lean_object* v_kind_1669_, lean_object* v_minIndexable_1670_, lean_object* v_suggest_1671_, lean_object* v_warn_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
uint8_t v_minIndexable_boxed_1678_; uint8_t v_suggest_boxed_1679_; uint8_t v_warn_boxed_1680_; lean_object* v_res_1681_; 
v_minIndexable_boxed_1678_ = lean_unbox(v_minIndexable_1670_);
v_suggest_boxed_1679_ = lean_unbox(v_suggest_1671_);
v_warn_boxed_1680_ = lean_unbox(v_warn_1672_);
v_res_1681_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_1666_, v_id_1667_, v_declName_1668_, v_kind_1669_, v_minIndexable_boxed_1678_, v_suggest_boxed_1679_, v_warn_boxed_1680_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object* v_declName_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1682_, v___y_1686_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object* v_declName_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(v_declName_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_1696_, lean_object* v_constName_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1704_, lean_object* v_constName_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(v_00_u03b1_1704_, v_constName_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1712_, lean_object* v_ref_1713_, lean_object* v_constName_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1713_, v_constName_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1721_, lean_object* v_ref_1722_, lean_object* v_constName_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(v_00_u03b1_1721_, v_ref_1722_, v_constName_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v_ref_1722_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1730_, lean_object* v_ref_1731_, lean_object* v_msg_1732_, lean_object* v_declHint_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1731_, v_msg_1732_, v_declHint_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1740_, lean_object* v_ref_1741_, lean_object* v_msg_1742_, lean_object* v_declHint_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1740_, v_ref_1741_, v_msg_1742_, v_declHint_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v_ref_1741_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1750_, lean_object* v_declHint_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1750_, v_declHint_1751_, v___y_1755_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1758_, lean_object* v_declHint_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1758_, v_declHint_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1766_, lean_object* v_ref_1767_, lean_object* v_msg_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1767_, v_msg_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1775_, lean_object* v_ref_1776_, lean_object* v_msg_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1775_, v_ref_1776_, v_msg_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v_ref_1776_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(lean_object* v_declName_1788_, lean_object* v_symPrios_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
uint8_t v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = 0;
lean_inc(v_declName_1788_);
v___x_1796_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1788_, v___x_1795_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1869_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1869_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1869_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
uint8_t v_kind_1866_; 
v_kind_1866_ = lean_ctor_get_uint8(v_a_1797_, sizeof(void*)*3);
switch(v_kind_1866_)
{
case 1:
{
goto v___jp_1801_;
}
case 2:
{
goto v___jp_1801_;
}
case 6:
{
goto v___jp_1801_;
}
default: 
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_del_object(v___x_1799_);
lean_dec(v_a_1797_);
lean_dec_ref(v_symPrios_1789_);
lean_dec(v_declName_1788_);
v___x_1867_ = lean_box(v___x_1795_);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
return v___x_1868_;
}
}
v___jp_1801_:
{
lean_object* v___x_1802_; lean_object* v_levelParams_1803_; lean_object* v_type_1804_; uint8_t v___x_1805_; 
v___x_1802_ = l_Lean_AsyncConstantInfo_toConstantVal(v_a_1797_);
v_levelParams_1803_ = lean_ctor_get(v___x_1802_, 1);
lean_inc(v_levelParams_1803_);
v_type_1804_ = lean_ctor_get(v___x_1802_, 2);
lean_inc_ref(v_type_1804_);
lean_dec_ref(v___x_1802_);
v___x_1805_ = l_List_isEmpty___redArg(v_levelParams_1803_);
lean_dec(v_levelParams_1803_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
lean_dec_ref(v_type_1804_);
lean_dec_ref(v_symPrios_1789_);
lean_dec(v_declName_1788_);
v___x_1806_ = lean_box(v___x_1795_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1806_);
v___x_1808_ = v___x_1799_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
else
{
lean_object* v___x_1810_; 
lean_del_object(v___x_1799_);
lean_inc_ref(v_type_1804_);
v___x_1810_ = l_Lean_Meta_whnfR(v_type_1804_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1857_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1857_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1857_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
uint8_t v___x_1815_; 
v___x_1815_ = l_Lean_Expr_isForall(v_a_1811_);
lean_dec(v_a_1811_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
lean_del_object(v___x_1813_);
v___x_1816_ = l_Lean_Meta_isProp(v_type_1804_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1852_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1852_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1852_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_unbox(v_a_1817_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
lean_dec(v_a_1817_);
lean_dec_ref(v_symPrios_1789_);
lean_dec(v_declName_1788_);
v___x_1822_ = lean_box(v___x_1795_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1822_);
v___x_1824_ = v___x_1819_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_del_object(v___x_1819_);
lean_inc(v_declName_1788_);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_declName_1788_);
v___x_1827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__0));
v___x_1828_ = lean_box(0);
v___x_1829_ = l_Lean_mkConst(v_declName_1788_, v___x_1828_);
v___x_1830_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v___x_1831_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_1826_, v___x_1827_, v___x_1829_, v___x_1830_, v_symPrios_1789_, v___x_1805_, v___x_1795_, v___x_1795_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1843_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1843_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1843_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
if (lean_obj_tag(v_a_1832_) == 0)
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v_a_1817_);
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1817_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
lean_dec_ref_known(v_a_1832_, 1);
lean_dec(v_a_1817_);
v___x_1839_ = lean_box(v___x_1815_);
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
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_a_1817_);
v_a_1844_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1831_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1831_);
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
else
{
lean_dec_ref(v_symPrios_1789_);
lean_dec(v_declName_1788_);
return v___x_1816_;
}
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
lean_dec_ref(v_type_1804_);
lean_dec_ref(v_symPrios_1789_);
lean_dec(v_declName_1788_);
v___x_1853_ = lean_box(v___x_1795_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1853_);
v___x_1855_ = v___x_1813_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
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
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec_ref(v_type_1804_);
lean_dec_ref(v_symPrios_1789_);
lean_dec(v_declName_1788_);
v_a_1858_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1810_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1810_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v_symPrios_1789_);
lean_dec(v_declName_1788_);
v_a_1870_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1796_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1796_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___boxed(lean_object* v_declName_1878_, lean_object* v_symPrios_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(v_declName_1878_, v_symPrios_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(lean_object* v_params_1886_, lean_object* v_declName_1887_, uint8_t v_minIndexable_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1920_; 
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; 
v_unused_1921_ = lean_ctor_get(v___x_1894_, 0);
lean_dec(v_unused_1921_);
v___x_1896_ = v___x_1894_;
v_isShared_1897_ = v_isSharedCheck_1920_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v___x_1894_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1920_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_config_1898_; lean_object* v_extensions_1899_; lean_object* v_extra_1900_; lean_object* v_extraInj_1901_; lean_object* v_extraFacts_1902_; lean_object* v_symPrios_1903_; lean_object* v_norm_1904_; lean_object* v_normProcs_1905_; lean_object* v_anchorRefs_x3f_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1919_; 
v_config_1898_ = lean_ctor_get(v_params_1886_, 0);
v_extensions_1899_ = lean_ctor_get(v_params_1886_, 1);
v_extra_1900_ = lean_ctor_get(v_params_1886_, 2);
v_extraInj_1901_ = lean_ctor_get(v_params_1886_, 3);
v_extraFacts_1902_ = lean_ctor_get(v_params_1886_, 4);
v_symPrios_1903_ = lean_ctor_get(v_params_1886_, 5);
v_norm_1904_ = lean_ctor_get(v_params_1886_, 6);
v_normProcs_1905_ = lean_ctor_get(v_params_1886_, 7);
v_anchorRefs_x3f_1906_ = lean_ctor_get(v_params_1886_, 8);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_params_1886_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1908_ = v_params_1886_;
v_isShared_1909_ = v_isSharedCheck_1919_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_anchorRefs_x3f_1906_);
lean_inc(v_normProcs_1905_);
lean_inc(v_norm_1904_);
lean_inc(v_symPrios_1903_);
lean_inc(v_extraFacts_1902_);
lean_inc(v_extraInj_1901_);
lean_inc(v_extra_1900_);
lean_inc(v_extensions_1899_);
lean_inc(v_config_1898_);
lean_dec(v_params_1886_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1919_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1910_ = lean_box(0);
v___x_1911_ = l_Lean_mkConst(v_declName_1887_, v___x_1910_);
v___x_1912_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_1902_, v___x_1911_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 4, v___x_1912_);
v___x_1914_ = v___x_1908_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_config_1898_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_extensions_1899_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_extra_1900_);
lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_extraInj_1901_);
lean_ctor_set(v_reuseFailAlloc_1918_, 4, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1918_, 5, v_symPrios_1903_);
lean_ctor_set(v_reuseFailAlloc_1918_, 6, v_norm_1904_);
lean_ctor_set(v_reuseFailAlloc_1918_, 7, v_normProcs_1905_);
lean_ctor_set(v_reuseFailAlloc_1918_, 8, v_anchorRefs_x3f_1906_);
v___x_1914_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1914_);
v___x_1916_ = v___x_1896_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_declName_1887_);
lean_dec_ref(v_params_1886_);
v_a_1922_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1894_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1894_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact___boxed(lean_object* v_params_1930_, lean_object* v_declName_1931_, lean_object* v_minIndexable_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
uint8_t v_minIndexable_boxed_1938_; lean_object* v_res_1939_; 
v_minIndexable_boxed_1938_ = lean_unbox(v_minIndexable_1932_);
v_res_1939_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(v_params_1930_, v_declName_1931_, v_minIndexable_boxed_1938_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1942_, lean_object* v_val_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v_config_1947_; lean_object* v_extensions_1948_; lean_object* v_extra_1949_; lean_object* v_extraInj_1950_; lean_object* v_extraFacts_1951_; lean_object* v_symPrios_1952_; lean_object* v_norm_1953_; lean_object* v_normProcs_1954_; lean_object* v_anchorRefs_x3f_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1985_; 
v_config_1947_ = lean_ctor_get(v_params_1942_, 0);
v_extensions_1948_ = lean_ctor_get(v_params_1942_, 1);
v_extra_1949_ = lean_ctor_get(v_params_1942_, 2);
v_extraInj_1950_ = lean_ctor_get(v_params_1942_, 3);
v_extraFacts_1951_ = lean_ctor_get(v_params_1942_, 4);
v_symPrios_1952_ = lean_ctor_get(v_params_1942_, 5);
v_norm_1953_ = lean_ctor_get(v_params_1942_, 6);
v_normProcs_1954_ = lean_ctor_get(v_params_1942_, 7);
v_anchorRefs_x3f_1955_ = lean_ctor_get(v_params_1942_, 8);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_params_1942_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1957_ = v_params_1942_;
v_isShared_1958_ = v_isSharedCheck_1985_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_anchorRefs_x3f_1955_);
lean_inc(v_normProcs_1954_);
lean_inc(v_norm_1953_);
lean_inc(v_symPrios_1952_);
lean_inc(v_extraFacts_1951_);
lean_inc(v_extraInj_1950_);
lean_inc(v_extra_1949_);
lean_inc(v_extensions_1948_);
lean_inc(v_config_1947_);
lean_dec(v_params_1942_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1985_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___y_1960_; 
if (lean_obj_tag(v_anchorRefs_x3f_1955_) == 0)
{
lean_object* v___x_1983_; 
v___x_1983_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_1960_ = v___x_1983_;
goto v___jp_1959_;
}
else
{
lean_object* v_val_1984_; 
v_val_1984_ = lean_ctor_get(v_anchorRefs_x3f_1955_, 0);
lean_inc(v_val_1984_);
lean_dec_ref_known(v_anchorRefs_x3f_1955_, 1);
v___y_1960_ = v_val_1984_;
goto v___jp_1959_;
}
v___jp_1959_:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1974_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1974_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1974_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1966_ = lean_array_push(v___y_1960_, v_a_1962_);
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 8, v___x_1967_);
v___x_1969_ = v___x_1957_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_config_1947_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_extensions_1948_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_extra_1949_);
lean_ctor_set(v_reuseFailAlloc_1973_, 3, v_extraInj_1950_);
lean_ctor_set(v_reuseFailAlloc_1973_, 4, v_extraFacts_1951_);
lean_ctor_set(v_reuseFailAlloc_1973_, 5, v_symPrios_1952_);
lean_ctor_set(v_reuseFailAlloc_1973_, 6, v_norm_1953_);
lean_ctor_set(v_reuseFailAlloc_1973_, 7, v_normProcs_1954_);
lean_ctor_set(v_reuseFailAlloc_1973_, 8, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1969_);
v___x_1971_ = v___x_1964_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v___y_1960_);
lean_del_object(v___x_1957_);
lean_dec_ref(v_normProcs_1954_);
lean_dec_ref(v_norm_1953_);
lean_dec_ref(v_symPrios_1952_);
lean_dec_ref(v_extraFacts_1951_);
lean_dec_ref(v_extraInj_1950_);
lean_dec_ref(v_extra_1949_);
lean_dec_ref(v_extensions_1948_);
lean_dec_ref(v_config_1947_);
v_a_1975_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1961_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1961_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_1986_, lean_object* v_val_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_1986_, v_val_1987_, v_a_1988_, v_a_1989_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_val_1987_);
return v_res_1991_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_1994_ = l_Lean_stringToMessageData(v___x_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_config_1999_; uint8_t v_revert_2000_; 
v_config_1999_ = lean_ctor_get(v_params_1995_, 0);
v_revert_2000_ = lean_ctor_get_uint8(v_config_1999_, sizeof(void*)*14 + 31);
if (v_revert_2000_ == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_box(0);
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
return v___x_2002_;
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_2004_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_2003_, v_a_1996_, v_a_1997_);
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2005_, v_a_2006_, v_a_2007_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_params_2005_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_2010_, lean_object* v___y_2011_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = l_Lean_Expr_hasMVar(v_e_2010_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_e_2010_);
return v___x_2014_;
}
else
{
lean_object* v___x_2015_; lean_object* v_mctx_2016_; lean_object* v___x_2017_; lean_object* v_fst_2018_; lean_object* v_snd_2019_; lean_object* v___x_2020_; lean_object* v_cache_2021_; lean_object* v_zetaDeltaFVarIds_2022_; lean_object* v_postponed_2023_; lean_object* v_diag_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2033_; 
v___x_2015_ = lean_st_ref_get(v___y_2011_);
v_mctx_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_ref(v_mctx_2016_);
lean_dec(v___x_2015_);
v___x_2017_ = l_Lean_instantiateMVarsCore(v_mctx_2016_, v_e_2010_);
v_fst_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_fst_2018_);
v_snd_2019_ = lean_ctor_get(v___x_2017_, 1);
lean_inc(v_snd_2019_);
lean_dec_ref(v___x_2017_);
v___x_2020_ = lean_st_ref_take(v___y_2011_);
v_cache_2021_ = lean_ctor_get(v___x_2020_, 1);
v_zetaDeltaFVarIds_2022_ = lean_ctor_get(v___x_2020_, 2);
v_postponed_2023_ = lean_ctor_get(v___x_2020_, 3);
v_diag_2024_ = lean_ctor_get(v___x_2020_, 4);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; 
v_unused_2034_ = lean_ctor_get(v___x_2020_, 0);
lean_dec(v_unused_2034_);
v___x_2026_ = v___x_2020_;
v_isShared_2027_ = v_isSharedCheck_2033_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_diag_2024_);
lean_inc(v_postponed_2023_);
lean_inc(v_zetaDeltaFVarIds_2022_);
lean_inc(v_cache_2021_);
lean_dec(v___x_2020_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2033_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v_snd_2019_);
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_snd_2019_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_cache_2021_);
lean_ctor_set(v_reuseFailAlloc_2032_, 2, v_zetaDeltaFVarIds_2022_);
lean_ctor_set(v_reuseFailAlloc_2032_, 3, v_postponed_2023_);
lean_ctor_set(v_reuseFailAlloc_2032_, 4, v_diag_2024_);
v___x_2029_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_st_ref_put(v___y_2011_, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v_fst_2018_);
return v___x_2031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_2035_, v___y_2036_);
lean_dec(v___y_2036_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_2039_, v___y_2043_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(uint8_t v___x_2057_, uint8_t v___x_2058_, uint8_t v_____do__lift_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
if (v_____do__lift_2059_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_box(v___x_2057_);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_box(v___x_2058_);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v___x_2071_, lean_object* v___x_2072_, lean_object* v_____do__lift_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
uint8_t v___x_14831__boxed_2081_; uint8_t v___x_14832__boxed_2082_; uint8_t v_____do__lift_14833__boxed_2083_; lean_object* v_res_2084_; 
v___x_14831__boxed_2081_ = lean_unbox(v___x_2071_);
v___x_14832__boxed_2082_ = lean_unbox(v___x_2072_);
v_____do__lift_14833__boxed_2083_ = lean_unbox(v_____do__lift_2073_);
v_res_2084_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_14831__boxed_2081_, v___x_14832__boxed_2082_, v_____do__lift_14833__boxed_2083_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(uint8_t v___x_2085_, uint8_t v___x_2086_, lean_object* v_as_2087_, size_t v_i_2088_, size_t v_stop_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v___x_2095_; 
v___x_2095_ = lean_usize_dec_eq(v_i_2088_, v_stop_2089_);
if (v___x_2095_ == 0)
{
uint8_t v___x_2096_; uint8_t v_a_2098_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2096_ = 1;
v___x_2104_ = lean_array_uget_borrowed(v_as_2087_, v_i_2088_);
lean_inc(v___x_2104_);
v___x_2105_ = l_Lean_Meta_isProof(v___x_2104_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; uint8_t v___x_2107_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = lean_unbox(v_a_2106_);
lean_dec(v_a_2106_);
if (v___x_2107_ == 0)
{
v_a_2098_ = v___x_2085_;
goto v___jp_2097_;
}
else
{
v_a_2098_ = v___x_2086_;
goto v___jp_2097_;
}
}
else
{
return v___x_2105_;
}
v___jp_2097_:
{
if (v_a_2098_ == 0)
{
size_t v___x_2099_; size_t v___x_2100_; 
v___x_2099_ = ((size_t)1ULL);
v___x_2100_ = lean_usize_add(v_i_2088_, v___x_2099_);
v_i_2088_ = v___x_2100_;
goto _start;
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_box(v___x_2096_);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
}
else
{
uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = 0;
v___x_2109_ = lean_box(v___x_2108_);
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
return v___x_2110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v___x_2111_, lean_object* v___x_2112_, lean_object* v_as_2113_, lean_object* v_i_2114_, lean_object* v_stop_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
uint8_t v___x_14869__boxed_2121_; uint8_t v___x_14870__boxed_2122_; size_t v_i_boxed_2123_; size_t v_stop_boxed_2124_; lean_object* v_res_2125_; 
v___x_14869__boxed_2121_ = lean_unbox(v___x_2111_);
v___x_14870__boxed_2122_ = lean_unbox(v___x_2112_);
v_i_boxed_2123_ = lean_unbox_usize(v_i_2114_);
lean_dec(v_i_2114_);
v_stop_boxed_2124_ = lean_unbox_usize(v_stop_2115_);
lean_dec(v_stop_2115_);
v_res_2125_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_14869__boxed_2121_, v___x_14870__boxed_2122_, v_as_2113_, v_i_boxed_2123_, v_stop_boxed_2124_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec_ref(v_as_2113_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_p_2126_, lean_object* v_term_2127_, lean_object* v___x_2128_, uint8_t v___x_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_toCold_2137_; lean_object* v_currRecDepth_2138_; lean_object* v_ref_2139_; uint16_t v_optionFlags_2140_; uint8_t v_suppressElabErrors_2141_; uint8_t v_isRecordingDeps_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2239_; 
v_toCold_2137_ = lean_ctor_get(v___y_2134_, 0);
v_currRecDepth_2138_ = lean_ctor_get(v___y_2134_, 1);
v_ref_2139_ = lean_ctor_get(v___y_2134_, 2);
v_optionFlags_2140_ = lean_ctor_get_uint16(v___y_2134_, sizeof(void*)*3);
v_suppressElabErrors_2141_ = lean_ctor_get_uint8(v___y_2134_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2142_ = lean_ctor_get_uint8(v___y_2134_, sizeof(void*)*3 + 3);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___y_2134_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2144_ = v___y_2134_;
v_isShared_2145_ = v_isSharedCheck_2239_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_ref_2139_);
lean_inc(v_currRecDepth_2138_);
lean_inc(v_toCold_2137_);
lean_dec(v___y_2134_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2239_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v_ref_2146_; lean_object* v___x_2148_; 
v_ref_2146_ = l_Lean_replaceRef(v_p_2126_, v_ref_2139_);
lean_dec(v_ref_2139_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 2, v_ref_2146_);
v___x_2148_ = v___x_2144_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_toCold_2137_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_currRecDepth_2138_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_ref_2146_);
lean_ctor_set_uint16(v_reuseFailAlloc_2238_, sizeof(void*)*3, v_optionFlags_2140_);
lean_ctor_set_uint8(v_reuseFailAlloc_2238_, sizeof(void*)*3 + 2, v_suppressElabErrors_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2238_, sizeof(void*)*3 + 3, v_isRecordingDeps_2142_);
v___x_2148_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_Elab_Term_elabTerm(v_term_2127_, v___x_2128_, v___x_2129_, v___x_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___x_2148_, v___y_2135_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = 1;
v___x_2152_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_2151_, v___x_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___x_2148_, v___y_2135_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v___x_2153_; lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2221_; 
lean_dec_ref_known(v___x_2152_, 1);
v___x_2153_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_2150_, v___y_2133_);
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2221_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2221_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
uint8_t v___x_2158_; 
v___x_2158_ = l_Lean_Expr_hasSyntheticSorry(v_a_2154_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2159_ = l_Lean_Expr_eta(v_a_2154_);
v___x_2160_ = l_Lean_Expr_hasMVar(v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_dec_ref(v___x_2148_);
v___x_2161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__0));
v___x_2162_ = lean_box(v___x_2160_);
v___x_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2159_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2161_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2165_);
v___x_2167_ = v___x_2156_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
else
{
lean_object* v___x_2169_; 
lean_del_object(v___x_2156_);
v___x_2169_ = l_Lean_Meta_abstractMVars(v___x_2159_, v___x_2129_, v___y_2132_, v___y_2133_, v___x_2148_, v___y_2135_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2208_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2208_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2208_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_paramNames_2174_; lean_object* v_mvars_2175_; lean_object* v_expr_2176_; uint8_t v_a_2178_; lean_object* v___y_2187_; lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v_paramNames_2174_ = lean_ctor_get(v_a_2170_, 0);
lean_inc_ref(v_paramNames_2174_);
v_mvars_2175_ = lean_ctor_get(v_a_2170_, 1);
lean_inc_ref(v_mvars_2175_);
v_expr_2176_ = lean_ctor_get(v_a_2170_, 2);
lean_inc_ref(v_expr_2176_);
lean_dec(v_a_2170_);
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = lean_array_get_size(v_mvars_2175_);
v___x_2192_ = lean_nat_dec_lt(v___x_2190_, v___x_2191_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; 
lean_dec_ref(v_mvars_2175_);
v___x_2193_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2160_, v___x_2158_, v___x_2192_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___x_2148_, v___y_2135_);
lean_dec_ref(v___x_2148_);
v___y_2187_ = v___x_2193_;
goto v___jp_2186_;
}
else
{
if (v___x_2192_ == 0)
{
lean_dec_ref(v_mvars_2175_);
lean_dec_ref(v___x_2148_);
v_a_2178_ = v___x_2160_;
goto v___jp_2177_;
}
else
{
size_t v___x_2194_; size_t v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = ((size_t)0ULL);
v___x_2195_ = lean_usize_of_nat(v___x_2191_);
v___x_2196_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2160_, v___x_2158_, v_mvars_2175_, v___x_2194_, v___x_2195_, v___y_2132_, v___y_2133_, v___x_2148_, v___y_2135_);
lean_dec_ref(v_mvars_2175_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
v___x_2198_ = lean_unbox(v_a_2197_);
lean_dec(v_a_2197_);
v___x_2199_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2160_, v___x_2158_, v___x_2198_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___x_2148_, v___y_2135_);
lean_dec_ref(v___x_2148_);
v___y_2187_ = v___x_2199_;
goto v___jp_2186_;
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec_ref(v_expr_2176_);
lean_dec_ref(v_paramNames_2174_);
lean_del_object(v___x_2172_);
lean_dec_ref(v___x_2148_);
v_a_2200_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2196_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2196_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
v___jp_2177_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2179_ = lean_box(v_a_2178_);
v___x_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2180_, 0, v_expr_2176_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2181_, 0, v_paramNames_2174_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2182_);
v___x_2184_ = v___x_2172_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
v___jp_2186_:
{
lean_object* v_a_2188_; uint8_t v___x_2189_; 
v_a_2188_ = lean_ctor_get(v___y_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref(v___y_2187_);
v___x_2189_ = lean_unbox(v_a_2188_);
lean_dec(v_a_2188_);
v_a_2178_ = v___x_2189_;
goto v___jp_2177_;
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec_ref(v___x_2148_);
v_a_2209_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2169_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2169_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2219_; 
lean_dec(v_a_2154_);
lean_dec_ref(v___x_2148_);
v___x_2217_ = lean_box(0);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2217_);
v___x_2219_ = v___x_2156_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_a_2150_);
lean_dec_ref(v___x_2148_);
v_a_2222_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2152_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2152_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec_ref(v___x_2148_);
v_a_2230_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2149_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2149_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_p_2240_, lean_object* v_term_2241_, lean_object* v___x_2242_, lean_object* v___x_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
uint8_t v___x_14926__boxed_2251_; lean_object* v_res_2252_; 
v___x_14926__boxed_2251_ = lean_unbox(v___x_2243_);
v_res_2252_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_p_2240_, v_term_2241_, v___x_2242_, v___x_14926__boxed_2251_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v_p_2240_);
return v_res_2252_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__2));
v___x_2258_ = l_Lean_stringToMessageData(v___x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(lean_object* v_params_2259_, lean_object* v_p_2260_, lean_object* v_fst_2261_, lean_object* v_fst_2262_, uint8_t v___x_2263_, uint8_t v_minIndexable_2264_, lean_object* v_kind_2265_, lean_object* v_idx_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_symPrios_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; lean_object* v___x_2277_; 
v_symPrios_2272_ = lean_ctor_get(v_params_2259_, 5);
lean_inc_ref(v_symPrios_2272_);
lean_dec_ref(v_params_2259_);
v___x_2273_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__1));
v___x_2274_ = lean_name_append_index_after(v___x_2273_, v_idx_2266_);
v___x_2275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v_p_2260_);
v___x_2276_ = 0;
v___x_2277_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2275_, v_fst_2261_, v_fst_2262_, v_kind_2265_, v_symPrios_2272_, v___x_2263_, v___x_2276_, v_minIndexable_2264_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2288_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2288_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2288_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
if (lean_obj_tag(v_a_2278_) == 1)
{
lean_object* v_val_2282_; lean_object* v___x_2284_; 
v_val_2282_ = lean_ctor_get(v_a_2278_, 0);
lean_inc(v_val_2282_);
lean_dec_ref_known(v_a_2278_, 1);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v_val_2282_);
v___x_2284_ = v___x_2280_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_val_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_del_object(v___x_2280_);
lean_dec(v_a_2278_);
v___x_2286_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3);
v___x_2287_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2286_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
return v___x_2287_;
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
v_a_2289_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2277_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2277_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed(lean_object* v_params_2297_, lean_object* v_p_2298_, lean_object* v_fst_2299_, lean_object* v_fst_2300_, lean_object* v___x_2301_, lean_object* v_minIndexable_2302_, lean_object* v_kind_2303_, lean_object* v_idx_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
uint8_t v___x_15156__boxed_2310_; uint8_t v_minIndexable_boxed_2311_; lean_object* v_res_2312_; 
v___x_15156__boxed_2310_ = lean_unbox(v___x_2301_);
v_minIndexable_boxed_2311_ = lean_unbox(v_minIndexable_2302_);
v_res_2312_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(v_params_2297_, v_p_2298_, v_fst_2299_, v_fst_2300_, v___x_15156__boxed_2310_, v_minIndexable_boxed_2311_, v_kind_2303_, v_idx_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
return v_res_2312_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_box(1);
v___x_2314_ = l_Lean_MessageData_ofFormat(v___x_2313_);
return v___x_2314_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__2));
v___x_2319_ = l_Lean_MessageData_ofFormat(v___x_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(lean_object* v_x_2320_, lean_object* v_x_2321_){
_start:
{
if (lean_obj_tag(v_x_2321_) == 0)
{
return v_x_2320_;
}
else
{
lean_object* v_head_2322_; lean_object* v_tail_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2345_; 
v_head_2322_ = lean_ctor_get(v_x_2321_, 0);
v_tail_2323_ = lean_ctor_get(v_x_2321_, 1);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_x_2321_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2325_ = v_x_2321_;
v_isShared_2326_ = v_isSharedCheck_2345_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_tail_2323_);
lean_inc(v_head_2322_);
lean_dec(v_x_2321_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2345_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v_before_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2343_; 
v_before_2327_ = lean_ctor_get(v_head_2322_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_head_2322_);
if (v_isSharedCheck_2343_ == 0)
{
lean_object* v_unused_2344_; 
v_unused_2344_ = lean_ctor_get(v_head_2322_, 1);
lean_dec(v_unused_2344_);
v___x_2329_ = v_head_2322_;
v_isShared_2330_ = v_isSharedCheck_2343_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_before_2327_);
lean_dec(v_head_2322_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2343_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2331_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2330_ == 0)
{
lean_ctor_set_tag(v___x_2329_, 7);
lean_ctor_set(v___x_2329_, 1, v___x_2331_);
lean_ctor_set(v___x_2329_, 0, v_x_2320_);
v___x_2333_ = v___x_2329_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_x_2320_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2334_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3);
if (v_isShared_2326_ == 0)
{
lean_ctor_set_tag(v___x_2325_, 7);
lean_ctor_set(v___x_2325_, 1, v___x_2334_);
lean_ctor_set(v___x_2325_, 0, v___x_2333_);
v___x_2336_ = v___x_2325_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = l_Lean_MessageData_ofSyntax(v_before_2327_);
v___x_2338_ = l_Lean_indentD(v___x_2337_);
v___x_2339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2336_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v_x_2320_ = v___x_2339_;
v_x_2321_ = v_tail_2323_;
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
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__1));
v___x_2350_ = l_Lean_MessageData_ofFormat(v___x_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(lean_object* v_msgData_2351_, lean_object* v_macroStack_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2355_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2353_);
v___x_2356_ = l_Lean_Elab_pp_macroStack;
v___x_2357_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_2355_, v___x_2356_);
lean_dec_ref(v___x_2355_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; 
lean_dec(v_macroStack_2352_);
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v_msgData_2351_);
return v___x_2358_;
}
else
{
if (lean_obj_tag(v_macroStack_2352_) == 0)
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v_msgData_2351_);
return v___x_2359_;
}
else
{
lean_object* v_head_2360_; lean_object* v_after_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2376_; 
v_head_2360_ = lean_ctor_get(v_macroStack_2352_, 0);
lean_inc(v_head_2360_);
v_after_2361_ = lean_ctor_get(v_head_2360_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_head_2360_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v_head_2360_, 0);
lean_dec(v_unused_2377_);
v___x_2363_ = v_head_2360_;
v_isShared_2364_ = v_isSharedCheck_2376_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_after_2361_);
lean_dec(v_head_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2376_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2365_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2364_ == 0)
{
lean_ctor_set_tag(v___x_2363_, 7);
lean_ctor_set(v___x_2363_, 1, v___x_2365_);
lean_ctor_set(v___x_2363_, 0, v_msgData_2351_);
v___x_2367_ = v___x_2363_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_msgData_2351_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v_msgData_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2368_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = l_Lean_MessageData_ofSyntax(v_after_2361_);
v___x_2371_ = l_Lean_indentD(v___x_2370_);
v_msgData_2372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2372_, 0, v___x_2369_);
lean_ctor_set(v_msgData_2372_, 1, v___x_2371_);
v___x_2373_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(v_msgData_2372_, v_macroStack_2352_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_2378_, lean_object* v_macroStack_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2378_, v_macroStack_2379_, v___y_2380_);
lean_dec_ref(v___y_2380_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(lean_object* v_msg_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_ref_2391_; lean_object* v_macroStack_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v_a_2395_; lean_object* v___x_2396_; lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2405_; 
v_ref_2391_ = lean_ctor_get(v___y_2388_, 2);
v_macroStack_2392_ = lean_ctor_get(v___y_2384_, 1);
v___x_2393_ = l_Lean_Elab_getBetterRef(v_ref_2391_, v_macroStack_2392_);
v___x_2394_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2383_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref(v___x_2394_);
lean_inc(v_macroStack_2392_);
v___x_2396_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_a_2395_, v_macroStack_2392_, v___y_2388_);
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2405_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2405_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2393_);
lean_ctor_set(v___x_2401_, 1, v_a_2397_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set_tag(v___x_2399_, 1);
lean_ctor_set(v___x_2399_, 0, v___x_2401_);
v___x_2403_ = v___x_2399_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg___boxed(lean_object* v_msg_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2414_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2417_ = l_Lean_stringToMessageData(v___x_2416_);
return v___x_2417_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2420_ = l_Lean_stringToMessageData(v___x_2419_);
return v___x_2420_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2423_ = l_Lean_stringToMessageData(v___x_2422_);
return v___x_2423_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_2426_ = l_Lean_stringToMessageData(v___x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2427_, lean_object* v_p_2428_, lean_object* v_mod_x3f_2429_, lean_object* v_term_2430_, uint8_t v_minIndexable_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v___y_2440_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; uint8_t v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v_kind_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v_toCold_2795_; lean_object* v_currRecDepth_2796_; lean_object* v_ref_2797_; uint16_t v_optionFlags_2798_; uint8_t v_suppressElabErrors_2799_; uint8_t v_isRecordingDeps_2800_; lean_object* v_ref_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v_toCold_2795_ = lean_ctor_get(v_a_2436_, 0);
v_currRecDepth_2796_ = lean_ctor_get(v_a_2436_, 1);
v_ref_2797_ = lean_ctor_get(v_a_2436_, 2);
v_optionFlags_2798_ = lean_ctor_get_uint16(v_a_2436_, sizeof(void*)*3);
v_suppressElabErrors_2799_ = lean_ctor_get_uint8(v_a_2436_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2800_ = lean_ctor_get_uint8(v_a_2436_, sizeof(void*)*3 + 3);
v_ref_2801_ = l_Lean_replaceRef(v_p_2428_, v_ref_2797_);
lean_inc(v_currRecDepth_2796_);
lean_inc_ref(v_toCold_2795_);
v___x_2802_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2802_, 0, v_toCold_2795_);
lean_ctor_set(v___x_2802_, 1, v_currRecDepth_2796_);
lean_ctor_set(v___x_2802_, 2, v_ref_2801_);
lean_ctor_set_uint16(v___x_2802_, sizeof(void*)*3, v_optionFlags_2798_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*3 + 2, v_suppressElabErrors_2799_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*3 + 3, v_isRecordingDeps_2800_);
v___x_2803_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2427_, v___x_2802_, v_a_2437_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_dec_ref_known(v___x_2803_, 1);
if (lean_obj_tag(v_mod_x3f_2429_) == 1)
{
lean_object* v_val_2804_; lean_object* v___x_2805_; 
v_val_2804_ = lean_ctor_get(v_mod_x3f_2429_, 0);
lean_inc(v_val_2804_);
v___x_2805_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2804_, v___x_2802_, v_a_2437_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
switch(lean_obj_tag(v_a_2806_))
{
case 0:
{
lean_object* v_k_2807_; 
v_k_2807_ = lean_ctor_get(v_a_2806_, 0);
lean_inc(v_k_2807_);
lean_dec_ref_known(v_a_2806_, 1);
if (lean_obj_tag(v_k_2807_) == 9)
{
lean_dec_ref_known(v_mod_x3f_2429_, 1);
lean_dec(v_term_2430_);
lean_dec(v_p_2428_);
lean_dec_ref(v_params_2427_);
v___y_2754_ = v_a_2432_;
v___y_2755_ = v_a_2433_;
v___y_2756_ = v_a_2434_;
v___y_2757_ = v_a_2435_;
v___y_2758_ = v___x_2802_;
v___y_2759_ = v_a_2437_;
goto v___jp_2753_;
}
else
{
v_kind_2685_ = v_k_2807_;
v___y_2686_ = v_a_2432_;
v___y_2687_ = v_a_2433_;
v___y_2688_ = v_a_2434_;
v___y_2689_ = v_a_2435_;
v___y_2690_ = v___x_2802_;
v___y_2691_ = v_a_2437_;
goto v___jp_2684_;
}
}
case 1:
{
lean_dec_ref_known(v_a_2806_, 0);
lean_dec_ref_known(v_mod_x3f_2429_, 1);
lean_dec(v_term_2430_);
lean_dec(v_p_2428_);
lean_dec_ref(v_params_2427_);
v___y_2771_ = v_a_2432_;
v___y_2772_ = v_a_2433_;
v___y_2773_ = v_a_2434_;
v___y_2774_ = v_a_2435_;
v___y_2775_ = v___x_2802_;
v___y_2776_ = v_a_2437_;
goto v___jp_2770_;
}
case 3:
{
v___y_2788_ = v_a_2432_;
v___y_2789_ = v_a_2433_;
v___y_2790_ = v_a_2434_;
v___y_2791_ = v_a_2435_;
v___y_2792_ = v___x_2802_;
v___y_2793_ = v_a_2437_;
goto v___jp_2787_;
}
case 5:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec_ref_known(v_a_2806_, 1);
lean_dec_ref_known(v_mod_x3f_2429_, 1);
lean_dec(v_term_2430_);
lean_dec(v_p_2428_);
lean_dec_ref(v_params_2427_);
v___x_2808_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2809_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2808_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v___x_2802_, v_a_2437_);
lean_dec_ref_known(v___x_2802_, 3);
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
case 8:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref_known(v_a_2806_, 0);
lean_dec_ref_known(v_mod_x3f_2429_, 1);
lean_dec(v_term_2430_);
lean_dec(v_p_2428_);
lean_dec_ref(v_params_2427_);
v___x_2818_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2819_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2818_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v___x_2802_, v_a_2437_);
lean_dec_ref_known(v___x_2802_, 3);
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2819_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
case 10:
{
lean_dec_ref_known(v_a_2806_, 0);
lean_dec_ref_known(v_mod_x3f_2429_, 1);
lean_dec(v_term_2430_);
lean_dec(v_p_2428_);
lean_dec_ref(v_params_2427_);
v___y_2771_ = v_a_2432_;
v___y_2772_ = v_a_2433_;
v___y_2773_ = v_a_2434_;
v___y_2774_ = v_a_2435_;
v___y_2775_ = v___x_2802_;
v___y_2776_ = v_a_2437_;
goto v___jp_2770_;
}
default: 
{
lean_dec(v_a_2806_);
lean_dec_ref_known(v_mod_x3f_2429_, 1);
lean_dec(v_term_2430_);
lean_dec(v_p_2428_);
lean_dec_ref(v_params_2427_);
v___y_2754_ = v_a_2432_;
v___y_2755_ = v_a_2433_;
v___y_2756_ = v_a_2434_;
v___y_2757_ = v_a_2435_;
v___y_2758_ = v___x_2802_;
v___y_2759_ = v_a_2437_;
goto v___jp_2753_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec_ref_known(v_mod_x3f_2429_, 1);
lean_dec_ref_known(v___x_2802_, 3);
lean_dec(v_term_2430_);
lean_dec(v_p_2428_);
lean_dec_ref(v_params_2427_);
v_a_2828_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2805_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2805_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
else
{
v___y_2788_ = v_a_2432_;
v___y_2789_ = v_a_2433_;
v___y_2790_ = v_a_2434_;
v___y_2791_ = v_a_2435_;
v___y_2792_ = v___x_2802_;
v___y_2793_ = v_a_2437_;
goto v___jp_2787_;
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec_ref_known(v___x_2802_, 3);
lean_dec(v_term_2430_);
lean_dec(v_mod_x3f_2429_);
lean_dec(v_p_2428_);
lean_dec_ref(v_params_2427_);
v_a_2836_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2803_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2803_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
v___jp_2439_:
{
lean_object* v_config_2441_; lean_object* v_extensions_2442_; lean_object* v_extra_2443_; lean_object* v_extraInj_2444_; lean_object* v_extraFacts_2445_; lean_object* v_symPrios_2446_; lean_object* v_norm_2447_; lean_object* v_normProcs_2448_; lean_object* v_anchorRefs_x3f_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2458_; 
v_config_2441_ = lean_ctor_get(v_params_2427_, 0);
v_extensions_2442_ = lean_ctor_get(v_params_2427_, 1);
v_extra_2443_ = lean_ctor_get(v_params_2427_, 2);
v_extraInj_2444_ = lean_ctor_get(v_params_2427_, 3);
v_extraFacts_2445_ = lean_ctor_get(v_params_2427_, 4);
v_symPrios_2446_ = lean_ctor_get(v_params_2427_, 5);
v_norm_2447_ = lean_ctor_get(v_params_2427_, 6);
v_normProcs_2448_ = lean_ctor_get(v_params_2427_, 7);
v_anchorRefs_x3f_2449_ = lean_ctor_get(v_params_2427_, 8);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_params_2427_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2451_ = v_params_2427_;
v_isShared_2452_ = v_isSharedCheck_2458_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_anchorRefs_x3f_2449_);
lean_inc(v_normProcs_2448_);
lean_inc(v_norm_2447_);
lean_inc(v_symPrios_2446_);
lean_inc(v_extraFacts_2445_);
lean_inc(v_extraInj_2444_);
lean_inc(v_extra_2443_);
lean_inc(v_extensions_2442_);
lean_inc(v_config_2441_);
lean_dec(v_params_2427_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2458_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2453_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2445_, v___y_2440_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 4, v___x_2453_);
v___x_2455_ = v___x_2451_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_config_2441_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_extensions_2442_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_extra_2443_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_extraInj_2444_);
lean_ctor_set(v_reuseFailAlloc_2457_, 4, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2457_, 5, v_symPrios_2446_);
lean_ctor_set(v_reuseFailAlloc_2457_, 6, v_norm_2447_);
lean_ctor_set(v_reuseFailAlloc_2457_, 7, v_normProcs_2448_);
lean_ctor_set(v_reuseFailAlloc_2457_, 8, v_anchorRefs_x3f_2449_);
v___x_2455_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
return v___x_2456_;
}
}
}
v___jp_2459_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2469_ = lean_array_get_size(v___y_2460_);
lean_dec_ref(v___y_2460_);
v___x_2470_ = lean_unsigned_to_nat(0u);
v___x_2471_ = lean_nat_dec_eq(v___x_2469_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v___y_2461_);
lean_dec_ref(v_params_2427_);
v___x_2472_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2473_ = l_Lean_indentExpr(v___y_2462_);
v___x_2474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2474_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
lean_dec_ref(v___y_2467_);
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2475_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2475_);
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
else
{
lean_dec_ref(v___y_2467_);
lean_dec_ref(v___y_2462_);
v___y_2440_ = v___y_2461_;
goto v___jp_2439_;
}
}
v___jp_2484_:
{
lean_object* v___x_2501_; 
lean_inc(v___y_2500_);
lean_inc(v___y_2498_);
lean_inc_ref(v___y_2497_);
v___x_2501_ = lean_apply_7(v___y_2488_, v___y_2485_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, lean_box(0));
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2511_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2504_ = v___x_2501_;
v_isShared_2505_ = v_isSharedCheck_2511_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2501_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2511_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2506_ = l_Lean_PersistentArray_push___redArg(v___y_2489_, v_a_2502_);
v___x_2507_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2507_, 0, v___y_2493_);
lean_ctor_set(v___x_2507_, 1, v___y_2490_);
lean_ctor_set(v___x_2507_, 2, v___x_2506_);
lean_ctor_set(v___x_2507_, 3, v___y_2492_);
lean_ctor_set(v___x_2507_, 4, v___y_2495_);
lean_ctor_set(v___x_2507_, 5, v___y_2487_);
lean_ctor_set(v___x_2507_, 6, v___y_2491_);
lean_ctor_set(v___x_2507_, 7, v___y_2486_);
lean_ctor_set(v___x_2507_, 8, v___y_2494_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v___x_2507_);
v___x_2509_ = v___x_2504_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v___y_2487_);
lean_dec_ref(v___y_2486_);
v_a_2512_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2501_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2501_);
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
lean_object* v___x_2537_; 
v___x_2537_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2431_, v___y_2523_, v___y_2533_, v___y_2526_, v___y_2527_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref_known(v___x_2537_, 1);
v___y_2485_ = v___y_2521_;
v___y_2486_ = v___y_2522_;
v___y_2487_ = v___y_2524_;
v___y_2488_ = v___y_2525_;
v___y_2489_ = v___y_2528_;
v___y_2490_ = v___y_2534_;
v___y_2491_ = v___y_2530_;
v___y_2492_ = v___y_2535_;
v___y_2493_ = v___y_2529_;
v___y_2494_ = v___y_2532_;
v___y_2495_ = v___y_2531_;
v___y_2496_ = v___y_2536_;
v___y_2497_ = v___y_2523_;
v___y_2498_ = v___y_2533_;
v___y_2499_ = v___y_2526_;
v___y_2500_ = v___y_2527_;
goto v___jp_2484_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec_ref(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
v___jp_2546_:
{
lean_object* v_extra_2553_; 
v_extra_2553_ = lean_ctor_get(v_params_2427_, 2);
lean_inc_ref(v_extra_2553_);
if (lean_obj_tag(v___y_2547_) == 2)
{
lean_object* v_config_2554_; lean_object* v_extensions_2555_; lean_object* v_extraInj_2556_; lean_object* v_extraFacts_2557_; lean_object* v_symPrios_2558_; lean_object* v_norm_2559_; lean_object* v_normProcs_2560_; lean_object* v_anchorRefs_x3f_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2616_; 
v_config_2554_ = lean_ctor_get(v_params_2427_, 0);
v_extensions_2555_ = lean_ctor_get(v_params_2427_, 1);
v_extraInj_2556_ = lean_ctor_get(v_params_2427_, 3);
v_extraFacts_2557_ = lean_ctor_get(v_params_2427_, 4);
v_symPrios_2558_ = lean_ctor_get(v_params_2427_, 5);
v_norm_2559_ = lean_ctor_get(v_params_2427_, 6);
v_normProcs_2560_ = lean_ctor_get(v_params_2427_, 7);
v_anchorRefs_x3f_2561_ = lean_ctor_get(v_params_2427_, 8);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_params_2427_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; 
v_unused_2617_ = lean_ctor_get(v_params_2427_, 2);
lean_dec(v_unused_2617_);
v___x_2563_ = v_params_2427_;
v_isShared_2564_ = v_isSharedCheck_2616_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_anchorRefs_x3f_2561_);
lean_inc(v_normProcs_2560_);
lean_inc(v_norm_2559_);
lean_inc(v_symPrios_2558_);
lean_inc(v_extraFacts_2557_);
lean_inc(v_extraInj_2556_);
lean_inc(v_extensions_2555_);
lean_inc(v_config_2554_);
lean_dec(v_params_2427_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2616_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v_size_2565_; uint8_t v_gen_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2615_; 
v_size_2565_ = lean_ctor_get(v_extra_2553_, 2);
v_gen_2566_ = lean_ctor_get_uint8(v___y_2547_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___y_2547_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2568_ = v___y_2547_;
v_isShared_2569_ = v_isSharedCheck_2615_;
goto v_resetjp_2567_;
}
else
{
lean_dec(v___y_2547_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2615_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; 
v___x_2570_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2431_, v___y_2549_, v___y_2548_, v___y_2552_, v___y_2551_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v___x_2572_; 
lean_dec_ref_known(v___x_2570_, 1);
if (v_isShared_2569_ == 0)
{
lean_ctor_set_tag(v___x_2568_, 0);
v___x_2572_ = v___x_2568_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2606_, 0, v_gen_2566_);
v___x_2572_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; 
lean_inc_ref(v___y_2550_);
lean_inc(v___y_2551_);
lean_inc_ref(v___y_2552_);
lean_inc(v___y_2548_);
lean_inc_ref(v___y_2549_);
lean_inc(v_size_2565_);
v___x_2573_ = lean_apply_7(v___y_2550_, v___x_2572_, v_size_2565_, v___y_2549_, v___y_2548_, v___y_2552_, v___y_2551_, lean_box(0));
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v___x_2575_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2575_, 0, v_gen_2566_);
lean_inc(v___y_2551_);
lean_inc(v___y_2548_);
lean_inc_ref(v___y_2549_);
lean_inc(v_size_2565_);
v___x_2576_ = lean_apply_7(v___y_2550_, v___x_2575_, v_size_2565_, v___y_2549_, v___y_2548_, v___y_2552_, v___y_2551_, lean_box(0));
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2589_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2589_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2589_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2584_; 
v___x_2581_ = l_Lean_PersistentArray_push___redArg(v_extra_2553_, v_a_2574_);
v___x_2582_ = l_Lean_PersistentArray_push___redArg(v___x_2581_, v_a_2577_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 2, v___x_2582_);
v___x_2584_ = v___x_2563_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_config_2554_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_extensions_2555_);
lean_ctor_set(v_reuseFailAlloc_2588_, 2, v___x_2582_);
lean_ctor_set(v_reuseFailAlloc_2588_, 3, v_extraInj_2556_);
lean_ctor_set(v_reuseFailAlloc_2588_, 4, v_extraFacts_2557_);
lean_ctor_set(v_reuseFailAlloc_2588_, 5, v_symPrios_2558_);
lean_ctor_set(v_reuseFailAlloc_2588_, 6, v_norm_2559_);
lean_ctor_set(v_reuseFailAlloc_2588_, 7, v_normProcs_2560_);
lean_ctor_set(v_reuseFailAlloc_2588_, 8, v_anchorRefs_x3f_2561_);
v___x_2584_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
lean_object* v___x_2586_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2584_);
v___x_2586_ = v___x_2579_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v_a_2574_);
lean_del_object(v___x_2563_);
lean_dec(v_anchorRefs_x3f_2561_);
lean_dec_ref(v_normProcs_2560_);
lean_dec_ref(v_norm_2559_);
lean_dec_ref(v_symPrios_2558_);
lean_dec_ref(v_extraFacts_2557_);
lean_dec_ref(v_extraInj_2556_);
lean_dec_ref(v_extensions_2555_);
lean_dec_ref(v_config_2554_);
lean_dec_ref(v_extra_2553_);
v_a_2590_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2576_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2576_);
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
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_del_object(v___x_2563_);
lean_dec(v_anchorRefs_x3f_2561_);
lean_dec_ref(v_normProcs_2560_);
lean_dec_ref(v_norm_2559_);
lean_dec_ref(v_symPrios_2558_);
lean_dec_ref(v_extraFacts_2557_);
lean_dec_ref(v_extraInj_2556_);
lean_dec_ref(v_extensions_2555_);
lean_dec_ref(v_config_2554_);
lean_dec_ref(v_extra_2553_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v___y_2550_);
v_a_2598_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2573_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2573_);
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
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_del_object(v___x_2568_);
lean_del_object(v___x_2563_);
lean_dec(v_anchorRefs_x3f_2561_);
lean_dec_ref(v_normProcs_2560_);
lean_dec_ref(v_norm_2559_);
lean_dec_ref(v_symPrios_2558_);
lean_dec_ref(v_extraFacts_2557_);
lean_dec_ref(v_extraInj_2556_);
lean_dec_ref(v_extensions_2555_);
lean_dec_ref(v_config_2554_);
lean_dec_ref(v_extra_2553_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v___y_2550_);
v_a_2607_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2570_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2570_);
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
else
{
switch(lean_obj_tag(v___y_2547_))
{
case 0:
{
lean_object* v_config_2618_; lean_object* v_extensions_2619_; lean_object* v_extraInj_2620_; lean_object* v_extraFacts_2621_; lean_object* v_symPrios_2622_; lean_object* v_norm_2623_; lean_object* v_normProcs_2624_; lean_object* v_anchorRefs_x3f_2625_; lean_object* v_size_2626_; 
v_config_2618_ = lean_ctor_get(v_params_2427_, 0);
lean_inc_ref(v_config_2618_);
v_extensions_2619_ = lean_ctor_get(v_params_2427_, 1);
lean_inc_ref(v_extensions_2619_);
v_extraInj_2620_ = lean_ctor_get(v_params_2427_, 3);
lean_inc_ref(v_extraInj_2620_);
v_extraFacts_2621_ = lean_ctor_get(v_params_2427_, 4);
lean_inc_ref(v_extraFacts_2621_);
v_symPrios_2622_ = lean_ctor_get(v_params_2427_, 5);
lean_inc_ref(v_symPrios_2622_);
v_norm_2623_ = lean_ctor_get(v_params_2427_, 6);
lean_inc_ref(v_norm_2623_);
v_normProcs_2624_ = lean_ctor_get(v_params_2427_, 7);
lean_inc_ref(v_normProcs_2624_);
v_anchorRefs_x3f_2625_ = lean_ctor_get(v_params_2427_, 8);
lean_inc(v_anchorRefs_x3f_2625_);
lean_dec_ref(v_params_2427_);
v_size_2626_ = lean_ctor_get(v_extra_2553_, 2);
lean_inc(v_size_2626_);
v___y_2521_ = v___y_2547_;
v___y_2522_ = v_normProcs_2624_;
v___y_2523_ = v___y_2549_;
v___y_2524_ = v_symPrios_2622_;
v___y_2525_ = v___y_2550_;
v___y_2526_ = v___y_2552_;
v___y_2527_ = v___y_2551_;
v___y_2528_ = v_extra_2553_;
v___y_2529_ = v_config_2618_;
v___y_2530_ = v_norm_2623_;
v___y_2531_ = v_extraFacts_2621_;
v___y_2532_ = v_anchorRefs_x3f_2625_;
v___y_2533_ = v___y_2548_;
v___y_2534_ = v_extensions_2619_;
v___y_2535_ = v_extraInj_2620_;
v___y_2536_ = v_size_2626_;
goto v___jp_2520_;
}
case 1:
{
lean_object* v_config_2627_; lean_object* v_extensions_2628_; lean_object* v_extraInj_2629_; lean_object* v_extraFacts_2630_; lean_object* v_symPrios_2631_; lean_object* v_norm_2632_; lean_object* v_normProcs_2633_; lean_object* v_anchorRefs_x3f_2634_; lean_object* v_size_2635_; 
v_config_2627_ = lean_ctor_get(v_params_2427_, 0);
lean_inc_ref(v_config_2627_);
v_extensions_2628_ = lean_ctor_get(v_params_2427_, 1);
lean_inc_ref(v_extensions_2628_);
v_extraInj_2629_ = lean_ctor_get(v_params_2427_, 3);
lean_inc_ref(v_extraInj_2629_);
v_extraFacts_2630_ = lean_ctor_get(v_params_2427_, 4);
lean_inc_ref(v_extraFacts_2630_);
v_symPrios_2631_ = lean_ctor_get(v_params_2427_, 5);
lean_inc_ref(v_symPrios_2631_);
v_norm_2632_ = lean_ctor_get(v_params_2427_, 6);
lean_inc_ref(v_norm_2632_);
v_normProcs_2633_ = lean_ctor_get(v_params_2427_, 7);
lean_inc_ref(v_normProcs_2633_);
v_anchorRefs_x3f_2634_ = lean_ctor_get(v_params_2427_, 8);
lean_inc(v_anchorRefs_x3f_2634_);
lean_dec_ref(v_params_2427_);
v_size_2635_ = lean_ctor_get(v_extra_2553_, 2);
lean_inc(v_size_2635_);
v___y_2521_ = v___y_2547_;
v___y_2522_ = v_normProcs_2633_;
v___y_2523_ = v___y_2549_;
v___y_2524_ = v_symPrios_2631_;
v___y_2525_ = v___y_2550_;
v___y_2526_ = v___y_2552_;
v___y_2527_ = v___y_2551_;
v___y_2528_ = v_extra_2553_;
v___y_2529_ = v_config_2627_;
v___y_2530_ = v_norm_2632_;
v___y_2531_ = v_extraFacts_2630_;
v___y_2532_ = v_anchorRefs_x3f_2634_;
v___y_2533_ = v___y_2548_;
v___y_2534_ = v_extensions_2628_;
v___y_2535_ = v_extraInj_2629_;
v___y_2536_ = v_size_2635_;
goto v___jp_2520_;
}
default: 
{
lean_object* v_config_2636_; lean_object* v_extensions_2637_; lean_object* v_extraInj_2638_; lean_object* v_extraFacts_2639_; lean_object* v_symPrios_2640_; lean_object* v_norm_2641_; lean_object* v_normProcs_2642_; lean_object* v_anchorRefs_x3f_2643_; lean_object* v_size_2644_; 
v_config_2636_ = lean_ctor_get(v_params_2427_, 0);
lean_inc_ref(v_config_2636_);
v_extensions_2637_ = lean_ctor_get(v_params_2427_, 1);
lean_inc_ref(v_extensions_2637_);
v_extraInj_2638_ = lean_ctor_get(v_params_2427_, 3);
lean_inc_ref(v_extraInj_2638_);
v_extraFacts_2639_ = lean_ctor_get(v_params_2427_, 4);
lean_inc_ref(v_extraFacts_2639_);
v_symPrios_2640_ = lean_ctor_get(v_params_2427_, 5);
lean_inc_ref(v_symPrios_2640_);
v_norm_2641_ = lean_ctor_get(v_params_2427_, 6);
lean_inc_ref(v_norm_2641_);
v_normProcs_2642_ = lean_ctor_get(v_params_2427_, 7);
lean_inc_ref(v_normProcs_2642_);
v_anchorRefs_x3f_2643_ = lean_ctor_get(v_params_2427_, 8);
lean_inc(v_anchorRefs_x3f_2643_);
lean_dec_ref(v_params_2427_);
v_size_2644_ = lean_ctor_get(v_extra_2553_, 2);
lean_inc(v_size_2644_);
v___y_2485_ = v___y_2547_;
v___y_2486_ = v_normProcs_2642_;
v___y_2487_ = v_symPrios_2640_;
v___y_2488_ = v___y_2550_;
v___y_2489_ = v_extra_2553_;
v___y_2490_ = v_extensions_2637_;
v___y_2491_ = v_norm_2641_;
v___y_2492_ = v_extraInj_2638_;
v___y_2493_ = v_config_2636_;
v___y_2494_ = v_anchorRefs_x3f_2643_;
v___y_2495_ = v_extraFacts_2639_;
v___y_2496_ = v_size_2644_;
v___y_2497_ = v___y_2549_;
v___y_2498_ = v___y_2548_;
v___y_2499_ = v___y_2552_;
v___y_2500_ = v___y_2551_;
goto v___jp_2484_;
}
}
}
}
v___jp_2645_:
{
if (lean_obj_tag(v_mod_x3f_2429_) == 0)
{
v___y_2460_ = v___y_2646_;
v___y_2461_ = v___y_2648_;
v___y_2462_ = v___y_2654_;
v___y_2463_ = v___y_2653_;
v___y_2464_ = v___y_2652_;
v___y_2465_ = v___y_2649_;
v___y_2466_ = v___y_2647_;
v___y_2467_ = v___y_2651_;
v___y_2468_ = v___y_2650_;
goto v___jp_2459_;
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec_ref_known(v_mod_x3f_2429_, 1);
lean_dec_ref(v___y_2648_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v_params_2427_);
v___x_2655_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2656_ = l_Lean_indentExpr(v___y_2654_);
v___x_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2655_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2657_, v___y_2653_, v___y_2652_, v___y_2649_, v___y_2647_, v___y_2651_, v___y_2650_);
lean_dec_ref(v___y_2651_);
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
v___jp_2667_:
{
uint8_t v___x_2680_; 
v___x_2680_ = l_Lean_Expr_isForall(v___y_2673_);
if (v___x_2680_ == 0)
{
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2670_);
v___y_2646_ = v___y_2669_;
v___y_2647_ = v___y_2677_;
v___y_2648_ = v___y_2671_;
v___y_2649_ = v___y_2676_;
v___y_2650_ = v___y_2679_;
v___y_2651_ = v___y_2678_;
v___y_2652_ = v___y_2675_;
v___y_2653_ = v___y_2674_;
v___y_2654_ = v___y_2673_;
goto v___jp_2645_;
}
else
{
if (v___y_2668_ == 0)
{
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___y_2671_);
lean_dec_ref(v___y_2669_);
lean_dec(v_mod_x3f_2429_);
v___y_2547_ = v___y_2670_;
v___y_2548_ = v___y_2677_;
v___y_2549_ = v___y_2676_;
v___y_2550_ = v___y_2672_;
v___y_2551_ = v___y_2679_;
v___y_2552_ = v___y_2678_;
goto v___jp_2546_;
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2681_ = lean_array_get_size(v___y_2669_);
v___x_2682_ = lean_unsigned_to_nat(0u);
v___x_2683_ = lean_nat_dec_eq(v___x_2681_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___y_2671_);
lean_dec_ref(v___y_2669_);
lean_dec(v_mod_x3f_2429_);
v___y_2547_ = v___y_2670_;
v___y_2548_ = v___y_2677_;
v___y_2549_ = v___y_2676_;
v___y_2550_ = v___y_2672_;
v___y_2551_ = v___y_2679_;
v___y_2552_ = v___y_2678_;
goto v___jp_2546_;
}
else
{
if (lean_obj_tag(v_mod_x3f_2429_) == 0)
{
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2670_);
v___y_2646_ = v___y_2669_;
v___y_2647_ = v___y_2677_;
v___y_2648_ = v___y_2671_;
v___y_2649_ = v___y_2676_;
v___y_2650_ = v___y_2679_;
v___y_2651_ = v___y_2678_;
v___y_2652_ = v___y_2675_;
v___y_2653_ = v___y_2674_;
v___y_2654_ = v___y_2673_;
goto v___jp_2645_;
}
else
{
lean_dec_ref_known(v_mod_x3f_2429_, 1);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___y_2671_);
lean_dec_ref(v___y_2669_);
v___y_2547_ = v___y_2670_;
v___y_2548_ = v___y_2677_;
v___y_2549_ = v___y_2676_;
v___y_2550_ = v___y_2672_;
v___y_2551_ = v___y_2679_;
v___y_2552_ = v___y_2678_;
goto v___jp_2546_;
}
}
}
}
}
v___jp_2684_:
{
lean_object* v___x_2692_; uint8_t v___x_2693_; lean_object* v___x_2694_; lean_object* v___f_2695_; lean_object* v___x_2696_; 
v___x_2692_ = lean_box(0);
v___x_2693_ = 1;
v___x_2694_ = lean_box(v___x_2693_);
lean_inc(v_p_2428_);
v___f_2695_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2695_, 0, v_p_2428_);
lean_closure_set(v___f_2695_, 1, v_term_2430_);
lean_closure_set(v___f_2695_, 2, v___x_2692_);
lean_closure_set(v___f_2695_, 3, v___x_2694_);
v___x_2696_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2695_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2744_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2744_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2744_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
if (lean_obj_tag(v_a_2697_) == 1)
{
lean_object* v_val_2701_; lean_object* v_snd_2702_; lean_object* v_fst_2703_; lean_object* v_fst_2704_; lean_object* v_snd_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; 
lean_del_object(v___x_2699_);
v_val_2701_ = lean_ctor_get(v_a_2697_, 0);
lean_inc(v_val_2701_);
lean_dec_ref_known(v_a_2697_, 1);
v_snd_2702_ = lean_ctor_get(v_val_2701_, 1);
lean_inc(v_snd_2702_);
v_fst_2703_ = lean_ctor_get(v_val_2701_, 0);
lean_inc_n(v_fst_2703_, 2);
lean_dec(v_val_2701_);
v_fst_2704_ = lean_ctor_get(v_snd_2702_, 0);
lean_inc_n(v_fst_2704_, 3);
v_snd_2705_ = lean_ctor_get(v_snd_2702_, 1);
lean_inc(v_snd_2705_);
lean_dec(v_snd_2702_);
v___x_2706_ = lean_box(v___x_2693_);
v___x_2707_ = lean_box(v_minIndexable_2431_);
lean_inc_ref(v_params_2427_);
v___f_2708_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed), 13, 6);
lean_closure_set(v___f_2708_, 0, v_params_2427_);
lean_closure_set(v___f_2708_, 1, v_p_2428_);
lean_closure_set(v___f_2708_, 2, v_fst_2703_);
lean_closure_set(v___f_2708_, 3, v_fst_2704_);
lean_closure_set(v___f_2708_, 4, v___x_2706_);
lean_closure_set(v___f_2708_, 5, v___x_2707_);
lean_inc(v___y_2691_);
lean_inc_ref(v___y_2690_);
lean_inc(v___y_2689_);
lean_inc_ref(v___y_2688_);
v___x_2709_ = lean_infer_type(v_fst_2704_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc_n(v_a_2710_, 2);
lean_dec_ref_known(v___x_2709_, 1);
v___x_2711_ = l_Lean_Meta_isProp(v_a_2710_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; uint8_t v___x_2713_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2713_ = lean_unbox(v_a_2712_);
lean_dec(v_a_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_dec(v_a_2710_);
lean_dec_ref(v___f_2708_);
lean_dec(v_snd_2705_);
lean_dec(v_fst_2704_);
lean_dec(v_fst_2703_);
lean_dec(v_kind_2685_);
lean_dec(v_mod_x3f_2429_);
lean_dec_ref(v_params_2427_);
v___x_2714_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2715_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2714_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec_ref(v___y_2690_);
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
else
{
uint8_t v___x_2724_; 
v___x_2724_ = lean_unbox(v_snd_2705_);
lean_dec(v_snd_2705_);
v___y_2668_ = v___x_2724_;
v___y_2669_ = v_fst_2703_;
v___y_2670_ = v_kind_2685_;
v___y_2671_ = v_fst_2704_;
v___y_2672_ = v___f_2708_;
v___y_2673_ = v_a_2710_;
v___y_2674_ = v___y_2686_;
v___y_2675_ = v___y_2687_;
v___y_2676_ = v___y_2688_;
v___y_2677_ = v___y_2689_;
v___y_2678_ = v___y_2690_;
v___y_2679_ = v___y_2691_;
goto v___jp_2667_;
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v_a_2710_);
lean_dec_ref(v___f_2708_);
lean_dec(v_snd_2705_);
lean_dec(v_fst_2704_);
lean_dec(v_fst_2703_);
lean_dec_ref(v___y_2690_);
lean_dec(v_kind_2685_);
lean_dec(v_mod_x3f_2429_);
lean_dec_ref(v_params_2427_);
v_a_2725_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2711_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2711_);
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
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec_ref(v___f_2708_);
lean_dec(v_snd_2705_);
lean_dec(v_fst_2704_);
lean_dec(v_fst_2703_);
lean_dec_ref(v___y_2690_);
lean_dec(v_kind_2685_);
lean_dec(v_mod_x3f_2429_);
lean_dec_ref(v_params_2427_);
v_a_2733_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2709_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2709_);
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
lean_object* v___x_2742_; 
lean_dec(v_a_2697_);
lean_dec_ref(v___y_2690_);
lean_dec(v_kind_2685_);
lean_dec(v_mod_x3f_2429_);
lean_dec(v_p_2428_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v_params_2427_);
v___x_2742_ = v___x_2699_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_params_2427_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec_ref(v___y_2690_);
lean_dec(v_kind_2685_);
lean_dec(v_mod_x3f_2429_);
lean_dec(v_p_2428_);
lean_dec_ref(v_params_2427_);
v_a_2745_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2696_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2696_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
v___jp_2753_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
v___x_2760_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2761_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2760_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec_ref(v___y_2758_);
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
v___jp_2770_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
v___x_2777_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2778_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2777_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec_ref(v___y_2775_);
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
v___jp_2787_:
{
lean_object* v___x_2794_; 
v___x_2794_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_kind_2685_ = v___x_2794_;
v___y_2686_ = v___y_2788_;
v___y_2687_ = v___y_2789_;
v___y_2688_ = v___y_2790_;
v___y_2689_ = v___y_2791_;
v___y_2690_ = v___y_2792_;
v___y_2691_ = v___y_2793_;
goto v___jp_2684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2844_, lean_object* v_p_2845_, lean_object* v_mod_x3f_2846_, lean_object* v_term_2847_, lean_object* v_minIndexable_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
uint8_t v_minIndexable_boxed_2856_; lean_object* v_res_2857_; 
v_minIndexable_boxed_2856_ = lean_unbox(v_minIndexable_2848_);
v_res_2857_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2844_, v_p_2845_, v_mod_x3f_2846_, v_term_2847_, v_minIndexable_boxed_2856_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(uint8_t v___x_2858_, uint8_t v___x_2859_, lean_object* v_as_2860_, size_t v_i_2861_, size_t v_stop_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2858_, v___x_2859_, v_as_2860_, v_i_2861_, v_stop_2862_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v___x_2871_, lean_object* v___x_2872_, lean_object* v_as_2873_, lean_object* v_i_2874_, lean_object* v_stop_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
uint8_t v___x_16187__boxed_2883_; uint8_t v___x_16188__boxed_2884_; size_t v_i_boxed_2885_; size_t v_stop_boxed_2886_; lean_object* v_res_2887_; 
v___x_16187__boxed_2883_ = lean_unbox(v___x_2871_);
v___x_16188__boxed_2884_ = lean_unbox(v___x_2872_);
v_i_boxed_2885_ = lean_unbox_usize(v_i_2874_);
lean_dec(v_i_2874_);
v_stop_boxed_2886_ = lean_unbox_usize(v_stop_2875_);
lean_dec(v_stop_2875_);
v_res_2887_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v___x_16187__boxed_2883_, v___x_16188__boxed_2884_, v_as_2873_, v_i_boxed_2885_, v_stop_boxed_2886_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec_ref(v_as_2873_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(lean_object* v_00_u03b1_2888_, lean_object* v_msg_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___boxed(lean_object* v_00_u03b1_2898_, lean_object* v_msg_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(v_00_u03b1_2898_, v_msg_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(lean_object* v_msgData_2908_, lean_object* v_macroStack_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2908_, v_macroStack_2909_, v___y_2914_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___boxed(lean_object* v_msgData_2918_, lean_object* v_macroStack_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(v_msgData_2918_, v_macroStack_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2928_, lean_object* v_val_2929_, lean_object* v___x_2930_, uint8_t v___x_2931_, lean_object* v_____r_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; lean_object* v_ext_2941_; lean_object* v_toEnvExtension_2942_; lean_object* v_env_2943_; lean_object* v_config_2944_; lean_object* v_extensions_2945_; lean_object* v_extra_2946_; lean_object* v_extraInj_2947_; lean_object* v_extraFacts_2948_; lean_object* v_symPrios_2949_; lean_object* v_norm_2950_; lean_object* v_normProcs_2951_; lean_object* v_anchorRefs_x3f_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2964_; 
v___x_2940_ = lean_st_ref_get(v___y_2938_);
v_ext_2941_ = lean_ctor_get(v_val_2929_, 1);
v_toEnvExtension_2942_ = lean_ctor_get(v_ext_2941_, 0);
v_env_2943_ = lean_ctor_get(v___x_2940_, 0);
lean_inc_ref(v_env_2943_);
lean_dec(v___x_2940_);
v_config_2944_ = lean_ctor_get(v_params_2928_, 0);
v_extensions_2945_ = lean_ctor_get(v_params_2928_, 1);
v_extra_2946_ = lean_ctor_get(v_params_2928_, 2);
v_extraInj_2947_ = lean_ctor_get(v_params_2928_, 3);
v_extraFacts_2948_ = lean_ctor_get(v_params_2928_, 4);
v_symPrios_2949_ = lean_ctor_get(v_params_2928_, 5);
v_norm_2950_ = lean_ctor_get(v_params_2928_, 6);
v_normProcs_2951_ = lean_ctor_get(v_params_2928_, 7);
v_anchorRefs_x3f_2952_ = lean_ctor_get(v_params_2928_, 8);
v_isSharedCheck_2964_ = !lean_is_exclusive(v_params_2928_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2954_ = v_params_2928_;
v_isShared_2955_ = v_isSharedCheck_2964_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_anchorRefs_x3f_2952_);
lean_inc(v_normProcs_2951_);
lean_inc(v_norm_2950_);
lean_inc(v_symPrios_2949_);
lean_inc(v_extraFacts_2948_);
lean_inc(v_extraInj_2947_);
lean_inc(v_extra_2946_);
lean_inc(v_extensions_2945_);
lean_inc(v_config_2944_);
lean_dec(v_params_2928_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2964_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v_asyncMode_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2960_; 
v_asyncMode_2956_ = lean_ctor_get(v_toEnvExtension_2942_, 2);
v___x_2957_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2930_, v_val_2929_, v_env_2943_, v_asyncMode_2956_, v___x_2931_);
v___x_2958_ = lean_array_push(v_extensions_2945_, v___x_2957_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v___x_2958_);
v___x_2960_ = v___x_2954_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_config_2944_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_2963_, 2, v_extra_2946_);
lean_ctor_set(v_reuseFailAlloc_2963_, 3, v_extraInj_2947_);
lean_ctor_set(v_reuseFailAlloc_2963_, 4, v_extraFacts_2948_);
lean_ctor_set(v_reuseFailAlloc_2963_, 5, v_symPrios_2949_);
lean_ctor_set(v_reuseFailAlloc_2963_, 6, v_norm_2950_);
lean_ctor_set(v_reuseFailAlloc_2963_, 7, v_normProcs_2951_);
lean_ctor_set(v_reuseFailAlloc_2963_, 8, v_anchorRefs_x3f_2952_);
v___x_2960_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2965_, lean_object* v_val_2966_, lean_object* v___x_2967_, lean_object* v___x_2968_, lean_object* v_____r_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
uint8_t v___x_31687__boxed_2977_; lean_object* v_res_2978_; 
v___x_31687__boxed_2977_ = lean_unbox(v___x_2968_);
v_res_2978_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2965_, v_val_2966_, v___x_2967_, v___x_31687__boxed_2977_, v_____r_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec_ref(v___x_2967_);
lean_dec_ref(v_val_2966_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2979_, lean_object* v_id_2980_, uint8_t v_minIndexable_2981_, lean_object* v_as_x27_2982_, lean_object* v_b_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
if (lean_obj_tag(v_as_x27_2982_) == 0)
{
lean_object* v___x_2989_; 
lean_dec(v_id_2980_);
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v_b_2983_);
return v___x_2989_;
}
else
{
lean_object* v_head_2990_; lean_object* v_tail_2991_; lean_object* v_toCold_2992_; lean_object* v_currRecDepth_2993_; lean_object* v_ref_2994_; uint16_t v_optionFlags_2995_; uint8_t v_suppressElabErrors_2996_; uint8_t v_isRecordingDeps_2997_; uint8_t v___x_2998_; lean_object* v___x_2999_; lean_object* v_ref_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_head_2990_ = lean_ctor_get(v_as_x27_2982_, 0);
v_tail_2991_ = lean_ctor_get(v_as_x27_2982_, 1);
v_toCold_2992_ = lean_ctor_get(v___y_2986_, 0);
v_currRecDepth_2993_ = lean_ctor_get(v___y_2986_, 1);
v_ref_2994_ = lean_ctor_get(v___y_2986_, 2);
v_optionFlags_2995_ = lean_ctor_get_uint16(v___y_2986_, sizeof(void*)*3);
v_suppressElabErrors_2996_ = lean_ctor_get_uint8(v___y_2986_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2997_ = lean_ctor_get_uint8(v___y_2986_, sizeof(void*)*3 + 3);
v___x_2998_ = 0;
v___x_2999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_ref_3000_ = l_Lean_replaceRef(v_p_2979_, v_ref_2994_);
lean_inc(v_currRecDepth_2993_);
lean_inc_ref(v_toCold_2992_);
v___x_3001_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3001_, 0, v_toCold_2992_);
lean_ctor_set(v___x_3001_, 1, v_currRecDepth_2993_);
lean_ctor_set(v___x_3001_, 2, v_ref_3000_);
lean_ctor_set_uint16(v___x_3001_, sizeof(void*)*3, v_optionFlags_2995_);
lean_ctor_set_uint8(v___x_3001_, sizeof(void*)*3 + 2, v_suppressElabErrors_2996_);
lean_ctor_set_uint8(v___x_3001_, sizeof(void*)*3 + 3, v_isRecordingDeps_2997_);
lean_inc(v_head_2990_);
lean_inc(v_id_2980_);
v___x_3002_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2983_, v_id_2980_, v_head_2990_, v___x_2999_, v_minIndexable_2981_, v___x_2998_, v___x_2998_, v___y_2984_, v___y_2985_, v___x_3001_, v___y_2987_);
lean_dec_ref_known(v___x_3001_, 3);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3002_, 1);
v_as_x27_2982_ = v_tail_2991_;
v_b_2983_ = v_a_3003_;
goto _start;
}
else
{
lean_dec(v_id_2980_);
return v___x_3002_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_3005_, lean_object* v_id_3006_, lean_object* v_minIndexable_3007_, lean_object* v_as_x27_3008_, lean_object* v_b_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
uint8_t v_minIndexable_boxed_3015_; lean_object* v_res_3016_; 
v_minIndexable_boxed_3015_ = lean_unbox(v_minIndexable_3007_);
v_res_3016_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3005_, v_id_3006_, v_minIndexable_boxed_3015_, v_as_x27_3008_, v_b_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v_as_x27_3008_);
lean_dec(v_p_3005_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
if (lean_obj_tag(v_a_3018_) == 0)
{
lean_object* v___x_3020_; 
v___x_3020_ = l_List_reverse___redArg(v_a_3019_);
return v___x_3020_;
}
else
{
lean_object* v_head_3021_; lean_object* v_tail_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3033_; 
v_head_3021_ = lean_ctor_get(v_a_3018_, 0);
v_tail_3022_ = lean_ctor_get(v_a_3018_, 1);
v_isSharedCheck_3033_ = !lean_is_exclusive(v_a_3018_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3024_ = v_a_3018_;
v_isShared_3025_ = v_isSharedCheck_3033_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_tail_3022_);
lean_inc(v_head_3021_);
lean_dec(v_a_3018_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3033_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v_kind_3026_; uint8_t v___x_3027_; 
v_kind_3026_ = lean_ctor_get(v_head_3021_, 6);
v___x_3027_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_3026_, v_k_3017_);
if (v___x_3027_ == 0)
{
lean_del_object(v___x_3024_);
lean_dec(v_head_3021_);
v_a_3018_ = v_tail_3022_;
goto _start;
}
else
{
lean_object* v___x_3030_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 1, v_a_3019_);
v___x_3030_ = v___x_3024_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_head_3021_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_a_3019_);
v___x_3030_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
v_a_3018_ = v_tail_3022_;
v_a_3019_ = v___x_3030_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_3034_, v_a_3035_, v_a_3036_);
lean_dec(v_k_3034_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_3038_, lean_object* v_msg_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_toCold_3047_; lean_object* v_currRecDepth_3048_; lean_object* v_ref_3049_; uint16_t v_optionFlags_3050_; uint8_t v_suppressElabErrors_3051_; uint8_t v_isRecordingDeps_3052_; lean_object* v_ref_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v_toCold_3047_ = lean_ctor_get(v___y_3044_, 0);
v_currRecDepth_3048_ = lean_ctor_get(v___y_3044_, 1);
v_ref_3049_ = lean_ctor_get(v___y_3044_, 2);
v_optionFlags_3050_ = lean_ctor_get_uint16(v___y_3044_, sizeof(void*)*3);
v_suppressElabErrors_3051_ = lean_ctor_get_uint8(v___y_3044_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3052_ = lean_ctor_get_uint8(v___y_3044_, sizeof(void*)*3 + 3);
v_ref_3053_ = l_Lean_replaceRef(v_ref_3038_, v_ref_3049_);
lean_inc(v_currRecDepth_3048_);
lean_inc_ref(v_toCold_3047_);
v___x_3054_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3054_, 0, v_toCold_3047_);
lean_ctor_set(v___x_3054_, 1, v_currRecDepth_3048_);
lean_ctor_set(v___x_3054_, 2, v_ref_3053_);
lean_ctor_set_uint16(v___x_3054_, sizeof(void*)*3, v_optionFlags_3050_);
lean_ctor_set_uint8(v___x_3054_, sizeof(void*)*3 + 2, v_suppressElabErrors_3051_);
lean_ctor_set_uint8(v___x_3054_, sizeof(void*)*3 + 3, v_isRecordingDeps_3052_);
v___x_3055_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___x_3054_, v___y_3045_);
lean_dec_ref_known(v___x_3054_, 3);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_3056_, lean_object* v_msg_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_3056_, v_msg_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v_ref_3056_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_3066_, lean_object* v_id_3067_, uint8_t v_minIndexable_3068_, lean_object* v_as_x27_3069_, lean_object* v_b_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
if (lean_obj_tag(v_as_x27_3069_) == 0)
{
lean_object* v___x_3076_; 
lean_dec(v_id_3067_);
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_b_3070_);
return v___x_3076_;
}
else
{
lean_object* v_head_3077_; lean_object* v_tail_3078_; lean_object* v_toCold_3079_; lean_object* v_currRecDepth_3080_; lean_object* v_ref_3081_; uint16_t v_optionFlags_3082_; uint8_t v_suppressElabErrors_3083_; uint8_t v_isRecordingDeps_3084_; uint8_t v___x_3085_; uint8_t v___x_3086_; lean_object* v___x_3087_; lean_object* v_ref_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v_head_3077_ = lean_ctor_get(v_as_x27_3069_, 0);
v_tail_3078_ = lean_ctor_get(v_as_x27_3069_, 1);
v_toCold_3079_ = lean_ctor_get(v___y_3073_, 0);
v_currRecDepth_3080_ = lean_ctor_get(v___y_3073_, 1);
v_ref_3081_ = lean_ctor_get(v___y_3073_, 2);
v_optionFlags_3082_ = lean_ctor_get_uint16(v___y_3073_, sizeof(void*)*3);
v_suppressElabErrors_3083_ = lean_ctor_get_uint8(v___y_3073_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3084_ = lean_ctor_get_uint8(v___y_3073_, sizeof(void*)*3 + 3);
v___x_3085_ = 0;
v___x_3086_ = 1;
v___x_3087_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_ref_3088_ = l_Lean_replaceRef(v_p_3066_, v_ref_3081_);
lean_inc(v_currRecDepth_3080_);
lean_inc_ref(v_toCold_3079_);
v___x_3089_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3089_, 0, v_toCold_3079_);
lean_ctor_set(v___x_3089_, 1, v_currRecDepth_3080_);
lean_ctor_set(v___x_3089_, 2, v_ref_3088_);
lean_ctor_set_uint16(v___x_3089_, sizeof(void*)*3, v_optionFlags_3082_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*3 + 2, v_suppressElabErrors_3083_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*3 + 3, v_isRecordingDeps_3084_);
lean_inc(v_head_3077_);
lean_inc(v_id_3067_);
v___x_3090_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_3070_, v_id_3067_, v_head_3077_, v___x_3087_, v_minIndexable_3068_, v___x_3085_, v___x_3086_, v___y_3071_, v___y_3072_, v___x_3089_, v___y_3074_);
lean_dec_ref_known(v___x_3089_, 3);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v___x_3090_, 1);
v_as_x27_3069_ = v_tail_3078_;
v_b_3070_ = v_a_3091_;
goto _start;
}
else
{
lean_dec(v_id_3067_);
return v___x_3090_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_3093_, lean_object* v_id_3094_, lean_object* v_minIndexable_3095_, lean_object* v_as_x27_3096_, lean_object* v_b_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
uint8_t v_minIndexable_boxed_3103_; lean_object* v_res_3104_; 
v_minIndexable_boxed_3103_ = lean_unbox(v_minIndexable_3095_);
v_res_3104_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3093_, v_id_3094_, v_minIndexable_boxed_3103_, v_as_x27_3096_, v_b_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v_as_x27_3096_);
lean_dec(v_p_3093_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_3105_){
_start:
{
if (lean_obj_tag(v_x_3105_) == 0)
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_box(0);
return v___x_3106_;
}
else
{
lean_object* v_head_3107_; lean_object* v_tail_3108_; lean_object* v_fst_3109_; uint8_t v___x_3110_; 
v_head_3107_ = lean_ctor_get(v_x_3105_, 0);
v_tail_3108_ = lean_ctor_get(v_x_3105_, 1);
v_fst_3109_ = lean_ctor_get(v_head_3107_, 0);
v___x_3110_ = l_Lean_isPrivateName(v_fst_3109_);
if (v___x_3110_ == 0)
{
v_x_3105_ = v_tail_3108_;
goto _start;
}
else
{
lean_object* v___x_3112_; 
lean_inc(v_head_3107_);
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v_head_3107_);
return v___x_3112_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_3113_);
lean_dec(v_x_3113_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_3115_, lean_object* v_msgData_3116_, uint8_t v_severity_3117_, uint8_t v_isSilent_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; uint8_t v___y_3128_; lean_object* v___y_3129_; uint8_t v___y_3130_; lean_object* v___y_3131_; lean_object* v_toCold_3132_; lean_object* v___y_3133_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; uint8_t v___y_3165_; uint8_t v___y_3166_; lean_object* v___y_3167_; uint8_t v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3189_; lean_object* v___y_3190_; uint8_t v___y_3191_; uint8_t v___y_3192_; uint8_t v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; uint8_t v___y_3199_; uint8_t v___y_3200_; uint8_t v___x_3210_; uint8_t v___y_3212_; uint8_t v___x_3218_; 
v___x_3210_ = 2;
v___x_3218_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3117_, v___x_3210_);
if (v___x_3218_ == 0)
{
v___y_3212_ = v___x_3218_;
goto v___jp_3211_;
}
else
{
uint8_t v___x_3219_; 
lean_inc_ref(v_msgData_3116_);
v___x_3219_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3116_);
if (v___x_3219_ == 0)
{
v___y_3212_ = v___x_3219_;
goto v___jp_3211_;
}
else
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_dec_ref(v_msgData_3116_);
v___x_3220_ = lean_box(0);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
return v___x_3221_;
}
}
v___jp_3124_:
{
lean_object* v_currNamespace_3134_; lean_object* v_openDecls_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v_env_3140_; lean_object* v_nextMacroScope_3141_; lean_object* v_ngen_3142_; lean_object* v_auxDeclNGen_3143_; lean_object* v_traceState_3144_; lean_object* v_cache_3145_; lean_object* v_recordedDeps_3146_; lean_object* v_messages_3147_; lean_object* v_infoState_3148_; lean_object* v_snapshotTasks_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3160_; 
v_currNamespace_3134_ = lean_ctor_get(v_toCold_3132_, 4);
v_openDecls_3135_ = lean_ctor_get(v_toCold_3132_, 5);
lean_inc(v_openDecls_3135_);
lean_inc(v_currNamespace_3134_);
v___x_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3136_, 0, v_currNamespace_3134_);
lean_ctor_set(v___x_3136_, 1, v_openDecls_3135_);
v___x_3137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
lean_ctor_set(v___x_3137_, 1, v___y_3127_);
lean_inc_ref(v___y_3125_);
lean_inc_ref(v___y_3126_);
v___x_3138_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3138_, 0, v___y_3126_);
lean_ctor_set(v___x_3138_, 1, v___y_3129_);
lean_ctor_set(v___x_3138_, 2, v___y_3131_);
lean_ctor_set(v___x_3138_, 3, v___y_3125_);
lean_ctor_set(v___x_3138_, 4, v___x_3137_);
lean_ctor_set_uint8(v___x_3138_, sizeof(void*)*5, v___y_3128_);
lean_ctor_set_uint8(v___x_3138_, sizeof(void*)*5 + 1, v___y_3130_);
lean_ctor_set_uint8(v___x_3138_, sizeof(void*)*5 + 2, v_isSilent_3118_);
v___x_3139_ = lean_st_ref_take(v___y_3133_);
v_env_3140_ = lean_ctor_get(v___x_3139_, 0);
v_nextMacroScope_3141_ = lean_ctor_get(v___x_3139_, 1);
v_ngen_3142_ = lean_ctor_get(v___x_3139_, 2);
v_auxDeclNGen_3143_ = lean_ctor_get(v___x_3139_, 3);
v_traceState_3144_ = lean_ctor_get(v___x_3139_, 4);
v_cache_3145_ = lean_ctor_get(v___x_3139_, 5);
v_recordedDeps_3146_ = lean_ctor_get(v___x_3139_, 6);
v_messages_3147_ = lean_ctor_get(v___x_3139_, 7);
v_infoState_3148_ = lean_ctor_get(v___x_3139_, 8);
v_snapshotTasks_3149_ = lean_ctor_get(v___x_3139_, 9);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3151_ = v___x_3139_;
v_isShared_3152_ = v_isSharedCheck_3160_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_snapshotTasks_3149_);
lean_inc(v_infoState_3148_);
lean_inc(v_messages_3147_);
lean_inc(v_recordedDeps_3146_);
lean_inc(v_cache_3145_);
lean_inc(v_traceState_3144_);
lean_inc(v_auxDeclNGen_3143_);
lean_inc(v_ngen_3142_);
lean_inc(v_nextMacroScope_3141_);
lean_inc(v_env_3140_);
lean_dec(v___x_3139_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3160_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3156_; 
v___x_3153_ = lean_box(0);
v___x_3154_ = l_Lean_MessageLog_add(v___x_3138_, v_messages_3147_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 7, v___x_3154_);
v___x_3156_ = v___x_3151_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_env_3140_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_nextMacroScope_3141_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_ngen_3142_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_auxDeclNGen_3143_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_traceState_3144_);
lean_ctor_set(v_reuseFailAlloc_3159_, 5, v_cache_3145_);
lean_ctor_set(v_reuseFailAlloc_3159_, 6, v_recordedDeps_3146_);
lean_ctor_set(v_reuseFailAlloc_3159_, 7, v___x_3154_);
lean_ctor_set(v_reuseFailAlloc_3159_, 8, v_infoState_3148_);
lean_ctor_set(v_reuseFailAlloc_3159_, 9, v_snapshotTasks_3149_);
v___x_3156_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_st_ref_put(v___y_3133_, v___x_3156_);
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3153_);
return v___x_3158_;
}
}
}
v___jp_3161_:
{
lean_object* v_fileName_3170_; lean_object* v_fileMap_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3187_; 
v_fileName_3170_ = lean_ctor_get(v___y_3164_, 0);
v_fileMap_3171_ = lean_ctor_get(v___y_3164_, 1);
v___x_3172_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3116_);
v___x_3173_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_3172_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3187_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3187_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
lean_inc_ref_n(v_fileMap_3171_, 2);
v___x_3178_ = l_Lean_FileMap_toPosition(v_fileMap_3171_, v___y_3167_);
lean_dec(v___y_3167_);
v___x_3179_ = l_Lean_FileMap_toPosition(v_fileMap_3171_, v___y_3169_);
lean_dec(v___y_3169_);
v___x_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_3168_ == 0)
{
lean_del_object(v___x_3176_);
lean_dec_ref(v___y_3163_);
v___y_3125_ = v___x_3181_;
v___y_3126_ = v_fileName_3170_;
v___y_3127_ = v_a_3174_;
v___y_3128_ = v___y_3165_;
v___y_3129_ = v___x_3178_;
v___y_3130_ = v___y_3166_;
v___y_3131_ = v___x_3180_;
v_toCold_3132_ = v___y_3162_;
v___y_3133_ = v___y_3122_;
goto v___jp_3124_;
}
else
{
uint8_t v___x_3182_; 
lean_inc(v_a_3174_);
v___x_3182_ = l_Lean_MessageData_hasTag(v___y_3163_, v_a_3174_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; lean_object* v___x_3185_; 
lean_dec_ref_known(v___x_3180_, 1);
lean_dec_ref(v___x_3178_);
lean_dec(v_a_3174_);
v___x_3183_ = lean_box(0);
if (v_isShared_3177_ == 0)
{
lean_ctor_set(v___x_3176_, 0, v___x_3183_);
v___x_3185_ = v___x_3176_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
else
{
lean_del_object(v___x_3176_);
v___y_3125_ = v___x_3181_;
v___y_3126_ = v_fileName_3170_;
v___y_3127_ = v_a_3174_;
v___y_3128_ = v___y_3165_;
v___y_3129_ = v___x_3178_;
v___y_3130_ = v___y_3166_;
v___y_3131_ = v___x_3180_;
v_toCold_3132_ = v___y_3162_;
v___y_3133_ = v___y_3122_;
goto v___jp_3124_;
}
}
}
}
v___jp_3188_:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lean_Syntax_getTailPos_x3f(v___y_3194_, v___y_3192_);
lean_dec(v___y_3194_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_inc(v___y_3195_);
v___y_3162_ = v___y_3189_;
v___y_3163_ = v___y_3190_;
v___y_3164_ = v___y_3189_;
v___y_3165_ = v___y_3192_;
v___y_3166_ = v___y_3193_;
v___y_3167_ = v___y_3195_;
v___y_3168_ = v___y_3191_;
v___y_3169_ = v___y_3195_;
goto v___jp_3161_;
}
else
{
lean_object* v_val_3197_; 
v_val_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_val_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v___y_3162_ = v___y_3189_;
v___y_3163_ = v___y_3190_;
v___y_3164_ = v___y_3189_;
v___y_3165_ = v___y_3192_;
v___y_3166_ = v___y_3193_;
v___y_3167_ = v___y_3195_;
v___y_3168_ = v___y_3191_;
v___y_3169_ = v_val_3197_;
goto v___jp_3161_;
}
}
v___jp_3198_:
{
lean_object* v_toCold_3201_; lean_object* v_ref_3202_; uint8_t v_suppressElabErrors_3203_; lean_object* v___x_3204_; lean_object* v___f_3205_; lean_object* v_ref_3206_; lean_object* v___x_3207_; 
v_toCold_3201_ = lean_ctor_get(v___y_3121_, 0);
v_ref_3202_ = lean_ctor_get(v___y_3121_, 2);
v_suppressElabErrors_3203_ = lean_ctor_get_uint8(v___y_3121_, sizeof(void*)*3 + 2);
v___x_3204_ = lean_box(v_suppressElabErrors_3203_);
v___f_3205_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3205_, 0, v___x_3204_);
v_ref_3206_ = l_Lean_replaceRef(v_ref_3115_, v_ref_3202_);
v___x_3207_ = l_Lean_Syntax_getPos_x3f(v_ref_3206_, v___y_3199_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v___x_3208_; 
v___x_3208_ = lean_unsigned_to_nat(0u);
v___y_3189_ = v_toCold_3201_;
v___y_3190_ = v___f_3205_;
v___y_3191_ = v_suppressElabErrors_3203_;
v___y_3192_ = v___y_3199_;
v___y_3193_ = v___y_3200_;
v___y_3194_ = v_ref_3206_;
v___y_3195_ = v___x_3208_;
goto v___jp_3188_;
}
else
{
lean_object* v_val_3209_; 
v_val_3209_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_val_3209_);
lean_dec_ref_known(v___x_3207_, 1);
v___y_3189_ = v_toCold_3201_;
v___y_3190_ = v___f_3205_;
v___y_3191_ = v_suppressElabErrors_3203_;
v___y_3192_ = v___y_3199_;
v___y_3193_ = v___y_3200_;
v___y_3194_ = v_ref_3206_;
v___y_3195_ = v_val_3209_;
goto v___jp_3188_;
}
}
v___jp_3211_:
{
uint8_t v___x_3213_; uint8_t v___x_3214_; 
v___x_3213_ = 1;
v___x_3214_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3117_, v___x_3213_);
if (v___x_3214_ == 0)
{
v___y_3199_ = v___y_3212_;
v___y_3200_ = v_severity_3117_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; 
v___x_3215_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3121_);
v___x_3216_ = l_Lean_warningAsError;
v___x_3217_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3215_, v___x_3216_);
lean_dec_ref(v___x_3215_);
if (v___x_3217_ == 0)
{
v___y_3199_ = v___y_3212_;
v___y_3200_ = v_severity_3117_;
goto v___jp_3198_;
}
else
{
v___y_3199_ = v___y_3212_;
v___y_3200_ = v___x_3210_;
goto v___jp_3198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_3222_, lean_object* v_msgData_3223_, lean_object* v_severity_3224_, lean_object* v_isSilent_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
uint8_t v_severity_boxed_3231_; uint8_t v_isSilent_boxed_3232_; lean_object* v_res_3233_; 
v_severity_boxed_3231_ = lean_unbox(v_severity_3224_);
v_isSilent_boxed_3232_ = lean_unbox(v_isSilent_3225_);
v_res_3233_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3222_, v_msgData_3223_, v_severity_boxed_3231_, v_isSilent_boxed_3232_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v_ref_3222_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_3234_, uint8_t v_severity_3235_, uint8_t v_isSilent_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v_ref_3244_; lean_object* v___x_3245_; 
v_ref_3244_ = lean_ctor_get(v___y_3241_, 2);
v___x_3245_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3244_, v_msgData_3234_, v_severity_3235_, v_isSilent_3236_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_3246_, lean_object* v_severity_3247_, lean_object* v_isSilent_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
uint8_t v_severity_boxed_3256_; uint8_t v_isSilent_boxed_3257_; lean_object* v_res_3258_; 
v_severity_boxed_3256_ = lean_unbox(v_severity_3247_);
v_isSilent_boxed_3257_ = lean_unbox(v_isSilent_3248_);
v_res_3258_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3246_, v_severity_boxed_3256_, v_isSilent_boxed_3257_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
uint8_t v___x_3267_; uint8_t v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = 1;
v___x_3268_ = 0;
v___x_3269_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3259_, v___x_3267_, v___x_3268_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___x_3282_; uint8_t v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3282_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3280_);
v___x_3283_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3282_, v_opt_3279_);
lean_dec_ref(v___x_3282_);
v___x_3284_ = lean_box(v___x_3283_);
v___x_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3286_, v___y_3287_);
lean_dec_ref(v___y_3287_);
lean_dec_ref(v_opt_3286_);
return v_res_3289_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3292_ = l_Lean_stringToMessageData(v___x_3291_);
return v___x_3292_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3295_ = l_Lean_stringToMessageData(v___x_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v___x_3304_; lean_object* v_env_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3327_; 
v___x_3304_ = lean_st_ref_get(v___y_3302_);
v_env_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc_ref(v_env_3305_);
lean_dec(v___x_3304_);
v___x_3306_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3307_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3306_, v___y_3301_);
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3327_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3327_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
uint8_t v_isExporting_3317_; 
v_isExporting_3317_ = lean_ctor_get_uint8(v_env_3305_, sizeof(void*)*13);
lean_dec_ref(v_env_3305_);
if (v_isExporting_3317_ == 0)
{
lean_dec(v_a_3308_);
lean_dec(v_id_3296_);
goto v___jp_3312_;
}
else
{
uint8_t v___x_3318_; 
v___x_3318_ = l_Lean_isPrivateName(v_id_3296_);
if (v___x_3318_ == 0)
{
lean_dec(v_a_3308_);
lean_dec(v_id_3296_);
goto v___jp_3312_;
}
else
{
uint8_t v___x_3319_; 
v___x_3319_ = lean_unbox(v_a_3308_);
lean_dec(v_a_3308_);
if (v___x_3319_ == 0)
{
lean_dec(v_id_3296_);
goto v___jp_3312_;
}
else
{
lean_object* v___x_3320_; uint8_t v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_del_object(v___x_3310_);
v___x_3320_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3321_ = 0;
v___x_3322_ = l_Lean_MessageData_ofConstName(v_id_3296_, v___x_3321_);
v___x_3323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3320_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
v___x_3324_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3325_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
return v___x_3326_;
}
}
}
v___jp_3312_:
{
lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3313_ = lean_box(0);
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 0, v___x_3313_);
v___x_3315_ = v___x_3310_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3337_, uint8_t v_enableLog_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v___x_3346_; lean_object* v_toCold_3347_; lean_object* v_env_3348_; lean_object* v_currNamespace_3349_; lean_object* v_openDecls_3350_; lean_object* v___x_3351_; lean_object* v_res_3352_; lean_object* v___x_3353_; 
v___x_3346_ = lean_st_ref_get(v___y_3344_);
v_toCold_3347_ = lean_ctor_get(v___y_3343_, 0);
v_env_3348_ = lean_ctor_get(v___x_3346_, 0);
lean_inc_ref(v_env_3348_);
lean_dec(v___x_3346_);
v_currNamespace_3349_ = lean_ctor_get(v_toCold_3347_, 4);
v_openDecls_3350_ = lean_ctor_get(v_toCold_3347_, 5);
v___x_3351_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3343_);
lean_inc(v_openDecls_3350_);
lean_inc(v_currNamespace_3349_);
v_res_3352_ = l_Lean_ResolveName_resolveGlobalName(v_env_3348_, v___x_3351_, v_currNamespace_3349_, v_openDecls_3350_, v_id_3337_);
lean_dec_ref(v___x_3351_);
v___x_3353_ = lean_st_ref_get(v___y_3344_);
if (v_enableLog_3338_ == 0)
{
lean_object* v___x_3354_; 
lean_dec(v___x_3353_);
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_res_3352_);
return v___x_3354_;
}
else
{
lean_object* v_env_3355_; uint8_t v_isExporting_3356_; 
v_env_3355_ = lean_ctor_get(v___x_3353_, 0);
lean_inc_ref(v_env_3355_);
lean_dec(v___x_3353_);
v_isExporting_3356_ = lean_ctor_get_uint8(v_env_3355_, sizeof(void*)*13);
lean_dec_ref(v_env_3355_);
if (v_isExporting_3356_ == 0)
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3357_, 0, v_res_3352_);
return v___x_3357_;
}
else
{
lean_object* v___x_3358_; 
v___x_3358_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3352_);
if (lean_obj_tag(v___x_3358_) == 1)
{
lean_object* v_val_3359_; lean_object* v_fst_3360_; lean_object* v___x_3361_; 
v_val_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_val_3359_);
lean_dec_ref_known(v___x_3358_, 1);
v_fst_3360_ = lean_ctor_get(v_val_3359_, 0);
lean_inc(v_fst_3360_);
lean_dec(v_val_3359_);
v___x_3361_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3360_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; 
v_unused_3369_ = lean_ctor_get(v___x_3361_, 0);
lean_dec(v_unused_3369_);
v___x_3363_ = v___x_3361_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_dec(v___x_3361_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v_res_3352_);
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_res_3352_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_dec(v_res_3352_);
v_a_3370_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3361_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3361_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
else
{
lean_object* v___x_3378_; 
lean_dec(v___x_3358_);
v___x_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3378_, 0, v_res_3352_);
return v___x_3378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3379_, lean_object* v_enableLog_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
uint8_t v_enableLog_boxed_3388_; lean_object* v_res_3389_; 
v_enableLog_boxed_3388_ = lean_unbox(v_enableLog_3380_);
v_res_3389_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3379_, v_enableLog_boxed_3388_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
if (lean_obj_tag(v_a_3390_) == 0)
{
lean_object* v___x_3392_; 
v___x_3392_ = l_List_reverse___redArg(v_a_3391_);
return v___x_3392_;
}
else
{
lean_object* v_head_3393_; lean_object* v_tail_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3405_; 
v_head_3393_ = lean_ctor_get(v_a_3390_, 0);
v_tail_3394_ = lean_ctor_get(v_a_3390_, 1);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_a_3390_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3396_ = v_a_3390_;
v_isShared_3397_ = v_isSharedCheck_3405_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_tail_3394_);
lean_inc(v_head_3393_);
lean_dec(v_a_3390_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3405_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v_snd_3398_; uint8_t v___x_3399_; 
v_snd_3398_ = lean_ctor_get(v_head_3393_, 1);
v___x_3399_ = l_List_isEmpty___redArg(v_snd_3398_);
if (v___x_3399_ == 0)
{
lean_del_object(v___x_3396_);
lean_dec(v_head_3393_);
v_a_3390_ = v_tail_3394_;
goto _start;
}
else
{
lean_object* v___x_3402_; 
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v_a_3391_);
v___x_3402_ = v___x_3396_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_head_3393_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_a_3391_);
v___x_3402_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
v_a_3390_ = v_tail_3394_;
v_a_3391_ = v___x_3402_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3406_, lean_object* v_findLocalDecl_x3f_3407_, lean_object* v_n_3408_, lean_object* v_projs_3409_, uint8_t v_globalDeclFound_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v___y_3419_; lean_object* v___y_3420_; uint8_t v_globalDeclFoundNext_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v_imported_3430_; lean_object* v_ctx_3431_; lean_object* v_scopes_3432_; lean_object* v_givenNameView_3433_; uint8_t v___y_3435_; 
v_imported_3430_ = lean_ctor_get(v_view_3406_, 1);
v_ctx_3431_ = lean_ctor_get(v_view_3406_, 2);
v_scopes_3432_ = lean_ctor_get(v_view_3406_, 3);
lean_inc(v_scopes_3432_);
lean_inc(v_ctx_3431_);
lean_inc(v_imported_3430_);
lean_inc(v_n_3408_);
v_givenNameView_3433_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3433_, 0, v_n_3408_);
lean_ctor_set(v_givenNameView_3433_, 1, v_imported_3430_);
lean_ctor_set(v_givenNameView_3433_, 2, v_ctx_3431_);
lean_ctor_set(v_givenNameView_3433_, 3, v_scopes_3432_);
if (v_globalDeclFound_3410_ == 0)
{
v___y_3435_ = v_globalDeclFound_3410_;
goto v___jp_3434_;
}
else
{
uint8_t v___x_3470_; 
v___x_3470_ = l_List_isEmpty___redArg(v_projs_3409_);
if (v___x_3470_ == 0)
{
v___y_3435_ = v_globalDeclFound_3410_;
goto v___jp_3434_;
}
else
{
uint8_t v___x_3471_; 
v___x_3471_ = 0;
v___y_3435_ = v___x_3471_;
goto v___jp_3434_;
}
}
v___jp_3418_:
{
lean_object* v___x_3428_; 
v___x_3428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___y_3419_);
lean_ctor_set(v___x_3428_, 1, v_projs_3409_);
v_n_3408_ = v___y_3420_;
v_projs_3409_ = v___x_3428_;
v_globalDeclFound_3410_ = v_globalDeclFoundNext_3421_;
v___y_3411_ = v___y_3422_;
v___y_3412_ = v___y_3423_;
v___y_3413_ = v___y_3424_;
v___y_3414_ = v___y_3425_;
v___y_3415_ = v___y_3426_;
v___y_3416_ = v___y_3427_;
goto _start;
}
v___jp_3434_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = lean_box(v___y_3435_);
lean_inc_ref(v_findLocalDecl_x3f_3407_);
lean_inc_ref(v_givenNameView_3433_);
v___x_3437_ = lean_apply_2(v_findLocalDecl_x3f_3407_, v_givenNameView_3433_, v___x_3436_);
if (lean_obj_tag(v___x_3437_) == 0)
{
if (lean_obj_tag(v_n_3408_) == 1)
{
if (v_globalDeclFound_3410_ == 0)
{
lean_object* v_pre_3438_; lean_object* v_str_3439_; uint8_t v_globalDeclFoundNext_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v_pre_3438_ = lean_ctor_get(v_n_3408_, 0);
lean_inc(v_pre_3438_);
v_str_3439_ = lean_ctor_get(v_n_3408_, 1);
lean_inc_ref(v_str_3439_);
lean_dec_ref_known(v_n_3408_, 2);
v_globalDeclFoundNext_3440_ = 1;
v___x_3441_ = l_Lean_MacroScopesView_review(v_givenNameView_3433_);
v___x_3442_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3441_, v_globalDeclFound_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3444_; lean_object* v_r_3445_; uint8_t v___x_3446_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v___x_3442_, 1);
v___x_3444_ = lean_box(0);
v_r_3445_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3443_, v___x_3444_);
v___x_3446_ = l_List_isEmpty___redArg(v_r_3445_);
lean_dec(v_r_3445_);
if (v___x_3446_ == 0)
{
v___y_3419_ = v_str_3439_;
v___y_3420_ = v_pre_3438_;
v_globalDeclFoundNext_3421_ = v_globalDeclFoundNext_3440_;
v___y_3422_ = v___y_3411_;
v___y_3423_ = v___y_3412_;
v___y_3424_ = v___y_3413_;
v___y_3425_ = v___y_3414_;
v___y_3426_ = v___y_3415_;
v___y_3427_ = v___y_3416_;
goto v___jp_3418_;
}
else
{
v___y_3419_ = v_str_3439_;
v___y_3420_ = v_pre_3438_;
v_globalDeclFoundNext_3421_ = v_globalDeclFound_3410_;
v___y_3422_ = v___y_3411_;
v___y_3423_ = v___y_3412_;
v___y_3424_ = v___y_3413_;
v___y_3425_ = v___y_3414_;
v___y_3426_ = v___y_3415_;
v___y_3427_ = v___y_3416_;
goto v___jp_3418_;
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec_ref(v_str_3439_);
lean_dec(v_pre_3438_);
lean_dec(v_projs_3409_);
lean_dec_ref(v_findLocalDecl_x3f_3407_);
v_a_3447_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3442_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3442_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
else
{
lean_object* v_pre_3455_; lean_object* v_str_3456_; 
lean_dec_ref_known(v_givenNameView_3433_, 4);
v_pre_3455_ = lean_ctor_get(v_n_3408_, 0);
lean_inc(v_pre_3455_);
v_str_3456_ = lean_ctor_get(v_n_3408_, 1);
lean_inc_ref(v_str_3456_);
lean_dec_ref_known(v_n_3408_, 2);
v___y_3419_ = v_str_3456_;
v___y_3420_ = v_pre_3455_;
v_globalDeclFoundNext_3421_ = v_globalDeclFound_3410_;
v___y_3422_ = v___y_3411_;
v___y_3423_ = v___y_3412_;
v___y_3424_ = v___y_3413_;
v___y_3425_ = v___y_3414_;
v___y_3426_ = v___y_3415_;
v___y_3427_ = v___y_3416_;
goto v___jp_3418_;
}
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
lean_dec_ref_known(v_givenNameView_3433_, 4);
lean_dec(v_projs_3409_);
lean_dec(v_n_3408_);
lean_dec_ref(v_findLocalDecl_x3f_3407_);
v___x_3457_ = lean_box(0);
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
return v___x_3458_;
}
}
else
{
lean_object* v_val_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref_known(v_givenNameView_3433_, 4);
lean_dec(v_n_3408_);
lean_dec_ref(v_findLocalDecl_x3f_3407_);
v_val_3459_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3461_ = v___x_3437_;
v_isShared_3462_ = v_isSharedCheck_3469_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_val_3459_);
lean_dec(v___x_3437_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3469_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3463_ = l_Lean_LocalDecl_toExpr(v_val_3459_);
v___x_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v_projs_3409_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3464_);
v___x_3466_ = v___x_3461_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
return v___x_3467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3472_, lean_object* v_findLocalDecl_x3f_3473_, lean_object* v_n_3474_, lean_object* v_projs_3475_, lean_object* v_globalDeclFound_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
uint8_t v_globalDeclFound_boxed_3484_; lean_object* v_res_3485_; 
v_globalDeclFound_boxed_3484_ = lean_unbox(v_globalDeclFound_3476_);
v_res_3485_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3472_, v_findLocalDecl_x3f_3473_, v_n_3474_, v_projs_3475_, v_globalDeclFound_boxed_3484_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec_ref(v_view_3472_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3486_, lean_object* v_givenName_3487_, lean_object* v_as_3488_, lean_object* v_i_3489_){
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
lean_object* v_one_3493_; lean_object* v_n_3494_; lean_object* v___x_3495_; 
v_one_3493_ = lean_unsigned_to_nat(1u);
v_n_3494_ = lean_nat_sub(v_i_3489_, v_one_3493_);
lean_dec(v_i_3489_);
v___x_3495_ = lean_array_fget_borrowed(v_as_3488_, v_n_3494_);
if (lean_obj_tag(v___x_3495_) == 0)
{
v_i_3489_ = v_n_3494_;
goto _start;
}
else
{
lean_object* v_val_3497_; uint8_t v___x_3498_; 
v_val_3497_ = lean_ctor_get(v___x_3495_, 0);
v___x_3498_ = l_Lean_LocalDecl_isAuxDecl(v_val_3497_);
if (v___x_3498_ == 0)
{
if (lean_obj_tag(v_localDecl_x3f_3486_) == 0)
{
v_i_3489_ = v_n_3494_;
goto _start;
}
else
{
lean_dec(v_n_3494_);
lean_inc_ref(v_localDecl_x3f_3486_);
return v_localDecl_x3f_3486_;
}
}
else
{
lean_object* v___x_3500_; uint8_t v___x_3501_; 
v___x_3500_ = l_Lean_LocalDecl_userName(v_val_3497_);
v___x_3501_ = lean_name_eq(v___x_3500_, v_givenName_3487_);
lean_dec(v___x_3500_);
if (v___x_3501_ == 0)
{
v_i_3489_ = v_n_3494_;
goto _start;
}
else
{
lean_dec(v_n_3494_);
lean_inc_ref(v___x_3495_);
return v___x_3495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3503_, lean_object* v_givenName_3504_, lean_object* v_as_3505_, lean_object* v_i_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3503_, v_givenName_3504_, v_as_3505_, v_i_3506_);
lean_dec_ref(v_as_3505_);
lean_dec(v_givenName_3504_);
lean_dec(v_localDecl_x3f_3503_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3508_, lean_object* v_givenName_3509_, lean_object* v_as_3510_, lean_object* v_i_3511_){
_start:
{
lean_object* v_zero_3512_; uint8_t v_isZero_3513_; 
v_zero_3512_ = lean_unsigned_to_nat(0u);
v_isZero_3513_ = lean_nat_dec_eq(v_i_3511_, v_zero_3512_);
if (v_isZero_3513_ == 1)
{
lean_object* v___x_3514_; 
lean_dec(v_i_3511_);
v___x_3514_ = lean_box(0);
return v___x_3514_;
}
else
{
lean_object* v_one_3515_; lean_object* v_n_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v_one_3515_ = lean_unsigned_to_nat(1u);
v_n_3516_ = lean_nat_sub(v_i_3511_, v_one_3515_);
lean_dec(v_i_3511_);
v___x_3517_ = lean_array_fget_borrowed(v_as_3510_, v_n_3516_);
v___x_3518_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3508_, v_givenName_3509_, v___x_3517_);
if (lean_obj_tag(v___x_3518_) == 0)
{
v_i_3511_ = v_n_3516_;
goto _start;
}
else
{
lean_dec(v_n_3516_);
return v___x_3518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3520_, lean_object* v_givenName_3521_, lean_object* v_x_3522_){
_start:
{
if (lean_obj_tag(v_x_3522_) == 0)
{
lean_object* v_cs_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v_cs_3523_ = lean_ctor_get(v_x_3522_, 0);
v___x_3524_ = lean_array_get_size(v_cs_3523_);
v___x_3525_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3520_, v_givenName_3521_, v_cs_3523_, v___x_3524_);
return v___x_3525_;
}
else
{
lean_object* v_vs_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v_vs_3526_ = lean_ctor_get(v_x_3522_, 0);
v___x_3527_ = lean_array_get_size(v_vs_3526_);
v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3520_, v_givenName_3521_, v_vs_3526_, v___x_3527_);
return v___x_3528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3529_, lean_object* v_givenName_3530_, lean_object* v_x_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3529_, v_givenName_3530_, v_x_3531_);
lean_dec_ref(v_x_3531_);
lean_dec(v_givenName_3530_);
lean_dec(v_localDecl_x3f_3529_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3533_, lean_object* v_givenName_3534_, lean_object* v_as_3535_, lean_object* v_i_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3533_, v_givenName_3534_, v_as_3535_, v_i_3536_);
lean_dec_ref(v_as_3535_);
lean_dec(v_givenName_3534_);
lean_dec(v_localDecl_x3f_3533_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3538_, lean_object* v_givenName_3539_, lean_object* v_t_3540_){
_start:
{
lean_object* v_root_3541_; lean_object* v_tail_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v_root_3541_ = lean_ctor_get(v_t_3540_, 0);
v_tail_3542_ = lean_ctor_get(v_t_3540_, 1);
v___x_3543_ = lean_array_get_size(v_tail_3542_);
v___x_3544_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3538_, v_givenName_3539_, v_tail_3542_, v___x_3543_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3538_, v_givenName_3539_, v_root_3541_);
return v___x_3545_;
}
else
{
return v___x_3544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3546_, lean_object* v_givenName_3547_, lean_object* v_t_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3546_, v_givenName_3547_, v_t_3548_);
lean_dec_ref(v_t_3548_);
lean_dec(v_givenName_3547_);
lean_dec(v_localDecl_x3f_3546_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3550_, lean_object* v_k_3551_){
_start:
{
if (lean_obj_tag(v_t_3550_) == 0)
{
lean_object* v_k_3552_; lean_object* v_v_3553_; lean_object* v_l_3554_; lean_object* v_r_3555_; uint8_t v___x_3556_; 
v_k_3552_ = lean_ctor_get(v_t_3550_, 1);
v_v_3553_ = lean_ctor_get(v_t_3550_, 2);
v_l_3554_ = lean_ctor_get(v_t_3550_, 3);
v_r_3555_ = lean_ctor_get(v_t_3550_, 4);
v___x_3556_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3551_, v_k_3552_);
switch(v___x_3556_)
{
case 0:
{
v_t_3550_ = v_l_3554_;
goto _start;
}
case 1:
{
lean_object* v___x_3558_; 
lean_inc(v_v_3553_);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v_v_3553_);
return v___x_3558_;
}
default: 
{
v_t_3550_ = v_r_3555_;
goto _start;
}
}
}
else
{
lean_object* v___x_3560_; 
v___x_3560_ = lean_box(0);
return v___x_3560_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3561_, lean_object* v_k_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3561_, v_k_3562_);
lean_dec(v_k_3562_);
lean_dec(v_t_3561_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3564_, lean_object* v_givenName_3565_){
_start:
{
lean_object* v___x_3566_; uint8_t v___x_3567_; 
v___x_3566_ = l_Lean_LocalDecl_userName(v_localDecl_3564_);
v___x_3567_ = lean_name_eq(v___x_3566_, v_givenName_3565_);
lean_dec(v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; 
lean_dec_ref(v_localDecl_3564_);
v___x_3568_ = lean_box(0);
return v___x_3568_;
}
else
{
lean_object* v___x_3569_; 
v___x_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3569_, 0, v_localDecl_3564_);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3570_, lean_object* v_givenName_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3570_, v_givenName_3571_);
lean_dec(v_givenName_3571_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3573_, uint8_t v_skipAuxDecl_3574_, lean_object* v_auxDeclToFullName_3575_, lean_object* v___x_3576_, lean_object* v_givenNameView_3577_, lean_object* v_as_3578_, lean_object* v_i_3579_){
_start:
{
lean_object* v_zero_3580_; uint8_t v_isZero_3581_; 
v_zero_3580_ = lean_unsigned_to_nat(0u);
v_isZero_3581_ = lean_nat_dec_eq(v_i_3579_, v_zero_3580_);
if (v_isZero_3581_ == 1)
{
lean_object* v___x_3582_; 
lean_dec(v_i_3579_);
lean_dec_ref(v_givenNameView_3577_);
lean_dec(v___x_3576_);
v___x_3582_ = lean_box(0);
return v___x_3582_;
}
else
{
lean_object* v_one_3583_; lean_object* v_n_3584_; lean_object* v___y_3586_; lean_object* v___x_3588_; 
v_one_3583_ = lean_unsigned_to_nat(1u);
v_n_3584_ = lean_nat_sub(v_i_3579_, v_one_3583_);
lean_dec(v_i_3579_);
v___x_3588_ = lean_array_fget_borrowed(v_as_3578_, v_n_3584_);
if (lean_obj_tag(v___x_3588_) == 0)
{
v_i_3579_ = v_n_3584_;
goto _start;
}
else
{
lean_object* v_val_3590_; uint8_t v___x_3591_; 
v_val_3590_ = lean_ctor_get(v___x_3588_, 0);
v___x_3591_ = l_Lean_LocalDecl_isAuxDecl(v_val_3590_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; 
lean_inc(v_val_3590_);
v___x_3592_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3590_, v_givenName_3573_);
v___y_3586_ = v___x_3592_;
goto v___jp_3585_;
}
else
{
if (v_skipAuxDecl_3574_ == 0)
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = l_Lean_LocalDecl_fvarId(v_val_3590_);
v___x_3594_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3575_, v___x_3593_);
lean_dec(v___x_3593_);
if (lean_obj_tag(v___x_3594_) == 1)
{
lean_object* v_val_3595_; lean_object* v_fullDeclView_3596_; lean_object* v_name_3597_; lean_object* v_imported_3598_; lean_object* v_ctx_3599_; lean_object* v_scopes_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3620_; 
v_val_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_val_3595_);
lean_dec_ref_known(v___x_3594_, 1);
v_fullDeclView_3596_ = l_Lean_extractMacroScopes(v_val_3595_);
v_name_3597_ = lean_ctor_get(v_fullDeclView_3596_, 0);
v_imported_3598_ = lean_ctor_get(v_fullDeclView_3596_, 1);
v_ctx_3599_ = lean_ctor_get(v_fullDeclView_3596_, 2);
v_scopes_3600_ = lean_ctor_get(v_fullDeclView_3596_, 3);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_fullDeclView_3596_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3602_ = v_fullDeclView_3596_;
v_isShared_3603_ = v_isSharedCheck_3620_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_scopes_3600_);
lean_inc(v_ctx_3599_);
lean_inc(v_imported_3598_);
lean_inc(v_name_3597_);
lean_dec(v_fullDeclView_3596_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3620_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___y_3605_; lean_object* v___x_3618_; 
lean_inc(v_name_3597_);
v___x_3618_ = l_Lean_privateToUserName_x3f(v_name_3597_);
if (lean_obj_tag(v___x_3618_) == 0)
{
v___y_3605_ = v_name_3597_;
goto v___jp_3604_;
}
else
{
lean_object* v_val_3619_; 
lean_dec(v_name_3597_);
v_val_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_val_3619_);
lean_dec_ref_known(v___x_3618_, 1);
v___y_3605_ = v_val_3619_;
goto v___jp_3604_;
}
v___jp_3604_:
{
lean_object* v_fullDeclView_3607_; 
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 0, v___y_3605_);
v_fullDeclView_3607_ = v___x_3602_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___y_3605_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_imported_3598_);
lean_ctor_set(v_reuseFailAlloc_3617_, 2, v_ctx_3599_);
lean_ctor_set(v_reuseFailAlloc_3617_, 3, v_scopes_3600_);
v_fullDeclView_3607_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v_fullDeclName_3608_; uint8_t v___x_3609_; 
lean_inc_ref(v_fullDeclView_3607_);
v_fullDeclName_3608_ = l_Lean_MacroScopesView_review(v_fullDeclView_3607_);
v___x_3609_ = l_Lean_Name_isPrefixOf(v___x_3576_, v_fullDeclName_3608_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; 
lean_dec_ref(v_fullDeclView_3607_);
lean_inc(v___x_3576_);
lean_inc_ref(v_givenNameView_3577_);
lean_inc(v_val_3590_);
v___x_3610_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3590_, v_givenNameView_3577_, v_fullDeclName_3608_, v___x_3576_);
lean_dec(v_fullDeclName_3608_);
v___y_3586_ = v___x_3610_;
goto v___jp_3585_;
}
else
{
lean_object* v___x_3611_; lean_object* v_localDeclNameView_3612_; uint8_t v___x_3613_; 
lean_dec(v_fullDeclName_3608_);
v___x_3611_ = l_Lean_LocalDecl_userName(v_val_3590_);
v_localDeclNameView_3612_ = l_Lean_extractMacroScopes(v___x_3611_);
v___x_3613_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3612_, v_givenNameView_3577_);
lean_dec_ref(v_localDeclNameView_3612_);
if (v___x_3613_ == 0)
{
lean_dec_ref(v_fullDeclView_3607_);
v_i_3579_ = v_n_3584_;
goto _start;
}
else
{
uint8_t v___x_3615_; 
v___x_3615_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3577_, v_fullDeclView_3607_);
lean_dec_ref(v_fullDeclView_3607_);
if (v___x_3615_ == 0)
{
v_i_3579_ = v_n_3584_;
goto _start;
}
else
{
lean_dec(v_n_3584_);
lean_dec_ref(v_givenNameView_3577_);
lean_dec(v___x_3576_);
lean_inc_ref(v___x_3588_);
return v___x_3588_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3621_; 
lean_dec(v___x_3594_);
lean_inc(v_val_3590_);
v___x_3621_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3590_, v_givenName_3573_);
v___y_3586_ = v___x_3621_;
goto v___jp_3585_;
}
}
else
{
v_i_3579_ = v_n_3584_;
goto _start;
}
}
}
v___jp_3585_:
{
if (lean_obj_tag(v___y_3586_) == 0)
{
v_i_3579_ = v_n_3584_;
goto _start;
}
else
{
lean_dec(v_n_3584_);
lean_dec_ref(v_givenNameView_3577_);
lean_dec(v___x_3576_);
return v___y_3586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3623_, lean_object* v_skipAuxDecl_3624_, lean_object* v_auxDeclToFullName_3625_, lean_object* v___x_3626_, lean_object* v_givenNameView_3627_, lean_object* v_as_3628_, lean_object* v_i_3629_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3630_; lean_object* v_res_3631_; 
v_skipAuxDecl_boxed_3630_ = lean_unbox(v_skipAuxDecl_3624_);
v_res_3631_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3623_, v_skipAuxDecl_boxed_3630_, v_auxDeclToFullName_3625_, v___x_3626_, v_givenNameView_3627_, v_as_3628_, v_i_3629_);
lean_dec_ref(v_as_3628_);
lean_dec(v_auxDeclToFullName_3625_);
lean_dec(v_givenName_3623_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3632_, uint8_t v_skipAuxDecl_3633_, lean_object* v_auxDeclToFullName_3634_, lean_object* v___x_3635_, lean_object* v_givenNameView_3636_, lean_object* v_as_3637_, lean_object* v_i_3638_){
_start:
{
lean_object* v_zero_3639_; uint8_t v_isZero_3640_; 
v_zero_3639_ = lean_unsigned_to_nat(0u);
v_isZero_3640_ = lean_nat_dec_eq(v_i_3638_, v_zero_3639_);
if (v_isZero_3640_ == 1)
{
lean_object* v___x_3641_; 
lean_dec(v_i_3638_);
lean_dec_ref(v_givenNameView_3636_);
lean_dec(v___x_3635_);
v___x_3641_ = lean_box(0);
return v___x_3641_;
}
else
{
lean_object* v_one_3642_; lean_object* v_n_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v_one_3642_ = lean_unsigned_to_nat(1u);
v_n_3643_ = lean_nat_sub(v_i_3638_, v_one_3642_);
lean_dec(v_i_3638_);
v___x_3644_ = lean_array_fget_borrowed(v_as_3637_, v_n_3643_);
lean_inc_ref(v_givenNameView_3636_);
lean_inc(v___x_3635_);
v___x_3645_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3632_, v_skipAuxDecl_3633_, v_auxDeclToFullName_3634_, v___x_3635_, v_givenNameView_3636_, v___x_3644_);
if (lean_obj_tag(v___x_3645_) == 0)
{
v_i_3638_ = v_n_3643_;
goto _start;
}
else
{
lean_dec(v_n_3643_);
lean_dec_ref(v_givenNameView_3636_);
lean_dec(v___x_3635_);
return v___x_3645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3647_, uint8_t v_skipAuxDecl_3648_, lean_object* v_auxDeclToFullName_3649_, lean_object* v___x_3650_, lean_object* v_givenNameView_3651_, lean_object* v_x_3652_){
_start:
{
if (lean_obj_tag(v_x_3652_) == 0)
{
lean_object* v_cs_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v_cs_3653_ = lean_ctor_get(v_x_3652_, 0);
v___x_3654_ = lean_array_get_size(v_cs_3653_);
v___x_3655_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3647_, v_skipAuxDecl_3648_, v_auxDeclToFullName_3649_, v___x_3650_, v_givenNameView_3651_, v_cs_3653_, v___x_3654_);
return v___x_3655_;
}
else
{
lean_object* v_vs_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v_vs_3656_ = lean_ctor_get(v_x_3652_, 0);
v___x_3657_ = lean_array_get_size(v_vs_3656_);
v___x_3658_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3647_, v_skipAuxDecl_3648_, v_auxDeclToFullName_3649_, v___x_3650_, v_givenNameView_3651_, v_vs_3656_, v___x_3657_);
return v___x_3658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3659_, lean_object* v_skipAuxDecl_3660_, lean_object* v_auxDeclToFullName_3661_, lean_object* v___x_3662_, lean_object* v_givenNameView_3663_, lean_object* v_x_3664_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3665_; lean_object* v_res_3666_; 
v_skipAuxDecl_boxed_3665_ = lean_unbox(v_skipAuxDecl_3660_);
v_res_3666_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3659_, v_skipAuxDecl_boxed_3665_, v_auxDeclToFullName_3661_, v___x_3662_, v_givenNameView_3663_, v_x_3664_);
lean_dec_ref(v_x_3664_);
lean_dec(v_auxDeclToFullName_3661_);
lean_dec(v_givenName_3659_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3667_, lean_object* v_skipAuxDecl_3668_, lean_object* v_auxDeclToFullName_3669_, lean_object* v___x_3670_, lean_object* v_givenNameView_3671_, lean_object* v_as_3672_, lean_object* v_i_3673_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3674_; lean_object* v_res_3675_; 
v_skipAuxDecl_boxed_3674_ = lean_unbox(v_skipAuxDecl_3668_);
v_res_3675_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3667_, v_skipAuxDecl_boxed_3674_, v_auxDeclToFullName_3669_, v___x_3670_, v_givenNameView_3671_, v_as_3672_, v_i_3673_);
lean_dec_ref(v_as_3672_);
lean_dec(v_auxDeclToFullName_3669_);
lean_dec(v_givenName_3667_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3676_, uint8_t v_skipAuxDecl_3677_, lean_object* v_auxDeclToFullName_3678_, lean_object* v___x_3679_, lean_object* v_givenNameView_3680_, lean_object* v_t_3681_){
_start:
{
lean_object* v_root_3682_; lean_object* v_tail_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v_root_3682_ = lean_ctor_get(v_t_3681_, 0);
v_tail_3683_ = lean_ctor_get(v_t_3681_, 1);
v___x_3684_ = lean_array_get_size(v_tail_3683_);
lean_inc_ref(v_givenNameView_3680_);
lean_inc(v___x_3679_);
v___x_3685_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3676_, v_skipAuxDecl_3677_, v_auxDeclToFullName_3678_, v___x_3679_, v_givenNameView_3680_, v_tail_3683_, v___x_3684_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3676_, v_skipAuxDecl_3677_, v_auxDeclToFullName_3678_, v___x_3679_, v_givenNameView_3680_, v_root_3682_);
return v___x_3686_;
}
else
{
lean_dec_ref(v_givenNameView_3680_);
lean_dec(v___x_3679_);
return v___x_3685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3687_, lean_object* v_skipAuxDecl_3688_, lean_object* v_auxDeclToFullName_3689_, lean_object* v___x_3690_, lean_object* v_givenNameView_3691_, lean_object* v_t_3692_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3693_; lean_object* v_res_3694_; 
v_skipAuxDecl_boxed_3693_ = lean_unbox(v_skipAuxDecl_3688_);
v_res_3694_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3687_, v_skipAuxDecl_boxed_3693_, v_auxDeclToFullName_3689_, v___x_3690_, v_givenNameView_3691_, v_t_3692_);
lean_dec_ref(v_t_3692_);
lean_dec(v_auxDeclToFullName_3689_);
lean_dec(v_givenName_3687_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3695_, lean_object* v_currNamespace_3696_, lean_object* v_decls_3697_, lean_object* v_givenNameView_3698_, uint8_t v_skipAuxDecl_3699_){
_start:
{
lean_object* v_givenName_3700_; lean_object* v_localDecl_x3f_3701_; 
lean_inc_ref(v_givenNameView_3698_);
v_givenName_3700_ = l_Lean_MacroScopesView_review(v_givenNameView_3698_);
v_localDecl_x3f_3701_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3700_, v_skipAuxDecl_3699_, v_auxDeclToFullName_3695_, v_currNamespace_3696_, v_givenNameView_3698_, v_decls_3697_);
if (lean_obj_tag(v_localDecl_x3f_3701_) == 0)
{
if (v_skipAuxDecl_3699_ == 0)
{
lean_object* v___x_3702_; 
v___x_3702_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3701_, v_givenName_3700_, v_decls_3697_);
lean_dec(v_givenName_3700_);
return v___x_3702_;
}
else
{
lean_dec(v_givenName_3700_);
return v_localDecl_x3f_3701_;
}
}
else
{
lean_dec(v_givenName_3700_);
return v_localDecl_x3f_3701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3703_, lean_object* v_currNamespace_3704_, lean_object* v_decls_3705_, lean_object* v_givenNameView_3706_, lean_object* v_skipAuxDecl_3707_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3708_; lean_object* v_res_3709_; 
v_skipAuxDecl_boxed_3708_ = lean_unbox(v_skipAuxDecl_3707_);
v_res_3709_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3703_, v_currNamespace_3704_, v_decls_3705_, v_givenNameView_3706_, v_skipAuxDecl_boxed_3708_);
lean_dec_ref(v_decls_3705_);
lean_dec(v_auxDeclToFullName_3703_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_lctx_3718_; lean_object* v_toCold_3719_; lean_object* v_decls_3720_; lean_object* v_auxDeclToFullName_3721_; lean_object* v_currNamespace_3722_; lean_object* v_view_3723_; lean_object* v_name_3724_; lean_object* v_findLocalDecl_x3f_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; lean_object* v___x_3728_; 
v_lctx_3718_ = lean_ctor_get(v___y_3713_, 2);
v_toCold_3719_ = lean_ctor_get(v___y_3715_, 0);
v_decls_3720_ = lean_ctor_get(v_lctx_3718_, 1);
v_auxDeclToFullName_3721_ = lean_ctor_get(v_lctx_3718_, 2);
v_currNamespace_3722_ = lean_ctor_get(v_toCold_3719_, 4);
v_view_3723_ = l_Lean_extractMacroScopes(v_n_3710_);
v_name_3724_ = lean_ctor_get(v_view_3723_, 0);
lean_inc(v_name_3724_);
lean_inc_ref(v_decls_3720_);
lean_inc(v_currNamespace_3722_);
lean_inc(v_auxDeclToFullName_3721_);
v_findLocalDecl_x3f_3725_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3725_, 0, v_auxDeclToFullName_3721_);
lean_closure_set(v_findLocalDecl_x3f_3725_, 1, v_currNamespace_3722_);
lean_closure_set(v_findLocalDecl_x3f_3725_, 2, v_decls_3720_);
v___x_3726_ = lean_box(0);
v___x_3727_ = 0;
v___x_3728_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3723_, v_findLocalDecl_x3f_3725_, v_name_3724_, v___x_3726_, v___x_3727_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
lean_dec_ref(v_view_3723_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3738_, lean_object* v_b_3739_){
_start:
{
if (lean_obj_tag(v_as_x27_3738_) == 0)
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v_b_3739_);
return v___x_3741_;
}
else
{
lean_object* v_head_3742_; lean_object* v_tail_3743_; lean_object* v_config_3744_; lean_object* v_extensions_3745_; lean_object* v_extra_3746_; lean_object* v_extraInj_3747_; lean_object* v_extraFacts_3748_; lean_object* v_symPrios_3749_; lean_object* v_norm_3750_; lean_object* v_normProcs_3751_; lean_object* v_anchorRefs_x3f_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3761_; 
v_head_3742_ = lean_ctor_get(v_as_x27_3738_, 0);
v_tail_3743_ = lean_ctor_get(v_as_x27_3738_, 1);
v_config_3744_ = lean_ctor_get(v_b_3739_, 0);
v_extensions_3745_ = lean_ctor_get(v_b_3739_, 1);
v_extra_3746_ = lean_ctor_get(v_b_3739_, 2);
v_extraInj_3747_ = lean_ctor_get(v_b_3739_, 3);
v_extraFacts_3748_ = lean_ctor_get(v_b_3739_, 4);
v_symPrios_3749_ = lean_ctor_get(v_b_3739_, 5);
v_norm_3750_ = lean_ctor_get(v_b_3739_, 6);
v_normProcs_3751_ = lean_ctor_get(v_b_3739_, 7);
v_anchorRefs_x3f_3752_ = lean_ctor_get(v_b_3739_, 8);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_b_3739_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3754_ = v_b_3739_;
v_isShared_3755_ = v_isSharedCheck_3761_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_anchorRefs_x3f_3752_);
lean_inc(v_normProcs_3751_);
lean_inc(v_norm_3750_);
lean_inc(v_symPrios_3749_);
lean_inc(v_extraFacts_3748_);
lean_inc(v_extraInj_3747_);
lean_inc(v_extra_3746_);
lean_inc(v_extensions_3745_);
lean_inc(v_config_3744_);
lean_dec(v_b_3739_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3761_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
lean_inc(v_head_3742_);
v___x_3756_ = l_Lean_PersistentArray_push___redArg(v_extra_3746_, v_head_3742_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 2, v___x_3756_);
v___x_3758_ = v___x_3754_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_config_3744_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_extensions_3745_);
lean_ctor_set(v_reuseFailAlloc_3760_, 2, v___x_3756_);
lean_ctor_set(v_reuseFailAlloc_3760_, 3, v_extraInj_3747_);
lean_ctor_set(v_reuseFailAlloc_3760_, 4, v_extraFacts_3748_);
lean_ctor_set(v_reuseFailAlloc_3760_, 5, v_symPrios_3749_);
lean_ctor_set(v_reuseFailAlloc_3760_, 6, v_norm_3750_);
lean_ctor_set(v_reuseFailAlloc_3760_, 7, v_normProcs_3751_);
lean_ctor_set(v_reuseFailAlloc_3760_, 8, v_anchorRefs_x3f_3752_);
v___x_3758_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
v_as_x27_3738_ = v_tail_3743_;
v_b_3739_ = v___x_3758_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3762_, lean_object* v_b_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3762_, v_b_3763_);
lean_dec(v_as_x27_3762_);
return v_res_3765_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3768_ = l_Lean_stringToMessageData(v___x_3767_);
return v___x_3768_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3771_ = l_Lean_stringToMessageData(v___x_3770_);
return v___x_3771_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3774_ = l_Lean_stringToMessageData(v___x_3773_);
return v___x_3774_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3777_ = l_Lean_stringToMessageData(v___x_3776_);
return v___x_3777_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3780_ = l_Lean_stringToMessageData(v___x_3779_);
return v___x_3780_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3783_ = l_Lean_stringToMessageData(v___x_3782_);
return v___x_3783_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3786_ = l_Lean_stringToMessageData(v___x_3785_);
return v___x_3786_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3789_ = l_Lean_stringToMessageData(v___x_3788_);
return v___x_3789_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3792_ = l_Lean_stringToMessageData(v___x_3791_);
return v___x_3792_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3794_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3795_ = l_Lean_stringToMessageData(v___x_3794_);
return v___x_3795_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3798_ = l_Lean_stringToMessageData(v___x_3797_);
return v___x_3798_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23(void){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22));
v___x_3801_ = l_Lean_stringToMessageData(v___x_3800_);
return v___x_3801_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25(void){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24));
v___x_3804_ = l_Lean_stringToMessageData(v___x_3803_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3805_, lean_object* v_p_3806_, lean_object* v_mod_x3f_3807_, lean_object* v_id_3808_, uint8_t v_minIndexable_3809_, uint8_t v_only_3810_, uint8_t v_incremental_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_){
_start:
{
lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; uint8_t v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; uint8_t v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v_a_3995_; lean_object* v___y_4220_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4231_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4232_ = lean_box(0);
lean_inc(v_id_3808_);
v___x_4233_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3808_, v___x_4232_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v___x_4233_, 1);
v_a_3995_ = v_a_4234_;
goto v___jp_3994_;
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4310_; 
v_a_4235_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4310_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4237_ = v___x_4233_;
v_isShared_4238_ = v_isSharedCheck_4310_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4233_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4310_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
uint8_t v___x_4239_; 
v___x_4239_ = l_Lean_Exception_isInterrupt(v_a_4235_);
if (v___x_4239_ == 0)
{
uint8_t v___x_4240_; 
lean_inc(v_a_4235_);
v___x_4240_ = l_Lean_Exception_isRuntime(v_a_4235_);
if (v___x_4240_ == 0)
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
lean_del_object(v___x_4237_);
v___x_4241_ = l_Lean_TSyntax_getId(v_id_3808_);
lean_inc(v___x_4241_);
v___x_4242_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4241_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4243_);
lean_dec_ref_known(v___x_4242_, 1);
if (lean_obj_tag(v_a_4243_) == 0)
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_4241_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4273_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4247_ = v___x_4244_;
v_isShared_4248_ = v_isSharedCheck_4273_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4244_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4273_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
if (lean_obj_tag(v_a_4245_) == 1)
{
lean_del_object(v___x_4247_);
lean_dec(v_a_4235_);
if (lean_obj_tag(v_mod_x3f_3807_) == 1)
{
lean_object* v_val_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec_ref_known(v_a_4245_, 1);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v_val_4249_ = lean_ctor_get(v_mod_x3f_3807_, 0);
lean_inc(v_val_4249_);
lean_dec_ref_known(v_mod_x3f_3807_, 1);
v___x_4250_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4251_ = l_Lean_MessageData_ofName(v___x_4241_);
v___x_4252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4250_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
v___x_4253_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4252_);
lean_ctor_set(v___x_4254_, 1, v___x_4253_);
v___x_4255_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4249_, v___x_4254_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
lean_dec(v_val_4249_);
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4255_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4255_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
else
{
lean_object* v_val_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
lean_dec(v___x_4241_);
v_val_4264_ = lean_ctor_get(v_a_4245_, 0);
lean_inc(v_val_4264_);
lean_dec_ref_known(v_a_4245_, 1);
v___x_4265_ = lean_box(0);
lean_inc_ref(v_params_3805_);
v___x_4266_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3805_, v_val_4264_, v___x_4231_, v___x_4240_, v___x_4265_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
lean_dec(v_val_4264_);
v___y_4220_ = v___x_4266_;
goto v___jp_4219_;
}
}
else
{
lean_object* v___x_4267_; uint8_t v___x_4268_; 
lean_dec(v_a_4245_);
v___x_4267_ = l_Lean_Name_getPrefix(v___x_4241_);
lean_dec(v___x_4241_);
v___x_4268_ = l_Lean_Name_isAnonymous(v___x_4267_);
lean_dec(v___x_4267_);
if (v___x_4268_ == 0)
{
lean_object* v___x_4269_; 
lean_del_object(v___x_4247_);
lean_dec(v_a_4235_);
v___x_4269_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3805_, v_p_3806_, v_mod_x3f_3807_, v_id_3808_, v_minIndexable_3809_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
return v___x_4269_;
}
else
{
lean_object* v___x_4271_; 
lean_dec(v_id_3808_);
lean_dec(v_mod_x3f_3807_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
if (v_isShared_4248_ == 0)
{
lean_ctor_set_tag(v___x_4247_, 1);
lean_ctor_set(v___x_4247_, 0, v_a_4235_);
v___x_4271_ = v___x_4247_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4235_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
}
else
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
lean_dec(v___x_4241_);
lean_dec(v_a_4235_);
lean_dec(v_id_3808_);
lean_dec(v_mod_x3f_3807_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v_a_4274_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4276_ = v___x_4244_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4244_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
else
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_dec_ref_known(v_a_4243_, 1);
lean_dec(v___x_4241_);
lean_dec(v_a_4235_);
lean_dec(v_mod_x3f_3807_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v___x_4282_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23);
lean_inc(v_id_3808_);
v___x_4283_ = l_Lean_MessageData_ofSyntax(v_id_3808_);
v___x_4284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4282_);
lean_ctor_set(v___x_4284_, 1, v___x_4283_);
v___x_4285_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25);
v___x_4286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4284_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3808_, v___x_4286_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
lean_dec(v_id_3808_);
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4287_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
else
{
lean_object* v_a_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4303_; 
lean_dec(v___x_4241_);
lean_dec(v_a_4235_);
lean_dec(v_id_3808_);
lean_dec(v_mod_x3f_3807_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v_a_4296_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4298_ = v___x_4242_;
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_a_4296_);
lean_dec(v___x_4242_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4301_; 
if (v_isShared_4299_ == 0)
{
v___x_4301_ = v___x_4298_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4296_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
return v___x_4301_;
}
}
}
}
else
{
lean_object* v___x_4305_; 
lean_dec(v_id_3808_);
lean_dec(v_mod_x3f_3807_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
if (v_isShared_4238_ == 0)
{
v___x_4305_ = v___x_4237_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4235_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
else
{
lean_object* v___x_4308_; 
lean_dec(v_id_3808_);
lean_dec(v_mod_x3f_3807_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
if (v_isShared_4238_ == 0)
{
v___x_4308_ = v___x_4237_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4235_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
}
v___jp_3819_:
{
lean_object* v_ctors_3827_; lean_object* v___x_3828_; 
v_ctors_3827_ = lean_ctor_get(v___y_3820_, 4);
lean_inc(v_ctors_3827_);
lean_dec_ref(v___y_3820_);
v___x_3828_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3806_, v_id_3808_, v_minIndexable_3809_, v_ctors_3827_, v_params_3805_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v_ctors_3827_);
lean_dec(v_p_3806_);
return v___x_3828_;
}
v___jp_3829_:
{
lean_object* v___x_3836_; 
v___x_3836_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3809_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_toCold_3837_; lean_object* v_currRecDepth_3838_; lean_object* v_ref_3839_; uint16_t v_optionFlags_3840_; uint8_t v_suppressElabErrors_3841_; uint8_t v_isRecordingDeps_3842_; lean_object* v_ref_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
lean_dec_ref_known(v___x_3836_, 1);
v_toCold_3837_ = lean_ctor_get(v___y_3834_, 0);
v_currRecDepth_3838_ = lean_ctor_get(v___y_3834_, 1);
v_ref_3839_ = lean_ctor_get(v___y_3834_, 2);
v_optionFlags_3840_ = lean_ctor_get_uint16(v___y_3834_, sizeof(void*)*3);
v_suppressElabErrors_3841_ = lean_ctor_get_uint8(v___y_3834_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3842_ = lean_ctor_get_uint8(v___y_3834_, sizeof(void*)*3 + 3);
v_ref_3843_ = l_Lean_replaceRef(v_p_3806_, v_ref_3839_);
lean_dec(v_p_3806_);
lean_inc(v_currRecDepth_3838_);
lean_inc_ref(v_toCold_3837_);
v___x_3844_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3844_, 0, v_toCold_3837_);
lean_ctor_set(v___x_3844_, 1, v_currRecDepth_3838_);
lean_ctor_set(v___x_3844_, 2, v_ref_3843_);
lean_ctor_set_uint16(v___x_3844_, sizeof(void*)*3, v_optionFlags_3840_);
lean_ctor_set_uint8(v___x_3844_, sizeof(void*)*3 + 2, v_suppressElabErrors_3841_);
lean_ctor_set_uint8(v___x_3844_, sizeof(void*)*3 + 3, v_isRecordingDeps_3842_);
lean_inc(v___y_3831_);
v___x_3845_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3831_, v___y_3830_, v___x_3844_, v___y_3835_);
lean_dec_ref_known(v___x_3844_, 3);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3853_; 
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3853_ == 0)
{
lean_object* v_unused_3854_; 
v_unused_3854_ = lean_ctor_get(v___x_3845_, 0);
lean_dec(v_unused_3854_);
v___x_3847_ = v___x_3845_;
v_isShared_3848_ = v_isSharedCheck_3853_;
goto v_resetjp_3846_;
}
else
{
lean_dec(v___x_3845_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3853_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3849_; lean_object* v___x_3851_; 
v___x_3849_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3805_, v___y_3831_, v___y_3830_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v___x_3849_);
v___x_3851_ = v___x_3847_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec(v___y_3831_);
lean_dec_ref(v_params_3805_);
v_a_3855_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3845_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3845_);
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
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_dec(v___y_3831_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v_a_3863_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3836_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3836_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
v___jp_3871_:
{
lean_object* v___x_3880_; 
v___x_3880_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3809_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
lean_dec_ref_known(v___x_3880_, 1);
v___x_3881_ = l_Lean_Meta_Grind_grindExt;
v___x_3882_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3881_, v___y_3879_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3882_, 1);
lean_inc(v___y_3873_);
v___x_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___y_3873_);
v___x_3885_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3883_, v___x_3884_);
lean_dec_ref_known(v___x_3884_, 1);
lean_dec(v_a_3883_);
v___x_3886_ = lean_box(0);
v___x_3887_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3872_, v___x_3885_, v___x_3886_);
lean_dec(v___y_3872_);
v___x_3888_ = l_List_isEmpty___redArg(v___x_3887_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; 
lean_dec(v___y_3873_);
lean_dec(v_p_3806_);
v___x_3889_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3887_, v_params_3805_);
lean_dec(v___x_3887_);
return v___x_3889_;
}
else
{
lean_object* v___x_3890_; uint8_t v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec(v___x_3887_);
lean_dec_ref(v_params_3805_);
v___x_3890_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3891_ = 0;
v___x_3892_ = l_Lean_MessageData_ofConstName(v___y_3873_, v___x_3891_);
v___x_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3890_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3893_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
v___x_3896_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3806_, v___x_3895_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
lean_dec(v_p_3806_);
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3896_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3896_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v_a_3905_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3882_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3882_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v_a_3913_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3880_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3880_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
v___jp_3921_:
{
uint8_t v___x_3930_; lean_object* v___x_3931_; 
v___x_3930_ = 0;
lean_inc(v___y_3923_);
v___x_3931_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3923_, v___x_3930_, v___y_3928_, v___y_3929_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
if (lean_obj_tag(v_a_3932_) == 1)
{
lean_object* v_val_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
lean_dec(v___y_3923_);
v_val_3933_ = lean_ctor_get(v_a_3932_, 0);
lean_inc_n(v_val_3933_, 2);
lean_dec_ref_known(v_a_3932_, 1);
v___x_3934_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3805_, v_val_3933_, v___x_3930_);
v___x_3935_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3933_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3946_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3938_ = v___x_3935_;
v_isShared_3939_ = v_isSharedCheck_3946_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3935_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3946_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
if (lean_obj_tag(v_a_3936_) == 1)
{
lean_object* v_val_3940_; lean_object* v_ctors_3941_; lean_object* v___x_3942_; 
lean_del_object(v___x_3938_);
v_val_3940_ = lean_ctor_get(v_a_3936_, 0);
lean_inc(v_val_3940_);
lean_dec_ref_known(v_a_3936_, 1);
v_ctors_3941_ = lean_ctor_get(v_val_3940_, 4);
lean_inc(v_ctors_3941_);
lean_dec(v_val_3940_);
v___x_3942_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3806_, v_id_3808_, v_minIndexable_3809_, v_ctors_3941_, v___x_3934_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec(v_ctors_3941_);
lean_dec(v_p_3806_);
return v___x_3942_;
}
else
{
lean_object* v___x_3944_; 
lean_dec(v_a_3936_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3934_);
v___x_3944_ = v___x_3938_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3934_);
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
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec_ref(v___x_3934_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
v_a_3947_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3935_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3935_);
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
else
{
lean_object* v_symPrios_3955_; lean_object* v___x_3956_; 
lean_dec(v_a_3932_);
v_symPrios_3955_ = lean_ctor_get(v_params_3805_, 5);
lean_inc_ref(v_symPrios_3955_);
lean_inc(v___y_3923_);
v___x_3956_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(v___y_3923_, v_symPrios_3955_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; uint8_t v___x_3958_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_a_3957_);
lean_dec_ref_known(v___x_3956_, 1);
v___x_3958_ = lean_unbox(v_a_3957_);
lean_dec(v_a_3957_);
if (v___x_3958_ == 0)
{
lean_object* v_toCold_3959_; lean_object* v_currRecDepth_3960_; lean_object* v_ref_3961_; uint16_t v_optionFlags_3962_; uint8_t v_suppressElabErrors_3963_; uint8_t v_isRecordingDeps_3964_; lean_object* v___x_3965_; lean_object* v_ref_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v_toCold_3959_ = lean_ctor_get(v___y_3928_, 0);
v_currRecDepth_3960_ = lean_ctor_get(v___y_3928_, 1);
v_ref_3961_ = lean_ctor_get(v___y_3928_, 2);
v_optionFlags_3962_ = lean_ctor_get_uint16(v___y_3928_, sizeof(void*)*3);
v_suppressElabErrors_3963_ = lean_ctor_get_uint8(v___y_3928_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3964_ = lean_ctor_get_uint8(v___y_3928_, sizeof(void*)*3 + 3);
v___x_3965_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_ref_3966_ = l_Lean_replaceRef(v_p_3806_, v_ref_3961_);
lean_dec(v_p_3806_);
lean_inc(v_currRecDepth_3960_);
lean_inc_ref(v_toCold_3959_);
v___x_3967_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3967_, 0, v_toCold_3959_);
lean_ctor_set(v___x_3967_, 1, v_currRecDepth_3960_);
lean_ctor_set(v___x_3967_, 2, v_ref_3966_);
lean_ctor_set_uint16(v___x_3967_, sizeof(void*)*3, v_optionFlags_3962_);
lean_ctor_set_uint8(v___x_3967_, sizeof(void*)*3 + 2, v_suppressElabErrors_3963_);
lean_ctor_set_uint8(v___x_3967_, sizeof(void*)*3 + 3, v_isRecordingDeps_3964_);
v___x_3968_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3805_, v_id_3808_, v___y_3923_, v___x_3965_, v_minIndexable_3809_, v___y_3922_, v___y_3922_, v___y_3926_, v___y_3927_, v___x_3967_, v___y_3929_);
lean_dec_ref_known(v___x_3967_, 3);
return v___x_3968_;
}
else
{
lean_object* v_toCold_3969_; lean_object* v_currRecDepth_3970_; lean_object* v_ref_3971_; uint16_t v_optionFlags_3972_; uint8_t v_suppressElabErrors_3973_; uint8_t v_isRecordingDeps_3974_; lean_object* v_ref_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
lean_dec(v_id_3808_);
v_toCold_3969_ = lean_ctor_get(v___y_3928_, 0);
v_currRecDepth_3970_ = lean_ctor_get(v___y_3928_, 1);
v_ref_3971_ = lean_ctor_get(v___y_3928_, 2);
v_optionFlags_3972_ = lean_ctor_get_uint16(v___y_3928_, sizeof(void*)*3);
v_suppressElabErrors_3973_ = lean_ctor_get_uint8(v___y_3928_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3974_ = lean_ctor_get_uint8(v___y_3928_, sizeof(void*)*3 + 3);
v_ref_3975_ = l_Lean_replaceRef(v_p_3806_, v_ref_3971_);
lean_dec(v_p_3806_);
lean_inc(v_currRecDepth_3970_);
lean_inc_ref(v_toCold_3969_);
v___x_3976_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3976_, 0, v_toCold_3969_);
lean_ctor_set(v___x_3976_, 1, v_currRecDepth_3970_);
lean_ctor_set(v___x_3976_, 2, v_ref_3975_);
lean_ctor_set_uint16(v___x_3976_, sizeof(void*)*3, v_optionFlags_3972_);
lean_ctor_set_uint8(v___x_3976_, sizeof(void*)*3 + 2, v_suppressElabErrors_3973_);
lean_ctor_set_uint8(v___x_3976_, sizeof(void*)*3 + 3, v_isRecordingDeps_3974_);
v___x_3977_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(v_params_3805_, v___y_3923_, v_minIndexable_3809_, v___y_3926_, v___y_3927_, v___x_3976_, v___y_3929_);
lean_dec_ref_known(v___x_3976_, 3);
return v___x_3977_;
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_dec(v___y_3923_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v_a_3978_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3956_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3956_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_dec(v___y_3923_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v_a_3986_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3931_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3931_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
v___jp_3994_:
{
uint8_t v___x_3996_; lean_object* v___x_3997_; 
v___x_3996_ = 1;
lean_inc(v_a_3995_);
v___x_3997_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_3995_, v___x_3996_, v_a_3812_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_dec_ref_known(v___x_3997_, 1);
if (lean_obj_tag(v_mod_x3f_3807_) == 1)
{
lean_object* v_val_3998_; lean_object* v___x_3999_; 
v_val_3998_ = lean_ctor_get(v_mod_x3f_3807_, 0);
lean_inc(v_val_3998_);
lean_dec_ref_known(v_mod_x3f_3807_, 1);
v___x_3999_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_3998_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4202_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4002_ = v___x_3999_;
v_isShared_4003_ = v_isSharedCheck_4202_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3999_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4202_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
switch(lean_obj_tag(v_a_4000_))
{
case 0:
{
lean_object* v_k_4004_; 
lean_del_object(v___x_4002_);
v_k_4004_ = lean_ctor_get(v_a_4000_, 0);
lean_inc(v_k_4004_);
lean_dec_ref_known(v_a_4000_, 1);
if (lean_obj_tag(v_k_4004_) == 9)
{
lean_dec(v_id_3808_);
if (v_only_3810_ == 0)
{
lean_object* v_toCold_4005_; lean_object* v_currRecDepth_4006_; lean_object* v_ref_4007_; uint16_t v_optionFlags_4008_; uint8_t v_suppressElabErrors_4009_; uint8_t v_isRecordingDeps_4010_; lean_object* v_ref_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_toCold_4005_ = lean_ctor_get(v_a_3816_, 0);
v_currRecDepth_4006_ = lean_ctor_get(v_a_3816_, 1);
v_ref_4007_ = lean_ctor_get(v_a_3816_, 2);
v_optionFlags_4008_ = lean_ctor_get_uint16(v_a_3816_, sizeof(void*)*3);
v_suppressElabErrors_4009_ = lean_ctor_get_uint8(v_a_3816_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4010_ = lean_ctor_get_uint8(v_a_3816_, sizeof(void*)*3 + 3);
v_ref_4011_ = l_Lean_replaceRef(v_p_3806_, v_ref_4007_);
lean_inc(v_currRecDepth_4006_);
lean_inc_ref(v_toCold_4005_);
v___x_4012_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4012_, 0, v_toCold_4005_);
lean_ctor_set(v___x_4012_, 1, v_currRecDepth_4006_);
lean_ctor_set(v___x_4012_, 2, v_ref_4011_);
lean_ctor_set_uint16(v___x_4012_, sizeof(void*)*3, v_optionFlags_4008_);
lean_ctor_set_uint8(v___x_4012_, sizeof(void*)*3 + 2, v_suppressElabErrors_4009_);
lean_ctor_set_uint8(v___x_4012_, sizeof(void*)*3 + 3, v_isRecordingDeps_4010_);
v___x_4013_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_4012_, v_a_3817_);
lean_dec_ref_known(v___x_4012_, 3);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_dec_ref_known(v___x_4013_, 1);
v___y_3872_ = v_k_4004_;
v___y_3873_ = v_a_3995_;
v___y_3874_ = v_a_3812_;
v___y_3875_ = v_a_3813_;
v___y_3876_ = v_a_3814_;
v___y_3877_ = v_a_3815_;
v___y_3878_ = v_a_3816_;
v___y_3879_ = v_a_3817_;
goto v___jp_3871_;
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec(v_a_3995_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
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
v___y_3872_ = v_k_4004_;
v___y_3873_ = v_a_3995_;
v___y_3874_ = v_a_3812_;
v___y_3875_ = v_a_3813_;
v___y_3876_ = v_a_3814_;
v___y_3877_ = v_a_3815_;
v___y_3878_ = v_a_3816_;
v___y_3879_ = v_a_3817_;
goto v___jp_3871_;
}
}
else
{
lean_object* v_toCold_4022_; lean_object* v_currRecDepth_4023_; lean_object* v_ref_4024_; uint16_t v_optionFlags_4025_; uint8_t v_suppressElabErrors_4026_; uint8_t v_isRecordingDeps_4027_; uint8_t v___x_4028_; lean_object* v_ref_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_toCold_4022_ = lean_ctor_get(v_a_3816_, 0);
v_currRecDepth_4023_ = lean_ctor_get(v_a_3816_, 1);
v_ref_4024_ = lean_ctor_get(v_a_3816_, 2);
v_optionFlags_4025_ = lean_ctor_get_uint16(v_a_3816_, sizeof(void*)*3);
v_suppressElabErrors_4026_ = lean_ctor_get_uint8(v_a_3816_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4027_ = lean_ctor_get_uint8(v_a_3816_, sizeof(void*)*3 + 3);
v___x_4028_ = 0;
v_ref_4029_ = l_Lean_replaceRef(v_p_3806_, v_ref_4024_);
lean_dec(v_p_3806_);
lean_inc(v_currRecDepth_4023_);
lean_inc_ref(v_toCold_4022_);
v___x_4030_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4030_, 0, v_toCold_4022_);
lean_ctor_set(v___x_4030_, 1, v_currRecDepth_4023_);
lean_ctor_set(v___x_4030_, 2, v_ref_4029_);
lean_ctor_set_uint16(v___x_4030_, sizeof(void*)*3, v_optionFlags_4025_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*3 + 2, v_suppressElabErrors_4026_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*3 + 3, v_isRecordingDeps_4027_);
v___x_4031_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3805_, v_id_3808_, v_a_3995_, v_k_4004_, v_minIndexable_3809_, v___x_4028_, v___x_3996_, v_a_3814_, v_a_3815_, v___x_4030_, v_a_3817_);
lean_dec_ref_known(v___x_4030_, 3);
return v___x_4031_;
}
}
case 1:
{
lean_del_object(v___x_4002_);
lean_dec(v_id_3808_);
if (v_incremental_3811_ == 0)
{
uint8_t v_eager_4032_; 
v_eager_4032_ = lean_ctor_get_uint8(v_a_4000_, 0);
lean_dec_ref_known(v_a_4000_, 0);
v___y_3830_ = v_eager_4032_;
v___y_3831_ = v_a_3995_;
v___y_3832_ = v_a_3814_;
v___y_3833_ = v_a_3815_;
v___y_3834_ = v_a_3816_;
v___y_3835_ = v_a_3817_;
goto v___jp_3829_;
}
else
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
lean_dec_ref_known(v_a_4000_, 0);
lean_dec(v_a_3995_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v___x_4033_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_4034_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4033_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4034_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4034_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
case 2:
{
uint8_t v___x_4043_; lean_object* v___x_4044_; 
lean_del_object(v___x_4002_);
v___x_4043_ = 0;
lean_inc(v_a_3995_);
v___x_4044_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3995_, v___x_4043_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v_a_4045_; 
v_a_4045_ = lean_ctor_get(v___x_4044_, 0);
lean_inc(v_a_4045_);
lean_dec_ref_known(v___x_4044_, 1);
if (lean_obj_tag(v_a_4045_) == 1)
{
lean_dec(v_a_3995_);
if (v_incremental_3811_ == 0)
{
lean_object* v_val_4046_; 
v_val_4046_ = lean_ctor_get(v_a_4045_, 0);
lean_inc(v_val_4046_);
lean_dec_ref_known(v_a_4045_, 1);
v___y_3820_ = v_val_4046_;
v___y_3821_ = v_a_3812_;
v___y_3822_ = v_a_3813_;
v___y_3823_ = v_a_3814_;
v___y_3824_ = v_a_3815_;
v___y_3825_ = v_a_3816_;
v___y_3826_ = v_a_3817_;
goto v___jp_3819_;
}
else
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec_ref_known(v_a_4045_, 1);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v___x_4047_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_4048_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4047_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4048_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4048_);
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
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_dec(v_a_4045_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v___x_4057_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_4058_ = l_Lean_MessageData_ofConstName(v_a_3995_, v___x_4043_);
v___x_4059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4057_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
v___x_4060_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_4061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4059_);
lean_ctor_set(v___x_4061_, 1, v___x_4060_);
v___x_4062_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4061_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4062_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4062_);
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
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec(v_a_3995_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v_a_4071_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4044_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4044_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
case 3:
{
lean_del_object(v___x_4002_);
v___y_3922_ = v___x_3996_;
v___y_3923_ = v_a_3995_;
v___y_3924_ = v_a_3812_;
v___y_3925_ = v_a_3813_;
v___y_3926_ = v_a_3814_;
v___y_3927_ = v_a_3815_;
v___y_3928_ = v_a_3816_;
v___y_3929_ = v_a_3817_;
goto v___jp_3921_;
}
case 4:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_del_object(v___x_4002_);
lean_dec(v_a_3995_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v___x_4079_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_4080_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4079_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4080_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4080_);
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
case 5:
{
lean_object* v_prio_4089_; lean_object* v___x_4090_; 
lean_del_object(v___x_4002_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
v_prio_4089_ = lean_ctor_get(v_a_4000_, 0);
lean_inc(v_prio_4089_);
lean_dec_ref_known(v_a_4000_, 1);
v___x_4090_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3809_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4114_; 
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4114_ == 0)
{
lean_object* v_unused_4115_; 
v_unused_4115_ = lean_ctor_get(v___x_4090_, 0);
lean_dec(v_unused_4115_);
v___x_4092_ = v___x_4090_;
v_isShared_4093_ = v_isSharedCheck_4114_;
goto v_resetjp_4091_;
}
else
{
lean_dec(v___x_4090_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4114_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v_config_4094_; lean_object* v_extensions_4095_; lean_object* v_extra_4096_; lean_object* v_extraInj_4097_; lean_object* v_extraFacts_4098_; lean_object* v_symPrios_4099_; lean_object* v_norm_4100_; lean_object* v_normProcs_4101_; lean_object* v_anchorRefs_x3f_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4113_; 
v_config_4094_ = lean_ctor_get(v_params_3805_, 0);
v_extensions_4095_ = lean_ctor_get(v_params_3805_, 1);
v_extra_4096_ = lean_ctor_get(v_params_3805_, 2);
v_extraInj_4097_ = lean_ctor_get(v_params_3805_, 3);
v_extraFacts_4098_ = lean_ctor_get(v_params_3805_, 4);
v_symPrios_4099_ = lean_ctor_get(v_params_3805_, 5);
v_norm_4100_ = lean_ctor_get(v_params_3805_, 6);
v_normProcs_4101_ = lean_ctor_get(v_params_3805_, 7);
v_anchorRefs_x3f_4102_ = lean_ctor_get(v_params_3805_, 8);
v_isSharedCheck_4113_ = !lean_is_exclusive(v_params_3805_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4104_ = v_params_3805_;
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
lean_dec(v_params_3805_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4113_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4106_; lean_object* v___x_4108_; 
v___x_4106_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_4099_, v_a_3995_, v_prio_4089_);
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 5, v___x_4106_);
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
lean_ctor_set(v_reuseFailAlloc_4112_, 3, v_extraInj_4097_);
lean_ctor_set(v_reuseFailAlloc_4112_, 4, v_extraFacts_4098_);
lean_ctor_set(v_reuseFailAlloc_4112_, 5, v___x_4106_);
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
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
lean_dec(v_prio_4089_);
lean_dec(v_a_3995_);
lean_dec_ref(v_params_3805_);
v_a_4116_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4090_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4090_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
case 6:
{
lean_object* v___x_4124_; 
lean_del_object(v___x_4002_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
v___x_4124_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3995_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4149_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4127_ = v___x_4124_;
v_isShared_4128_ = v_isSharedCheck_4149_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4124_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4149_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v_config_4129_; lean_object* v_extensions_4130_; lean_object* v_extra_4131_; lean_object* v_extraInj_4132_; lean_object* v_extraFacts_4133_; lean_object* v_symPrios_4134_; lean_object* v_norm_4135_; lean_object* v_normProcs_4136_; lean_object* v_anchorRefs_x3f_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4148_; 
v_config_4129_ = lean_ctor_get(v_params_3805_, 0);
v_extensions_4130_ = lean_ctor_get(v_params_3805_, 1);
v_extra_4131_ = lean_ctor_get(v_params_3805_, 2);
v_extraInj_4132_ = lean_ctor_get(v_params_3805_, 3);
v_extraFacts_4133_ = lean_ctor_get(v_params_3805_, 4);
v_symPrios_4134_ = lean_ctor_get(v_params_3805_, 5);
v_norm_4135_ = lean_ctor_get(v_params_3805_, 6);
v_normProcs_4136_ = lean_ctor_get(v_params_3805_, 7);
v_anchorRefs_x3f_4137_ = lean_ctor_get(v_params_3805_, 8);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_params_3805_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4139_ = v_params_3805_;
v_isShared_4140_ = v_isSharedCheck_4148_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_anchorRefs_x3f_4137_);
lean_inc(v_normProcs_4136_);
lean_inc(v_norm_4135_);
lean_inc(v_symPrios_4134_);
lean_inc(v_extraFacts_4133_);
lean_inc(v_extraInj_4132_);
lean_inc(v_extra_4131_);
lean_inc(v_extensions_4130_);
lean_inc(v_config_4129_);
lean_dec(v_params_3805_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4148_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4141_; lean_object* v___x_4143_; 
v___x_4141_ = l_Lean_PersistentArray_push___redArg(v_extraInj_4132_, v_a_4125_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 3, v___x_4141_);
v___x_4143_ = v___x_4139_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_config_4129_);
lean_ctor_set(v_reuseFailAlloc_4147_, 1, v_extensions_4130_);
lean_ctor_set(v_reuseFailAlloc_4147_, 2, v_extra_4131_);
lean_ctor_set(v_reuseFailAlloc_4147_, 3, v___x_4141_);
lean_ctor_set(v_reuseFailAlloc_4147_, 4, v_extraFacts_4133_);
lean_ctor_set(v_reuseFailAlloc_4147_, 5, v_symPrios_4134_);
lean_ctor_set(v_reuseFailAlloc_4147_, 6, v_norm_4135_);
lean_ctor_set(v_reuseFailAlloc_4147_, 7, v_normProcs_4136_);
lean_ctor_set(v_reuseFailAlloc_4147_, 8, v_anchorRefs_x3f_4137_);
v___x_4143_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
lean_object* v___x_4145_; 
if (v_isShared_4128_ == 0)
{
lean_ctor_set(v___x_4127_, 0, v___x_4143_);
v___x_4145_ = v___x_4127_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec_ref(v_params_3805_);
v_a_4150_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4124_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4124_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
case 7:
{
lean_object* v___x_4158_; lean_object* v___x_4160_; 
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
v___x_4158_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3805_, v_a_3995_);
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 0, v___x_4158_);
v___x_4160_ = v___x_4002_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
case 8:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec_ref_known(v_a_4000_, 0);
lean_del_object(v___x_4002_);
lean_dec(v_a_3995_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v___x_4162_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_4163_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4162_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4163_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4163_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
case 9:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
lean_del_object(v___x_4002_);
lean_dec(v_a_3995_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v___x_4172_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_4173_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4172_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___x_4173_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4173_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
case 10:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
lean_dec_ref_known(v_a_4000_, 0);
lean_del_object(v___x_4002_);
lean_dec(v_a_3995_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v___x_4182_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_4183_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4182_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4183_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
default: 
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_del_object(v___x_4002_);
lean_dec(v_a_3995_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v___x_4192_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
v___x_4193_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4192_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4193_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4193_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
lean_dec(v_a_3995_);
lean_dec(v_id_3808_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v_a_4203_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_3999_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_3999_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_3807_);
v___y_3922_ = v___x_3996_;
v___y_3923_ = v_a_3995_;
v___y_3924_ = v_a_3812_;
v___y_3925_ = v_a_3813_;
v___y_3926_ = v_a_3814_;
v___y_3927_ = v_a_3815_;
v___y_3928_ = v_a_3816_;
v___y_3929_ = v_a_3817_;
goto v___jp_3921_;
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
lean_dec(v_a_3995_);
lean_dec(v_id_3808_);
lean_dec(v_mod_x3f_3807_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v_a_4211_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_3997_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_3997_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
v___jp_4219_:
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4230_; 
v_a_4221_ = lean_ctor_get(v___y_4220_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___y_4220_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4223_ = v___y_4220_;
v_isShared_4224_ = v_isSharedCheck_4230_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___y_4220_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4230_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
if (lean_obj_tag(v_a_4221_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4227_; 
lean_dec(v_id_3808_);
lean_dec(v_mod_x3f_3807_);
lean_dec(v_p_3806_);
lean_dec_ref(v_params_3805_);
v_a_4225_ = lean_ctor_get(v_a_4221_, 0);
lean_inc(v_a_4225_);
lean_dec_ref_known(v_a_4221_, 1);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 0, v_a_4225_);
v___x_4227_ = v___x_4223_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4225_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
else
{
lean_object* v_a_4229_; 
lean_del_object(v___x_4223_);
v_a_4229_ = lean_ctor_get(v_a_4221_, 0);
lean_inc(v_a_4229_);
lean_dec_ref_known(v_a_4221_, 1);
v_a_3995_ = v_a_4229_;
goto v___jp_3994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4311_, lean_object* v_p_4312_, lean_object* v_mod_x3f_4313_, lean_object* v_id_4314_, lean_object* v_minIndexable_4315_, lean_object* v_only_4316_, lean_object* v_incremental_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
uint8_t v_minIndexable_boxed_4325_; uint8_t v_only_boxed_4326_; uint8_t v_incremental_boxed_4327_; lean_object* v_res_4328_; 
v_minIndexable_boxed_4325_ = lean_unbox(v_minIndexable_4315_);
v_only_boxed_4326_ = lean_unbox(v_only_4316_);
v_incremental_boxed_4327_ = lean_unbox(v_incremental_4317_);
v_res_4328_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4311_, v_p_4312_, v_mod_x3f_4313_, v_id_4314_, v_minIndexable_boxed_4325_, v_only_boxed_4326_, v_incremental_boxed_4327_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
lean_dec(v_a_4319_);
lean_dec_ref(v_a_4318_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4329_, lean_object* v_id_4330_, uint8_t v_minIndexable_4331_, lean_object* v_as_4332_, lean_object* v_as_x27_4333_, lean_object* v_b_4334_, lean_object* v_a_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v___x_4343_; 
v___x_4343_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4329_, v_id_4330_, v_minIndexable_4331_, v_as_x27_4333_, v_b_4334_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4344_, lean_object* v_id_4345_, lean_object* v_minIndexable_4346_, lean_object* v_as_4347_, lean_object* v_as_x27_4348_, lean_object* v_b_4349_, lean_object* v_a_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
uint8_t v_minIndexable_boxed_4358_; lean_object* v_res_4359_; 
v_minIndexable_boxed_4358_ = lean_unbox(v_minIndexable_4346_);
v_res_4359_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4344_, v_id_4345_, v_minIndexable_boxed_4358_, v_as_4347_, v_as_x27_4348_, v_b_4349_, v_a_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec(v_as_x27_4348_);
lean_dec(v_as_4347_);
lean_dec(v_p_4344_);
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4360_, lean_object* v_as_x27_4361_, lean_object* v_b_4362_, lean_object* v_a_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4361_, v_b_4362_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4372_, lean_object* v_as_x27_4373_, lean_object* v_b_4374_, lean_object* v_a_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4372_, v_as_x27_4373_, v_b_4374_, v_a_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v_as_x27_4373_);
lean_dec(v_as_4372_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4384_, lean_object* v_ref_4385_, lean_object* v_msg_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4385_, v_msg_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4395_, lean_object* v_ref_4396_, lean_object* v_msg_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4395_, v_ref_4396_, v_msg_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
lean_dec(v_ref_4396_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4406_, lean_object* v_id_4407_, uint8_t v_minIndexable_4408_, lean_object* v_as_4409_, lean_object* v_as_x27_4410_, lean_object* v_b_4411_, lean_object* v_a_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v___x_4420_; 
v___x_4420_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4406_, v_id_4407_, v_minIndexable_4408_, v_as_x27_4410_, v_b_4411_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4421_, lean_object* v_id_4422_, lean_object* v_minIndexable_4423_, lean_object* v_as_4424_, lean_object* v_as_x27_4425_, lean_object* v_b_4426_, lean_object* v_a_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
uint8_t v_minIndexable_boxed_4435_; lean_object* v_res_4436_; 
v_minIndexable_boxed_4435_ = lean_unbox(v_minIndexable_4423_);
v_res_4436_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4421_, v_id_4422_, v_minIndexable_boxed_4435_, v_as_4424_, v_as_x27_4425_, v_b_4426_, v_a_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v_as_x27_4425_);
lean_dec(v_as_4424_);
lean_dec(v_p_4421_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4437_, lean_object* v_t_4438_, lean_object* v_k_4439_){
_start:
{
lean_object* v___x_4440_; 
v___x_4440_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4438_, v_k_4439_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4441_, lean_object* v_t_4442_, lean_object* v_k_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4441_, v_t_4442_, v_k_4443_);
lean_dec(v_k_4443_);
lean_dec(v_t_4442_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4445_, uint8_t v_skipAuxDecl_4446_, lean_object* v_auxDeclToFullName_4447_, lean_object* v___x_4448_, lean_object* v_givenNameView_4449_, lean_object* v_as_4450_, lean_object* v_i_4451_, lean_object* v_a_4452_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4445_, v_skipAuxDecl_4446_, v_auxDeclToFullName_4447_, v___x_4448_, v_givenNameView_4449_, v_as_4450_, v_i_4451_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4454_, lean_object* v_skipAuxDecl_4455_, lean_object* v_auxDeclToFullName_4456_, lean_object* v___x_4457_, lean_object* v_givenNameView_4458_, lean_object* v_as_4459_, lean_object* v_i_4460_, lean_object* v_a_4461_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4462_; lean_object* v_res_4463_; 
v_skipAuxDecl_boxed_4462_ = lean_unbox(v_skipAuxDecl_4455_);
v_res_4463_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4454_, v_skipAuxDecl_boxed_4462_, v_auxDeclToFullName_4456_, v___x_4457_, v_givenNameView_4458_, v_as_4459_, v_i_4460_, v_a_4461_);
lean_dec_ref(v_as_4459_);
lean_dec(v_auxDeclToFullName_4456_);
lean_dec(v_givenName_4454_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4464_, lean_object* v_givenName_4465_, lean_object* v_as_4466_, lean_object* v_i_4467_, lean_object* v_a_4468_){
_start:
{
lean_object* v___x_4469_; 
v___x_4469_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4464_, v_givenName_4465_, v_as_4466_, v_i_4467_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4470_, lean_object* v_givenName_4471_, lean_object* v_as_4472_, lean_object* v_i_4473_, lean_object* v_a_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4470_, v_givenName_4471_, v_as_4472_, v_i_4473_, v_a_4474_);
lean_dec_ref(v_as_4472_);
lean_dec(v_givenName_4471_);
lean_dec(v_localDecl_x3f_4470_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4476_, uint8_t v_skipAuxDecl_4477_, lean_object* v_auxDeclToFullName_4478_, lean_object* v___x_4479_, lean_object* v_givenNameView_4480_, lean_object* v_as_4481_, lean_object* v_i_4482_, lean_object* v_a_4483_){
_start:
{
lean_object* v___x_4484_; 
v___x_4484_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4476_, v_skipAuxDecl_4477_, v_auxDeclToFullName_4478_, v___x_4479_, v_givenNameView_4480_, v_as_4481_, v_i_4482_);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4485_, lean_object* v_skipAuxDecl_4486_, lean_object* v_auxDeclToFullName_4487_, lean_object* v___x_4488_, lean_object* v_givenNameView_4489_, lean_object* v_as_4490_, lean_object* v_i_4491_, lean_object* v_a_4492_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4493_; lean_object* v_res_4494_; 
v_skipAuxDecl_boxed_4493_ = lean_unbox(v_skipAuxDecl_4486_);
v_res_4494_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4485_, v_skipAuxDecl_boxed_4493_, v_auxDeclToFullName_4487_, v___x_4488_, v_givenNameView_4489_, v_as_4490_, v_i_4491_, v_a_4492_);
lean_dec_ref(v_as_4490_);
lean_dec(v_auxDeclToFullName_4487_);
lean_dec(v_givenName_4485_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4495_, lean_object* v_givenName_4496_, lean_object* v_as_4497_, lean_object* v_i_4498_, lean_object* v_a_4499_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4495_, v_givenName_4496_, v_as_4497_, v_i_4498_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4501_, lean_object* v_givenName_4502_, lean_object* v_as_4503_, lean_object* v_i_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4501_, v_givenName_4502_, v_as_4503_, v_i_4504_, v_a_4505_);
lean_dec_ref(v_as_4503_);
lean_dec(v_givenName_4502_);
lean_dec(v_localDecl_x3f_4501_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v___x_4515_; 
v___x_4515_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4507_, v___y_4512_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec_ref(v_opt_4516_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4525_, lean_object* v_msgData_4526_, uint8_t v_severity_4527_, uint8_t v_isSilent_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
lean_object* v___x_4536_; 
v___x_4536_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4525_, v_msgData_4526_, v_severity_4527_, v_isSilent_4528_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4537_, lean_object* v_msgData_4538_, lean_object* v_severity_4539_, lean_object* v_isSilent_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
uint8_t v_severity_boxed_4548_; uint8_t v_isSilent_boxed_4549_; lean_object* v_res_4550_; 
v_severity_boxed_4548_ = lean_unbox(v_severity_4539_);
v_isSilent_boxed_4549_ = lean_unbox(v_isSilent_4540_);
v_res_4550_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4537_, v_msgData_4538_, v_severity_boxed_4548_, v_isSilent_boxed_4549_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v_ref_4537_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4551_, uint8_t v___x_4552_, lean_object* v_b_4553_, lean_object* v_____r_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4562_ = lean_box(0);
v___x_4563_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4551_, v___x_4562_, v___y_4559_, v___y_4560_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v___x_4565_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc_n(v_a_4564_, 2);
lean_dec_ref_known(v___x_4563_, 1);
v___x_4565_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4564_, v___x_4552_, v___y_4555_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
if (lean_obj_tag(v___x_4565_) == 0)
{
uint8_t v___x_4566_; lean_object* v___x_4567_; 
lean_dec_ref_known(v___x_4565_, 1);
v___x_4566_ = 0;
lean_inc(v_a_4564_);
v___x_4567_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4564_, v___x_4566_, v___y_4559_, v___y_4560_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4627_; 
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4570_ = v___x_4567_;
v_isShared_4571_ = v_isSharedCheck_4627_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4567_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4627_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
if (lean_obj_tag(v_a_4568_) == 1)
{
lean_object* v_val_4572_; lean_object* v___x_4573_; 
lean_del_object(v___x_4570_);
lean_dec(v_a_4564_);
v_val_4572_ = lean_ctor_get(v_a_4568_, 0);
lean_inc_n(v_val_4572_, 2);
lean_dec_ref_known(v_a_4568_, 1);
v___x_4573_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4572_, v___y_4559_, v___y_4560_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_object* v___x_4574_; 
lean_dec_ref_known(v___x_4573_, 1);
v___x_4574_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4553_, v_val_4572_, v___y_4559_, v___y_4560_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4584_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4577_ = v___x_4574_;
v_isShared_4578_ = v_isSharedCheck_4584_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4574_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4584_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4582_; 
v___x_4579_ = lean_box(0);
v___x_4580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
lean_ctor_set(v___x_4580_, 1, v_a_4575_);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v___x_4580_);
v___x_4582_ = v___x_4577_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4580_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
v_a_4585_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4574_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4574_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
lean_dec(v_val_4572_);
lean_dec_ref(v_b_4553_);
v_a_4593_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4573_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4573_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4598_; 
if (v_isShared_4596_ == 0)
{
v___x_4598_ = v___x_4595_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
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
else
{
uint8_t v___x_4601_; 
lean_dec(v_a_4568_);
lean_inc(v_a_4564_);
v___x_4601_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4553_, v_a_4564_);
if (v___x_4601_ == 0)
{
lean_object* v___x_4602_; 
lean_del_object(v___x_4570_);
v___x_4602_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4553_, v_a_4564_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4612_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4605_ = v___x_4602_;
v_isShared_4606_ = v_isSharedCheck_4612_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4602_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4612_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4610_; 
v___x_4607_ = lean_box(0);
v___x_4608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
lean_ctor_set(v___x_4608_, 1, v_a_4603_);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v___x_4608_);
v___x_4610_ = v___x_4605_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v___x_4608_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
else
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4620_; 
v_a_4613_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4615_ = v___x_4602_;
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4602_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
}
}
else
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4625_; 
v___x_4621_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4553_, v_a_4564_);
v___x_4622_ = lean_box(0);
v___x_4623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4622_);
lean_ctor_set(v___x_4623_, 1, v___x_4621_);
if (v_isShared_4571_ == 0)
{
lean_ctor_set(v___x_4570_, 0, v___x_4623_);
v___x_4625_ = v___x_4570_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4623_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
}
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
lean_dec(v_a_4564_);
lean_dec_ref(v_b_4553_);
v_a_4628_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4567_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4567_);
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
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec(v_a_4564_);
lean_dec_ref(v_b_4553_);
v_a_4636_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4565_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4565_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
lean_dec_ref(v_b_4553_);
v_a_4644_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4563_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4563_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4652_, lean_object* v___x_4653_, lean_object* v_b_4654_, lean_object* v_____r_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
uint8_t v___x_17309__boxed_4663_; lean_object* v_res_4664_; 
v___x_17309__boxed_4663_ = lean_unbox(v___x_4653_);
v_res_4664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4652_, v___x_17309__boxed_4663_, v_b_4654_, v_____r_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
lean_dec(v___y_4661_);
lean_dec_ref(v___y_4660_);
lean_dec(v___y_4659_);
lean_dec_ref(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4668_, lean_object* v_b_4669_, lean_object* v_a_4670_, uint8_t v___x_4671_, uint8_t v_only_4672_, uint8_t v_incremental_4673_, lean_object* v_x_4674_, lean_object* v_mod_x3f_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___x_4711_; uint8_t v___x_4712_; 
v___x_4683_ = lean_unsigned_to_nat(1u);
v___x_4684_ = l_Lean_Syntax_getArg(v___x_4668_, v___x_4683_);
v___x_4711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4684_);
v___x_4712_ = l_Lean_Syntax_isOfKind(v___x_4684_, v___x_4711_);
if (v___x_4712_ == 0)
{
lean_object* v___x_4713_; 
v___x_4713_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4669_, v_a_4670_, v_mod_x3f_4675_, v___x_4684_, v___x_4671_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
if (lean_obj_tag(v___x_4713_) == 0)
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4723_; 
v_a_4714_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4716_ = v___x_4713_;
v_isShared_4717_ = v_isSharedCheck_4723_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4713_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4723_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4721_; 
v___x_4718_ = lean_box(0);
v___x_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4718_);
lean_ctor_set(v___x_4719_, 1, v_a_4714_);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v___x_4719_);
v___x_4721_ = v___x_4716_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4719_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
return v___x_4721_;
}
}
}
else
{
lean_object* v_a_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4731_; 
v_a_4724_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4726_ = v___x_4713_;
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_a_4724_);
lean_dec(v___x_4713_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4729_; 
if (v_isShared_4727_ == 0)
{
v___x_4729_ = v___x_4726_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4724_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
}
else
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = l_Lean_TSyntax_getId(v___x_4684_);
v___x_4733_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4732_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v_a_4734_; 
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v___x_4733_, 1);
if (lean_obj_tag(v_a_4734_) == 1)
{
lean_object* v_val_4735_; lean_object* v_snd_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4761_; 
v_val_4735_ = lean_ctor_get(v_a_4734_, 0);
lean_inc(v_val_4735_);
lean_dec_ref_known(v_a_4734_, 1);
v_snd_4736_ = lean_ctor_get(v_val_4735_, 1);
v_isSharedCheck_4761_ = !lean_is_exclusive(v_val_4735_);
if (v_isSharedCheck_4761_ == 0)
{
lean_object* v_unused_4762_; 
v_unused_4762_ = lean_ctor_get(v_val_4735_, 0);
lean_dec(v_unused_4762_);
v___x_4738_ = v_val_4735_;
v_isShared_4739_ = v_isSharedCheck_4761_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_snd_4736_);
lean_dec(v_val_4735_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4761_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
if (lean_obj_tag(v_snd_4736_) == 1)
{
lean_object* v___x_4740_; 
lean_dec_ref_known(v_snd_4736_, 2);
v___x_4740_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4669_, v_a_4670_, v_mod_x3f_4675_, v___x_4684_, v___x_4671_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
if (lean_obj_tag(v___x_4740_) == 0)
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4752_; 
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4743_ = v___x_4740_;
v_isShared_4744_ = v_isSharedCheck_4752_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4740_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4752_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4745_; lean_object* v___x_4747_; 
v___x_4745_ = lean_box(0);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 1, v_a_4741_);
lean_ctor_set(v___x_4738_, 0, v___x_4745_);
v___x_4747_ = v___x_4738_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v___x_4745_);
lean_ctor_set(v_reuseFailAlloc_4751_, 1, v_a_4741_);
v___x_4747_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
lean_object* v___x_4749_; 
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 0, v___x_4747_);
v___x_4749_ = v___x_4743_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4747_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
else
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4760_; 
lean_del_object(v___x_4738_);
v_a_4753_ = lean_ctor_get(v___x_4740_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4755_ = v___x_4740_;
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4740_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
else
{
lean_del_object(v___x_4738_);
lean_dec(v_snd_4736_);
v___y_4686_ = v___y_4676_;
v___y_4687_ = v___y_4677_;
v___y_4688_ = v___y_4678_;
v___y_4689_ = v___y_4679_;
v___y_4690_ = v___y_4680_;
v___y_4691_ = v___y_4681_;
goto v___jp_4685_;
}
}
}
else
{
lean_dec(v_a_4734_);
v___y_4686_ = v___y_4676_;
v___y_4687_ = v___y_4677_;
v___y_4688_ = v___y_4678_;
v___y_4689_ = v___y_4679_;
v___y_4690_ = v___y_4680_;
v___y_4691_ = v___y_4681_;
goto v___jp_4685_;
}
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
lean_dec(v___x_4684_);
lean_dec(v_mod_x3f_4675_);
lean_dec(v_a_4670_);
lean_dec_ref(v_b_4669_);
v_a_4763_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4733_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4733_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
v___jp_4685_:
{
lean_object* v___x_4692_; 
v___x_4692_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4669_, v_a_4670_, v_mod_x3f_4675_, v___x_4684_, v___x_4671_, v_only_4672_, v_incremental_4673_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
if (lean_obj_tag(v___x_4692_) == 0)
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4702_; 
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4695_ = v___x_4692_;
v_isShared_4696_ = v_isSharedCheck_4702_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4692_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4702_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4700_; 
v___x_4697_ = lean_box(0);
v___x_4698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4697_);
lean_ctor_set(v___x_4698_, 1, v_a_4693_);
if (v_isShared_4696_ == 0)
{
lean_ctor_set(v___x_4695_, 0, v___x_4698_);
v___x_4700_ = v___x_4695_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v___x_4698_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
else
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4710_; 
v_a_4703_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4705_ = v___x_4692_;
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4692_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4771_, lean_object* v_b_4772_, lean_object* v_a_4773_, lean_object* v___x_4774_, lean_object* v_only_4775_, lean_object* v_incremental_4776_, lean_object* v_x_4777_, lean_object* v_mod_x3f_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_){
_start:
{
uint8_t v___x_17527__boxed_4786_; uint8_t v_only_boxed_4787_; uint8_t v_incremental_boxed_4788_; lean_object* v_res_4789_; 
v___x_17527__boxed_4786_ = lean_unbox(v___x_4774_);
v_only_boxed_4787_ = lean_unbox(v_only_4775_);
v_incremental_boxed_4788_ = lean_unbox(v_incremental_4776_);
v_res_4789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4771_, v_b_4772_, v_a_4773_, v___x_17527__boxed_4786_, v_only_boxed_4787_, v_incremental_boxed_4788_, v_x_4777_, v_mod_x3f_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___x_4771_);
return v_res_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4790_, lean_object* v___x_4791_, lean_object* v_____r_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
lean_object* v___x_4800_; 
v___x_4800_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4790_, v___x_4791_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4800_) == 0)
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4810_; 
v_a_4801_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4803_ = v___x_4800_;
v_isShared_4804_ = v_isSharedCheck_4810_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4800_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4810_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4808_; 
v___x_4805_ = lean_box(0);
v___x_4806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4805_);
lean_ctor_set(v___x_4806_, 1, v_a_4801_);
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 0, v___x_4806_);
v___x_4808_ = v___x_4803_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4806_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
v_a_4811_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4813_ = v___x_4800_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4800_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_a_4811_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4819_, lean_object* v___x_4820_, lean_object* v_____r_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4819_, v___x_4820_, v_____r_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
lean_dec(v___x_4820_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4830_, lean_object* v_b_4831_, lean_object* v_a_4832_, uint8_t v___x_4833_, uint8_t v_only_4834_, uint8_t v_incremental_4835_, lean_object* v_x_4836_, lean_object* v_mod_x3f_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___y_4848_; lean_object* v___y_4849_; lean_object* v___y_4850_; lean_object* v___y_4851_; lean_object* v___y_4852_; lean_object* v___y_4853_; lean_object* v___x_4873_; uint8_t v___x_4874_; 
v___x_4845_ = lean_unsigned_to_nat(2u);
v___x_4846_ = l_Lean_Syntax_getArg(v___x_4830_, v___x_4845_);
v___x_4873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4846_);
v___x_4874_ = l_Lean_Syntax_isOfKind(v___x_4846_, v___x_4873_);
if (v___x_4874_ == 0)
{
lean_object* v___x_4875_; 
v___x_4875_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4831_, v_a_4832_, v_mod_x3f_4837_, v___x_4846_, v___x_4833_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4885_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4878_ = v___x_4875_;
v_isShared_4879_ = v_isSharedCheck_4885_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4875_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4885_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4883_; 
v___x_4880_ = lean_box(0);
v___x_4881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4880_);
lean_ctor_set(v___x_4881_, 1, v_a_4876_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 0, v___x_4881_);
v___x_4883_ = v___x_4878_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4881_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
else
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4893_; 
v_a_4886_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4888_ = v___x_4875_;
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4875_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4891_; 
if (v_isShared_4889_ == 0)
{
v___x_4891_ = v___x_4888_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_a_4886_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
else
{
lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4894_ = l_Lean_TSyntax_getId(v___x_4846_);
v___x_4895_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4894_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
lean_inc(v_a_4896_);
lean_dec_ref_known(v___x_4895_, 1);
if (lean_obj_tag(v_a_4896_) == 1)
{
lean_object* v_val_4897_; lean_object* v_snd_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4923_; 
v_val_4897_ = lean_ctor_get(v_a_4896_, 0);
lean_inc(v_val_4897_);
lean_dec_ref_known(v_a_4896_, 1);
v_snd_4898_ = lean_ctor_get(v_val_4897_, 1);
v_isSharedCheck_4923_ = !lean_is_exclusive(v_val_4897_);
if (v_isSharedCheck_4923_ == 0)
{
lean_object* v_unused_4924_; 
v_unused_4924_ = lean_ctor_get(v_val_4897_, 0);
lean_dec(v_unused_4924_);
v___x_4900_ = v_val_4897_;
v_isShared_4901_ = v_isSharedCheck_4923_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_snd_4898_);
lean_dec(v_val_4897_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4923_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
if (lean_obj_tag(v_snd_4898_) == 1)
{
lean_object* v___x_4902_; 
lean_dec_ref_known(v_snd_4898_, 2);
v___x_4902_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4831_, v_a_4832_, v_mod_x3f_4837_, v___x_4846_, v___x_4833_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
if (lean_obj_tag(v___x_4902_) == 0)
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4914_; 
v_a_4903_ = lean_ctor_get(v___x_4902_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4905_ = v___x_4902_;
v_isShared_4906_ = v_isSharedCheck_4914_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4902_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4914_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4907_; lean_object* v___x_4909_; 
v___x_4907_ = lean_box(0);
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 1, v_a_4903_);
lean_ctor_set(v___x_4900_, 0, v___x_4907_);
v___x_4909_ = v___x_4900_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4907_);
lean_ctor_set(v_reuseFailAlloc_4913_, 1, v_a_4903_);
v___x_4909_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
lean_object* v___x_4911_; 
if (v_isShared_4906_ == 0)
{
lean_ctor_set(v___x_4905_, 0, v___x_4909_);
v___x_4911_ = v___x_4905_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4909_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
}
}
else
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
lean_del_object(v___x_4900_);
v_a_4915_ = lean_ctor_get(v___x_4902_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4902_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4917_ = v___x_4902_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4902_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
else
{
lean_del_object(v___x_4900_);
lean_dec(v_snd_4898_);
v___y_4848_ = v___y_4838_;
v___y_4849_ = v___y_4839_;
v___y_4850_ = v___y_4840_;
v___y_4851_ = v___y_4841_;
v___y_4852_ = v___y_4842_;
v___y_4853_ = v___y_4843_;
goto v___jp_4847_;
}
}
}
else
{
lean_dec(v_a_4896_);
v___y_4848_ = v___y_4838_;
v___y_4849_ = v___y_4839_;
v___y_4850_ = v___y_4840_;
v___y_4851_ = v___y_4841_;
v___y_4852_ = v___y_4842_;
v___y_4853_ = v___y_4843_;
goto v___jp_4847_;
}
}
else
{
lean_object* v_a_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4932_; 
lean_dec(v___x_4846_);
lean_dec(v_mod_x3f_4837_);
lean_dec(v_a_4832_);
lean_dec_ref(v_b_4831_);
v_a_4925_ = lean_ctor_get(v___x_4895_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4895_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4927_ = v___x_4895_;
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_a_4925_);
lean_dec(v___x_4895_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4930_; 
if (v_isShared_4928_ == 0)
{
v___x_4930_ = v___x_4927_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_a_4925_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
return v___x_4930_;
}
}
}
}
v___jp_4847_:
{
lean_object* v___x_4854_; 
v___x_4854_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4831_, v_a_4832_, v_mod_x3f_4837_, v___x_4846_, v___x_4833_, v_only_4834_, v_incremental_4835_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_);
if (lean_obj_tag(v___x_4854_) == 0)
{
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4864_; 
v_a_4855_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4857_ = v___x_4854_;
v_isShared_4858_ = v_isSharedCheck_4864_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_a_4855_);
lean_dec(v___x_4854_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4864_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4862_; 
v___x_4859_ = lean_box(0);
v___x_4860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4859_);
lean_ctor_set(v___x_4860_, 1, v_a_4855_);
if (v_isShared_4858_ == 0)
{
lean_ctor_set(v___x_4857_, 0, v___x_4860_);
v___x_4862_ = v___x_4857_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v___x_4860_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
else
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4872_; 
v_a_4865_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4867_ = v___x_4854_;
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4854_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4870_; 
if (v_isShared_4868_ == 0)
{
v___x_4870_ = v___x_4867_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4933_, lean_object* v_b_4934_, lean_object* v_a_4935_, lean_object* v___x_4936_, lean_object* v_only_4937_, lean_object* v_incremental_4938_, lean_object* v_x_4939_, lean_object* v_mod_x3f_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
uint8_t v___x_17806__boxed_4948_; uint8_t v_only_boxed_4949_; uint8_t v_incremental_boxed_4950_; lean_object* v_res_4951_; 
v___x_17806__boxed_4948_ = lean_unbox(v___x_4936_);
v_only_boxed_4949_ = lean_unbox(v_only_4937_);
v_incremental_boxed_4950_ = lean_unbox(v_incremental_4938_);
v_res_4951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4933_, v_b_4934_, v_a_4935_, v___x_17806__boxed_4948_, v_only_boxed_4949_, v_incremental_boxed_4950_, v_x_4939_, v_mod_x3f_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___y_4942_);
lean_dec_ref(v___y_4941_);
lean_dec(v___x_4933_);
return v_res_4951_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4959_; lean_object* v___x_4960_; 
v___x_4959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4960_ = l_Lean_stringToMessageData(v___x_4959_);
return v___x_4960_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15(void){
_start:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14));
v___x_4990_ = l_Lean_stringToMessageData(v___x_4989_);
return v___x_4990_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4993_ = l_Lean_stringToMessageData(v___x_4992_);
return v___x_4993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4994_, uint8_t v_only_4995_, uint8_t v_incremental_4996_, lean_object* v_as_4997_, size_t v_sz_4998_, size_t v_i_4999_, lean_object* v_b_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v_snd_5009_; lean_object* v_a_5014_; lean_object* v___y_5021_; uint8_t v___x_5025_; 
v___x_5025_ = lean_usize_dec_lt(v_i_4999_, v_sz_4998_);
if (v___x_5025_ == 0)
{
lean_object* v___x_5026_; 
v___x_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5026_, 0, v_b_5000_);
return v___x_5026_;
}
else
{
lean_object* v_a_5027_; lean_object* v___x_5028_; uint8_t v___x_5029_; 
v_a_5027_ = lean_array_uget_borrowed(v_as_4997_, v_i_4999_);
v___x_5028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_5027_);
v___x_5029_ = l_Lean_Syntax_isOfKind(v_a_5027_, v___x_5028_);
if (v___x_5029_ == 0)
{
lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5030_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5027_);
v___x_5031_ = l_Lean_MessageData_ofSyntax(v_a_5027_);
v___x_5032_ = l_Lean_indentD(v___x_5031_);
v___x_5033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5033_, 0, v___x_5030_);
lean_ctor_set(v___x_5033_, 1, v___x_5032_);
v___x_5034_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5033_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_dec_ref_known(v___x_5034_, 1);
v_snd_5009_ = v_b_5000_;
goto v___jp_5008_;
}
else
{
lean_object* v_a_5035_; 
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_a_5035_);
lean_dec_ref_known(v___x_5034_, 1);
v_a_5014_ = v_a_5035_;
goto v___jp_5013_;
}
}
else
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; 
v___x_5036_ = lean_unsigned_to_nat(0u);
v___x_5037_ = l_Lean_Syntax_getArg(v_a_5027_, v___x_5036_);
v___x_5038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_5037_);
v___x_5039_ = l_Lean_Syntax_isOfKind(v___x_5037_, v___x_5038_);
if (v___x_5039_ == 0)
{
lean_object* v___x_5040_; uint8_t v___x_5041_; 
v___x_5040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_5037_);
v___x_5041_ = l_Lean_Syntax_isOfKind(v___x_5037_, v___x_5040_);
if (v___x_5041_ == 0)
{
lean_object* v___x_5042_; uint8_t v___x_5043_; 
v___x_5042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_5037_);
v___x_5043_ = l_Lean_Syntax_isOfKind(v___x_5037_, v___x_5042_);
if (v___x_5043_ == 0)
{
lean_object* v___x_5044_; uint8_t v___x_5045_; 
v___x_5044_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_5037_);
v___x_5045_ = l_Lean_Syntax_isOfKind(v___x_5037_, v___x_5044_);
if (v___x_5045_ == 0)
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; 
lean_dec(v___x_5037_);
v___x_5046_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5027_);
v___x_5047_ = l_Lean_MessageData_ofSyntax(v_a_5027_);
v___x_5048_ = l_Lean_indentD(v___x_5047_);
v___x_5049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5049_, 0, v___x_5046_);
lean_ctor_set(v___x_5049_, 1, v___x_5048_);
v___x_5050_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5049_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5050_) == 0)
{
lean_dec_ref_known(v___x_5050_, 1);
v_snd_5009_ = v_b_5000_;
goto v___jp_5008_;
}
else
{
lean_object* v_a_5051_; 
v_a_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc(v_a_5051_);
lean_dec_ref_known(v___x_5050_, 1);
v_a_5014_ = v_a_5051_;
goto v___jp_5013_;
}
}
else
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; uint8_t v___x_5055_; 
v___x_5052_ = lean_unsigned_to_nat(1u);
v___x_5053_ = l_Lean_Syntax_getArg(v___x_5037_, v___x_5052_);
lean_dec(v___x_5037_);
v___x_5054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13));
lean_inc(v___x_5053_);
v___x_5055_ = l_Lean_Syntax_isOfKind(v___x_5053_, v___x_5054_);
if (v___x_5055_ == 0)
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
lean_dec(v___x_5053_);
v___x_5056_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5027_);
v___x_5057_ = l_Lean_MessageData_ofSyntax(v_a_5027_);
v___x_5058_ = l_Lean_indentD(v___x_5057_);
v___x_5059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5056_);
lean_ctor_set(v___x_5059_, 1, v___x_5058_);
v___x_5060_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5059_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_dec_ref_known(v___x_5060_, 1);
v_snd_5009_ = v_b_5000_;
goto v___jp_5008_;
}
else
{
lean_object* v_a_5061_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5061_);
lean_dec_ref_known(v___x_5060_, 1);
v_a_5014_ = v_a_5061_;
goto v___jp_5013_;
}
}
else
{
if (v_only_4995_ == 0)
{
lean_object* v___x_5062_; lean_object* v___x_5063_; 
v___x_5062_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15);
v___x_5063_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_5053_, v___x_5062_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5063_) == 0)
{
lean_object* v_a_5064_; lean_object* v___x_5065_; 
v_a_5064_ = lean_ctor_get(v___x_5063_, 0);
lean_inc(v_a_5064_);
lean_dec_ref_known(v___x_5063_, 1);
lean_inc_ref(v_b_5000_);
v___x_5065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_5000_, v___x_5053_, v_a_5064_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___x_5053_);
v___y_5021_ = v___x_5065_;
goto v___jp_5020_;
}
else
{
lean_object* v_a_5066_; 
lean_dec(v___x_5053_);
v_a_5066_ = lean_ctor_get(v___x_5063_, 0);
lean_inc(v_a_5066_);
lean_dec_ref_known(v___x_5063_, 1);
v_a_5014_ = v_a_5066_;
goto v___jp_5013_;
}
}
else
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = lean_box(0);
lean_inc_ref(v_b_5000_);
v___x_5068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_5000_, v___x_5053_, v___x_5067_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___x_5053_);
v___y_5021_ = v___x_5068_;
goto v___jp_5020_;
}
}
}
}
else
{
lean_object* v___x_5069_; lean_object* v___x_5070_; uint8_t v___x_5071_; 
v___x_5069_ = lean_unsigned_to_nat(1u);
v___x_5070_ = l_Lean_Syntax_getArg(v___x_5037_, v___x_5069_);
v___x_5071_ = l_Lean_Syntax_isNone(v___x_5070_);
if (v___x_5071_ == 0)
{
uint8_t v___x_5072_; 
lean_inc(v___x_5070_);
v___x_5072_ = l_Lean_Syntax_matchesNull(v___x_5070_, v___x_5069_);
if (v___x_5072_ == 0)
{
lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
lean_dec(v___x_5070_);
lean_dec(v___x_5037_);
v___x_5073_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5027_);
v___x_5074_ = l_Lean_MessageData_ofSyntax(v_a_5027_);
v___x_5075_ = l_Lean_indentD(v___x_5074_);
v___x_5076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5073_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
v___x_5077_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5076_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_dec_ref_known(v___x_5077_, 1);
v_snd_5009_ = v_b_5000_;
goto v___jp_5008_;
}
else
{
lean_object* v_a_5078_; 
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_a_5078_);
lean_dec_ref_known(v___x_5077_, 1);
v_a_5014_ = v_a_5078_;
goto v___jp_5013_;
}
}
else
{
lean_object* v___x_5079_; lean_object* v___x_5080_; uint8_t v___x_5081_; 
v___x_5079_ = l_Lean_Syntax_getArg(v___x_5070_, v___x_5036_);
lean_dec(v___x_5070_);
v___x_5080_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_5079_);
v___x_5081_ = l_Lean_Syntax_isOfKind(v___x_5079_, v___x_5080_);
if (v___x_5081_ == 0)
{
lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; 
lean_dec(v___x_5079_);
lean_dec(v___x_5037_);
v___x_5082_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5027_);
v___x_5083_ = l_Lean_MessageData_ofSyntax(v_a_5027_);
v___x_5084_ = l_Lean_indentD(v___x_5083_);
v___x_5085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5085_, 0, v___x_5082_);
lean_ctor_set(v___x_5085_, 1, v___x_5084_);
v___x_5086_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5085_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_dec_ref_known(v___x_5086_, 1);
v_snd_5009_ = v_b_5000_;
goto v___jp_5008_;
}
else
{
lean_object* v_a_5087_; 
v_a_5087_ = lean_ctor_get(v___x_5086_, 0);
lean_inc(v_a_5087_);
lean_dec_ref_known(v___x_5086_, 1);
v_a_5014_ = v_a_5087_;
goto v___jp_5013_;
}
}
else
{
lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; 
v___x_5088_ = lean_box(0);
v___x_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5089_, 0, v___x_5079_);
lean_inc(v_a_5027_);
lean_inc_ref(v_b_5000_);
v___x_5090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_5037_, v_b_5000_, v_a_5027_, v___x_5029_, v_only_4995_, v_incremental_4996_, v___x_5088_, v___x_5089_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___x_5037_);
v___y_5021_ = v___x_5090_;
goto v___jp_5020_;
}
}
}
else
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
lean_dec(v___x_5070_);
v___x_5091_ = lean_box(0);
v___x_5092_ = lean_box(0);
lean_inc(v_a_5027_);
lean_inc_ref(v_b_5000_);
v___x_5093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_5037_, v_b_5000_, v_a_5027_, v___x_5029_, v_only_4995_, v_incremental_4996_, v___x_5091_, v___x_5092_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___x_5037_);
v___y_5021_ = v___x_5093_;
goto v___jp_5020_;
}
}
}
else
{
lean_object* v___x_5094_; uint8_t v___x_5095_; 
v___x_5094_ = l_Lean_Syntax_getArg(v___x_5037_, v___x_5036_);
v___x_5095_ = l_Lean_Syntax_isNone(v___x_5094_);
if (v___x_5095_ == 0)
{
lean_object* v___x_5096_; uint8_t v___x_5097_; 
v___x_5096_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_5094_);
v___x_5097_ = l_Lean_Syntax_matchesNull(v___x_5094_, v___x_5096_);
if (v___x_5097_ == 0)
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; 
lean_dec(v___x_5094_);
lean_dec(v___x_5037_);
v___x_5098_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5027_);
v___x_5099_ = l_Lean_MessageData_ofSyntax(v_a_5027_);
v___x_5100_ = l_Lean_indentD(v___x_5099_);
v___x_5101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5098_);
lean_ctor_set(v___x_5101_, 1, v___x_5100_);
v___x_5102_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5101_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_dec_ref_known(v___x_5102_, 1);
v_snd_5009_ = v_b_5000_;
goto v___jp_5008_;
}
else
{
lean_object* v_a_5103_; 
v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
lean_inc(v_a_5103_);
lean_dec_ref_known(v___x_5102_, 1);
v_a_5014_ = v_a_5103_;
goto v___jp_5013_;
}
}
else
{
lean_object* v___x_5104_; lean_object* v___x_5105_; uint8_t v___x_5106_; 
v___x_5104_ = l_Lean_Syntax_getArg(v___x_5094_, v___x_5036_);
lean_dec(v___x_5094_);
v___x_5105_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_5104_);
v___x_5106_ = l_Lean_Syntax_isOfKind(v___x_5104_, v___x_5105_);
if (v___x_5106_ == 0)
{
lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; 
lean_dec(v___x_5104_);
lean_dec(v___x_5037_);
v___x_5107_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5027_);
v___x_5108_ = l_Lean_MessageData_ofSyntax(v_a_5027_);
v___x_5109_ = l_Lean_indentD(v___x_5108_);
v___x_5110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5110_, 0, v___x_5107_);
lean_ctor_set(v___x_5110_, 1, v___x_5109_);
v___x_5111_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5110_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_dec_ref_known(v___x_5111_, 1);
v_snd_5009_ = v_b_5000_;
goto v___jp_5008_;
}
else
{
lean_object* v_a_5112_; 
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
lean_inc(v_a_5112_);
lean_dec_ref_known(v___x_5111_, 1);
v_a_5014_ = v_a_5112_;
goto v___jp_5013_;
}
}
else
{
lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; 
v___x_5113_ = lean_box(0);
v___x_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5114_, 0, v___x_5104_);
lean_inc(v_a_5027_);
lean_inc_ref(v_b_5000_);
v___x_5115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_5037_, v_b_5000_, v_a_5027_, v___x_5039_, v_only_4995_, v_incremental_4996_, v___x_5113_, v___x_5114_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___x_5037_);
v___y_5021_ = v___x_5115_;
goto v___jp_5020_;
}
}
}
else
{
lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; 
lean_dec(v___x_5094_);
v___x_5116_ = lean_box(0);
v___x_5117_ = lean_box(0);
lean_inc(v_a_5027_);
lean_inc_ref(v_b_5000_);
v___x_5118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_5037_, v_b_5000_, v_a_5027_, v___x_5039_, v_only_4995_, v_incremental_4996_, v___x_5116_, v___x_5117_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___x_5037_);
v___y_5021_ = v___x_5118_;
goto v___jp_5020_;
}
}
}
else
{
lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; uint8_t v___x_5122_; 
v___x_5119_ = lean_unsigned_to_nat(1u);
v___x_5120_ = l_Lean_Syntax_getArg(v___x_5037_, v___x_5119_);
lean_dec(v___x_5037_);
v___x_5121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_5120_);
v___x_5122_ = l_Lean_Syntax_isOfKind(v___x_5120_, v___x_5121_);
if (v___x_5122_ == 0)
{
lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
lean_dec(v___x_5120_);
v___x_5123_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5027_);
v___x_5124_ = l_Lean_MessageData_ofSyntax(v_a_5027_);
v___x_5125_ = l_Lean_indentD(v___x_5124_);
v___x_5126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5126_, 0, v___x_5123_);
lean_ctor_set(v___x_5126_, 1, v___x_5125_);
v___x_5127_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5126_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_dec_ref_known(v___x_5127_, 1);
v_snd_5009_ = v_b_5000_;
goto v___jp_5008_;
}
else
{
lean_object* v_a_5128_; 
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
lean_inc(v_a_5128_);
lean_dec_ref_known(v___x_5127_, 1);
v_a_5014_ = v_a_5128_;
goto v___jp_5013_;
}
}
else
{
if (v_incremental_4996_ == 0)
{
lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5129_ = lean_box(0);
lean_inc_ref(v_b_5000_);
v___x_5130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_5120_, v___x_5029_, v_b_5000_, v___x_5129_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5021_ = v___x_5130_;
goto v___jp_5020_;
}
else
{
lean_object* v___x_5131_; lean_object* v___x_5132_; 
v___x_5131_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_5132_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_5027_, v___x_5131_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v_a_5133_; lean_object* v___x_5134_; 
v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_a_5133_);
lean_dec_ref_known(v___x_5132_, 1);
lean_inc_ref(v_b_5000_);
v___x_5134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_5120_, v___x_5029_, v_b_5000_, v_a_5133_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5021_ = v___x_5134_;
goto v___jp_5020_;
}
else
{
lean_object* v_a_5135_; 
lean_dec(v___x_5120_);
v_a_5135_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5132_, 1);
v_a_5014_ = v_a_5135_;
goto v___jp_5013_;
}
}
}
}
}
}
v___jp_5008_:
{
size_t v___x_5010_; size_t v___x_5011_; 
v___x_5010_ = ((size_t)1ULL);
v___x_5011_ = lean_usize_add(v_i_4999_, v___x_5010_);
v_i_4999_ = v___x_5011_;
v_b_5000_ = v_snd_5009_;
goto _start;
}
v___jp_5013_:
{
uint8_t v___x_5015_; 
v___x_5015_ = l_Lean_Exception_isInterrupt(v_a_5014_);
if (v___x_5015_ == 0)
{
uint8_t v___x_5016_; 
lean_inc_ref(v_a_5014_);
v___x_5016_ = l_Lean_Exception_isRuntime(v_a_5014_);
if (v___x_5016_ == 0)
{
if (v_lax_4994_ == 0)
{
lean_object* v___x_5017_; 
lean_dec_ref(v_b_5000_);
v___x_5017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5017_, 0, v_a_5014_);
return v___x_5017_;
}
else
{
lean_dec_ref(v_a_5014_);
v_snd_5009_ = v_b_5000_;
goto v___jp_5008_;
}
}
else
{
lean_object* v___x_5018_; 
lean_dec_ref(v_b_5000_);
v___x_5018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5018_, 0, v_a_5014_);
return v___x_5018_;
}
}
else
{
lean_object* v___x_5019_; 
lean_dec_ref(v_b_5000_);
v___x_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5019_, 0, v_a_5014_);
return v___x_5019_;
}
}
v___jp_5020_:
{
if (lean_obj_tag(v___y_5021_) == 0)
{
lean_object* v_a_5022_; lean_object* v_snd_5023_; 
lean_dec_ref(v_b_5000_);
v_a_5022_ = lean_ctor_get(v___y_5021_, 0);
lean_inc(v_a_5022_);
lean_dec_ref_known(v___y_5021_, 1);
v_snd_5023_ = lean_ctor_get(v_a_5022_, 1);
lean_inc(v_snd_5023_);
lean_dec(v_a_5022_);
v_snd_5009_ = v_snd_5023_;
goto v___jp_5008_;
}
else
{
lean_object* v_a_5024_; 
v_a_5024_ = lean_ctor_get(v___y_5021_, 0);
lean_inc(v_a_5024_);
lean_dec_ref_known(v___y_5021_, 1);
v_a_5014_ = v_a_5024_;
goto v___jp_5013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_5136_, lean_object* v_only_5137_, lean_object* v_incremental_5138_, lean_object* v_as_5139_, lean_object* v_sz_5140_, lean_object* v_i_5141_, lean_object* v_b_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
uint8_t v_lax_boxed_5150_; uint8_t v_only_boxed_5151_; uint8_t v_incremental_boxed_5152_; size_t v_sz_boxed_5153_; size_t v_i_boxed_5154_; lean_object* v_res_5155_; 
v_lax_boxed_5150_ = lean_unbox(v_lax_5136_);
v_only_boxed_5151_ = lean_unbox(v_only_5137_);
v_incremental_boxed_5152_ = lean_unbox(v_incremental_5138_);
v_sz_boxed_5153_ = lean_unbox_usize(v_sz_5140_);
lean_dec(v_sz_5140_);
v_i_boxed_5154_ = lean_unbox_usize(v_i_5141_);
lean_dec(v_i_5141_);
v_res_5155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_5150_, v_only_boxed_5151_, v_incremental_boxed_5152_, v_as_5139_, v_sz_boxed_5153_, v_i_boxed_5154_, v_b_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
lean_dec(v___y_5144_);
lean_dec_ref(v___y_5143_);
lean_dec_ref(v_as_5139_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_5156_, lean_object* v_ps_5157_, uint8_t v_only_5158_, uint8_t v_lax_5159_, uint8_t v_incremental_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_){
_start:
{
size_t v_sz_5168_; size_t v___x_5169_; lean_object* v___x_5170_; 
v_sz_5168_ = lean_array_size(v_ps_5157_);
v___x_5169_ = ((size_t)0ULL);
v___x_5170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_5159_, v_only_5158_, v_incremental_5160_, v_ps_5157_, v_sz_5168_, v___x_5169_, v_params_5156_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
return v___x_5170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_5171_, lean_object* v_ps_5172_, lean_object* v_only_5173_, lean_object* v_lax_5174_, lean_object* v_incremental_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_){
_start:
{
uint8_t v_only_boxed_5183_; uint8_t v_lax_boxed_5184_; uint8_t v_incremental_boxed_5185_; lean_object* v_res_5186_; 
v_only_boxed_5183_ = lean_unbox(v_only_5173_);
v_lax_boxed_5184_ = lean_unbox(v_lax_5174_);
v_incremental_boxed_5185_ = lean_unbox(v_incremental_5175_);
v_res_5186_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5171_, v_ps_5172_, v_only_boxed_5183_, v_lax_boxed_5184_, v_incremental_boxed_5185_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_);
lean_dec(v_a_5181_);
lean_dec_ref(v_a_5180_);
lean_dec(v_a_5179_);
lean_dec_ref(v_a_5178_);
lean_dec(v_a_5177_);
lean_dec_ref(v_a_5176_);
lean_dec_ref(v_ps_5172_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_){
_start:
{
lean_object* v_origin_5198_; 
v_origin_5198_ = lean_ctor_get(v_thm_5187_, 5);
if (lean_obj_tag(v_origin_5198_) == 0)
{
lean_object* v_declName_5199_; lean_object* v___x_5200_; 
lean_inc_ref(v_origin_5198_);
lean_dec_ref(v_thm_5187_);
v_declName_5199_ = lean_ctor_get(v_origin_5198_, 0);
lean_inc(v_declName_5199_);
lean_dec_ref_known(v_origin_5198_, 1);
v___x_5200_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_5199_, v_a_5195_, v_a_5196_);
return v___x_5200_;
}
else
{
lean_object* v_proof_5201_; lean_object* v___x_5202_; 
v_proof_5201_ = lean_ctor_get(v_thm_5187_, 1);
lean_inc_ref(v_proof_5201_);
lean_dec_ref(v_thm_5187_);
v___x_5202_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_5201_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
return v___x_5202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_){
_start:
{
lean_object* v_res_5214_; 
v_res_5214_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_, v_a_5210_, v_a_5211_, v_a_5212_);
lean_dec(v_a_5212_);
lean_dec_ref(v_a_5211_);
lean_dec(v_a_5210_);
lean_dec_ref(v_a_5209_);
lean_dec(v_a_5208_);
lean_dec_ref(v_a_5207_);
lean_dec(v_a_5206_);
lean_dec_ref(v_a_5205_);
lean_dec(v_a_5204_);
return v_res_5214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_5215_, size_t v_sz_5216_, size_t v_i_5217_, lean_object* v_b_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
uint8_t v___x_5229_; 
v___x_5229_ = lean_usize_dec_lt(v_i_5217_, v_sz_5216_);
if (v___x_5229_ == 0)
{
lean_object* v___x_5230_; 
v___x_5230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5230_, 0, v_b_5218_);
return v___x_5230_;
}
else
{
lean_object* v_snd_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5257_; 
v_snd_5231_ = lean_ctor_get(v_b_5218_, 1);
v_isSharedCheck_5257_ = !lean_is_exclusive(v_b_5218_);
if (v_isSharedCheck_5257_ == 0)
{
lean_object* v_unused_5258_; 
v_unused_5258_ = lean_ctor_get(v_b_5218_, 0);
lean_dec(v_unused_5258_);
v___x_5233_ = v_b_5218_;
v_isShared_5234_ = v_isSharedCheck_5257_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_snd_5231_);
lean_dec(v_b_5218_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5257_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5235_; lean_object* v_a_5237_; lean_object* v_a_5244_; lean_object* v___x_5245_; 
v___x_5235_ = lean_box(0);
v_a_5244_ = lean_array_uget_borrowed(v_as_5215_, v_i_5217_);
lean_inc(v_a_5244_);
v___x_5245_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5244_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_);
if (lean_obj_tag(v___x_5245_) == 0)
{
lean_object* v_a_5246_; uint8_t v___x_5247_; 
v_a_5246_ = lean_ctor_get(v___x_5245_, 0);
lean_inc(v_a_5246_);
lean_dec_ref_known(v___x_5245_, 1);
v___x_5247_ = lean_unbox(v_a_5246_);
lean_dec(v_a_5246_);
if (v___x_5247_ == 0)
{
v_a_5237_ = v_snd_5231_;
goto v___jp_5236_;
}
else
{
lean_object* v___x_5248_; 
lean_inc(v_a_5244_);
v___x_5248_ = l_Lean_PersistentArray_push___redArg(v_snd_5231_, v_a_5244_);
v_a_5237_ = v___x_5248_;
goto v___jp_5236_;
}
}
else
{
lean_object* v_a_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5256_; 
lean_del_object(v___x_5233_);
lean_dec(v_snd_5231_);
v_a_5249_ = lean_ctor_get(v___x_5245_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5251_ = v___x_5245_;
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_a_5249_);
lean_dec(v___x_5245_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5256_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v___x_5254_; 
if (v_isShared_5252_ == 0)
{
v___x_5254_ = v___x_5251_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_a_5249_);
v___x_5254_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
return v___x_5254_;
}
}
}
v___jp_5236_:
{
lean_object* v___x_5239_; 
if (v_isShared_5234_ == 0)
{
lean_ctor_set(v___x_5233_, 1, v_a_5237_);
lean_ctor_set(v___x_5233_, 0, v___x_5235_);
v___x_5239_ = v___x_5233_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v___x_5235_);
lean_ctor_set(v_reuseFailAlloc_5243_, 1, v_a_5237_);
v___x_5239_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
size_t v___x_5240_; size_t v___x_5241_; 
v___x_5240_ = ((size_t)1ULL);
v___x_5241_ = lean_usize_add(v_i_5217_, v___x_5240_);
v_i_5217_ = v___x_5241_;
v_b_5218_ = v___x_5239_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5259_, lean_object* v_sz_5260_, lean_object* v_i_5261_, lean_object* v_b_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_){
_start:
{
size_t v_sz_boxed_5273_; size_t v_i_boxed_5274_; lean_object* v_res_5275_; 
v_sz_boxed_5273_ = lean_unbox_usize(v_sz_5260_);
lean_dec(v_sz_5260_);
v_i_boxed_5274_ = lean_unbox_usize(v_i_5261_);
lean_dec(v_i_5261_);
v_res_5275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5259_, v_sz_boxed_5273_, v_i_boxed_5274_, v_b_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec(v___y_5265_);
lean_dec_ref(v___y_5264_);
lean_dec(v___y_5263_);
lean_dec_ref(v_as_5259_);
return v_res_5275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5276_, size_t v_sz_5277_, size_t v_i_5278_, lean_object* v_b_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_){
_start:
{
uint8_t v___x_5290_; 
v___x_5290_ = lean_usize_dec_lt(v_i_5278_, v_sz_5277_);
if (v___x_5290_ == 0)
{
lean_object* v___x_5291_; 
v___x_5291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5291_, 0, v_b_5279_);
return v___x_5291_;
}
else
{
lean_object* v_snd_5292_; lean_object* v___x_5294_; uint8_t v_isShared_5295_; uint8_t v_isSharedCheck_5318_; 
v_snd_5292_ = lean_ctor_get(v_b_5279_, 1);
v_isSharedCheck_5318_ = !lean_is_exclusive(v_b_5279_);
if (v_isSharedCheck_5318_ == 0)
{
lean_object* v_unused_5319_; 
v_unused_5319_ = lean_ctor_get(v_b_5279_, 0);
lean_dec(v_unused_5319_);
v___x_5294_ = v_b_5279_;
v_isShared_5295_ = v_isSharedCheck_5318_;
goto v_resetjp_5293_;
}
else
{
lean_inc(v_snd_5292_);
lean_dec(v_b_5279_);
v___x_5294_ = lean_box(0);
v_isShared_5295_ = v_isSharedCheck_5318_;
goto v_resetjp_5293_;
}
v_resetjp_5293_:
{
lean_object* v___x_5296_; lean_object* v_a_5298_; lean_object* v_a_5305_; lean_object* v___x_5306_; 
v___x_5296_ = lean_box(0);
v_a_5305_ = lean_array_uget_borrowed(v_as_5276_, v_i_5278_);
lean_inc(v_a_5305_);
v___x_5306_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5305_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
if (lean_obj_tag(v___x_5306_) == 0)
{
lean_object* v_a_5307_; uint8_t v___x_5308_; 
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
lean_inc(v_a_5307_);
lean_dec_ref_known(v___x_5306_, 1);
v___x_5308_ = lean_unbox(v_a_5307_);
lean_dec(v_a_5307_);
if (v___x_5308_ == 0)
{
v_a_5298_ = v_snd_5292_;
goto v___jp_5297_;
}
else
{
lean_object* v___x_5309_; 
lean_inc(v_a_5305_);
v___x_5309_ = l_Lean_PersistentArray_push___redArg(v_snd_5292_, v_a_5305_);
v_a_5298_ = v___x_5309_;
goto v___jp_5297_;
}
}
else
{
lean_object* v_a_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5317_; 
lean_del_object(v___x_5294_);
lean_dec(v_snd_5292_);
v_a_5310_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5312_ = v___x_5306_;
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_a_5310_);
lean_dec(v___x_5306_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v___x_5315_; 
if (v_isShared_5313_ == 0)
{
v___x_5315_ = v___x_5312_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5310_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
}
}
}
v___jp_5297_:
{
lean_object* v___x_5300_; 
if (v_isShared_5295_ == 0)
{
lean_ctor_set(v___x_5294_, 1, v_a_5298_);
lean_ctor_set(v___x_5294_, 0, v___x_5296_);
v___x_5300_ = v___x_5294_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v___x_5296_);
lean_ctor_set(v_reuseFailAlloc_5304_, 1, v_a_5298_);
v___x_5300_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
size_t v___x_5301_; size_t v___x_5302_; lean_object* v___x_5303_; 
v___x_5301_ = ((size_t)1ULL);
v___x_5302_ = lean_usize_add(v_i_5278_, v___x_5301_);
v___x_5303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5276_, v_sz_5277_, v___x_5302_, v___x_5300_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
return v___x_5303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5320_, lean_object* v_sz_5321_, lean_object* v_i_5322_, lean_object* v_b_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_){
_start:
{
size_t v_sz_boxed_5334_; size_t v_i_boxed_5335_; lean_object* v_res_5336_; 
v_sz_boxed_5334_ = lean_unbox_usize(v_sz_5321_);
lean_dec(v_sz_5321_);
v_i_boxed_5335_ = lean_unbox_usize(v_i_5322_);
lean_dec(v_i_5322_);
v_res_5336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5320_, v_sz_boxed_5334_, v_i_boxed_5335_, v_b_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_);
lean_dec(v___y_5332_);
lean_dec_ref(v___y_5331_);
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
lean_dec(v___y_5324_);
lean_dec_ref(v_as_5320_);
return v_res_5336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5337_, size_t v_sz_5338_, size_t v_i_5339_, lean_object* v_b_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
uint8_t v___x_5351_; 
v___x_5351_ = lean_usize_dec_lt(v_i_5339_, v_sz_5338_);
if (v___x_5351_ == 0)
{
lean_object* v___x_5352_; 
v___x_5352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5352_, 0, v_b_5340_);
return v___x_5352_;
}
else
{
lean_object* v_snd_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5379_; 
v_snd_5353_ = lean_ctor_get(v_b_5340_, 1);
v_isSharedCheck_5379_ = !lean_is_exclusive(v_b_5340_);
if (v_isSharedCheck_5379_ == 0)
{
lean_object* v_unused_5380_; 
v_unused_5380_ = lean_ctor_get(v_b_5340_, 0);
lean_dec(v_unused_5380_);
v___x_5355_ = v_b_5340_;
v_isShared_5356_ = v_isSharedCheck_5379_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_snd_5353_);
lean_dec(v_b_5340_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5379_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
lean_object* v___x_5357_; lean_object* v_a_5359_; lean_object* v_a_5366_; lean_object* v___x_5367_; 
v___x_5357_ = lean_box(0);
v_a_5366_ = lean_array_uget_borrowed(v_as_5337_, v_i_5339_);
lean_inc(v_a_5366_);
v___x_5367_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5366_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
if (lean_obj_tag(v___x_5367_) == 0)
{
lean_object* v_a_5368_; uint8_t v___x_5369_; 
v_a_5368_ = lean_ctor_get(v___x_5367_, 0);
lean_inc(v_a_5368_);
lean_dec_ref_known(v___x_5367_, 1);
v___x_5369_ = lean_unbox(v_a_5368_);
lean_dec(v_a_5368_);
if (v___x_5369_ == 0)
{
v_a_5359_ = v_snd_5353_;
goto v___jp_5358_;
}
else
{
lean_object* v___x_5370_; 
lean_inc(v_a_5366_);
v___x_5370_ = l_Lean_PersistentArray_push___redArg(v_snd_5353_, v_a_5366_);
v_a_5359_ = v___x_5370_;
goto v___jp_5358_;
}
}
else
{
lean_object* v_a_5371_; lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5378_; 
lean_del_object(v___x_5355_);
lean_dec(v_snd_5353_);
v_a_5371_ = lean_ctor_get(v___x_5367_, 0);
v_isSharedCheck_5378_ = !lean_is_exclusive(v___x_5367_);
if (v_isSharedCheck_5378_ == 0)
{
v___x_5373_ = v___x_5367_;
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
else
{
lean_inc(v_a_5371_);
lean_dec(v___x_5367_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5378_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v___x_5376_; 
if (v_isShared_5374_ == 0)
{
v___x_5376_ = v___x_5373_;
goto v_reusejp_5375_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_a_5371_);
v___x_5376_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5375_;
}
v_reusejp_5375_:
{
return v___x_5376_;
}
}
}
v___jp_5358_:
{
lean_object* v___x_5361_; 
if (v_isShared_5356_ == 0)
{
lean_ctor_set(v___x_5355_, 1, v_a_5359_);
lean_ctor_set(v___x_5355_, 0, v___x_5357_);
v___x_5361_ = v___x_5355_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v___x_5357_);
lean_ctor_set(v_reuseFailAlloc_5365_, 1, v_a_5359_);
v___x_5361_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
size_t v___x_5362_; size_t v___x_5363_; 
v___x_5362_ = ((size_t)1ULL);
v___x_5363_ = lean_usize_add(v_i_5339_, v___x_5362_);
v_i_5339_ = v___x_5363_;
v_b_5340_ = v___x_5361_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5381_, lean_object* v_sz_5382_, lean_object* v_i_5383_, lean_object* v_b_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_){
_start:
{
size_t v_sz_boxed_5395_; size_t v_i_boxed_5396_; lean_object* v_res_5397_; 
v_sz_boxed_5395_ = lean_unbox_usize(v_sz_5382_);
lean_dec(v_sz_5382_);
v_i_boxed_5396_ = lean_unbox_usize(v_i_5383_);
lean_dec(v_i_5383_);
v_res_5397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5381_, v_sz_boxed_5395_, v_i_boxed_5396_, v_b_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
lean_dec(v___y_5391_);
lean_dec_ref(v___y_5390_);
lean_dec(v___y_5389_);
lean_dec_ref(v___y_5388_);
lean_dec(v___y_5387_);
lean_dec_ref(v___y_5386_);
lean_dec(v___y_5385_);
lean_dec_ref(v_as_5381_);
return v_res_5397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5398_, size_t v_sz_5399_, size_t v_i_5400_, lean_object* v_b_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
uint8_t v___x_5412_; 
v___x_5412_ = lean_usize_dec_lt(v_i_5400_, v_sz_5399_);
if (v___x_5412_ == 0)
{
lean_object* v___x_5413_; 
v___x_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5413_, 0, v_b_5401_);
return v___x_5413_;
}
else
{
lean_object* v_snd_5414_; lean_object* v___x_5416_; uint8_t v_isShared_5417_; uint8_t v_isSharedCheck_5440_; 
v_snd_5414_ = lean_ctor_get(v_b_5401_, 1);
v_isSharedCheck_5440_ = !lean_is_exclusive(v_b_5401_);
if (v_isSharedCheck_5440_ == 0)
{
lean_object* v_unused_5441_; 
v_unused_5441_ = lean_ctor_get(v_b_5401_, 0);
lean_dec(v_unused_5441_);
v___x_5416_ = v_b_5401_;
v_isShared_5417_ = v_isSharedCheck_5440_;
goto v_resetjp_5415_;
}
else
{
lean_inc(v_snd_5414_);
lean_dec(v_b_5401_);
v___x_5416_ = lean_box(0);
v_isShared_5417_ = v_isSharedCheck_5440_;
goto v_resetjp_5415_;
}
v_resetjp_5415_:
{
lean_object* v___x_5418_; lean_object* v_a_5420_; lean_object* v_a_5427_; lean_object* v___x_5428_; 
v___x_5418_ = lean_box(0);
v_a_5427_ = lean_array_uget_borrowed(v_as_5398_, v_i_5400_);
lean_inc(v_a_5427_);
v___x_5428_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5427_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5429_; uint8_t v___x_5430_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
lean_inc(v_a_5429_);
lean_dec_ref_known(v___x_5428_, 1);
v___x_5430_ = lean_unbox(v_a_5429_);
lean_dec(v_a_5429_);
if (v___x_5430_ == 0)
{
v_a_5420_ = v_snd_5414_;
goto v___jp_5419_;
}
else
{
lean_object* v___x_5431_; 
lean_inc(v_a_5427_);
v___x_5431_ = l_Lean_PersistentArray_push___redArg(v_snd_5414_, v_a_5427_);
v_a_5420_ = v___x_5431_;
goto v___jp_5419_;
}
}
else
{
lean_object* v_a_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5439_; 
lean_del_object(v___x_5416_);
lean_dec(v_snd_5414_);
v_a_5432_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5439_ == 0)
{
v___x_5434_ = v___x_5428_;
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_a_5432_);
lean_dec(v___x_5428_);
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
v___jp_5419_:
{
lean_object* v___x_5422_; 
if (v_isShared_5417_ == 0)
{
lean_ctor_set(v___x_5416_, 1, v_a_5420_);
lean_ctor_set(v___x_5416_, 0, v___x_5418_);
v___x_5422_ = v___x_5416_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v___x_5418_);
lean_ctor_set(v_reuseFailAlloc_5426_, 1, v_a_5420_);
v___x_5422_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
size_t v___x_5423_; size_t v___x_5424_; lean_object* v___x_5425_; 
v___x_5423_ = ((size_t)1ULL);
v___x_5424_ = lean_usize_add(v_i_5400_, v___x_5423_);
v___x_5425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5398_, v_sz_5399_, v___x_5424_, v___x_5422_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
return v___x_5425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5442_, lean_object* v_sz_5443_, lean_object* v_i_5444_, lean_object* v_b_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_){
_start:
{
size_t v_sz_boxed_5456_; size_t v_i_boxed_5457_; lean_object* v_res_5458_; 
v_sz_boxed_5456_ = lean_unbox_usize(v_sz_5443_);
lean_dec(v_sz_5443_);
v_i_boxed_5457_ = lean_unbox_usize(v_i_5444_);
lean_dec(v_i_5444_);
v_res_5458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5442_, v_sz_boxed_5456_, v_i_boxed_5457_, v_b_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_);
lean_dec(v___y_5454_);
lean_dec_ref(v___y_5453_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
lean_dec(v___y_5450_);
lean_dec_ref(v___y_5449_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec(v___y_5446_);
lean_dec_ref(v_as_5442_);
return v_res_5458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5459_, lean_object* v_n_5460_, lean_object* v_b_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_){
_start:
{
if (lean_obj_tag(v_n_5460_) == 0)
{
lean_object* v_cs_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; size_t v_sz_5475_; size_t v___x_5476_; lean_object* v___x_5477_; 
v_cs_5472_ = lean_ctor_get(v_n_5460_, 0);
v___x_5473_ = lean_box(0);
v___x_5474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5474_, 0, v___x_5473_);
lean_ctor_set(v___x_5474_, 1, v_b_5461_);
v_sz_5475_ = lean_array_size(v_cs_5472_);
v___x_5476_ = ((size_t)0ULL);
v___x_5477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5459_, v_cs_5472_, v_sz_5475_, v___x_5476_, v___x_5474_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_);
if (lean_obj_tag(v___x_5477_) == 0)
{
lean_object* v_a_5478_; lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5492_; 
v_a_5478_ = lean_ctor_get(v___x_5477_, 0);
v_isSharedCheck_5492_ = !lean_is_exclusive(v___x_5477_);
if (v_isSharedCheck_5492_ == 0)
{
v___x_5480_ = v___x_5477_;
v_isShared_5481_ = v_isSharedCheck_5492_;
goto v_resetjp_5479_;
}
else
{
lean_inc(v_a_5478_);
lean_dec(v___x_5477_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5492_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v_fst_5482_; 
v_fst_5482_ = lean_ctor_get(v_a_5478_, 0);
if (lean_obj_tag(v_fst_5482_) == 0)
{
lean_object* v_snd_5483_; lean_object* v___x_5484_; lean_object* v___x_5486_; 
v_snd_5483_ = lean_ctor_get(v_a_5478_, 1);
lean_inc(v_snd_5483_);
lean_dec(v_a_5478_);
v___x_5484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5484_, 0, v_snd_5483_);
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 0, v___x_5484_);
v___x_5486_ = v___x_5480_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v___x_5484_);
v___x_5486_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
return v___x_5486_;
}
}
else
{
lean_object* v_val_5488_; lean_object* v___x_5490_; 
lean_inc_ref(v_fst_5482_);
lean_dec(v_a_5478_);
v_val_5488_ = lean_ctor_get(v_fst_5482_, 0);
lean_inc(v_val_5488_);
lean_dec_ref_known(v_fst_5482_, 1);
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 0, v_val_5488_);
v___x_5490_ = v___x_5480_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_val_5488_);
v___x_5490_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
return v___x_5490_;
}
}
}
}
else
{
lean_object* v_a_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5500_; 
v_a_5493_ = lean_ctor_get(v___x_5477_, 0);
v_isSharedCheck_5500_ = !lean_is_exclusive(v___x_5477_);
if (v_isSharedCheck_5500_ == 0)
{
v___x_5495_ = v___x_5477_;
v_isShared_5496_ = v_isSharedCheck_5500_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_a_5493_);
lean_dec(v___x_5477_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5500_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v___x_5498_; 
if (v_isShared_5496_ == 0)
{
v___x_5498_ = v___x_5495_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_a_5493_);
v___x_5498_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
return v___x_5498_;
}
}
}
}
else
{
lean_object* v_vs_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; size_t v_sz_5504_; size_t v___x_5505_; lean_object* v___x_5506_; 
v_vs_5501_ = lean_ctor_get(v_n_5460_, 0);
v___x_5502_ = lean_box(0);
v___x_5503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5503_, 0, v___x_5502_);
lean_ctor_set(v___x_5503_, 1, v_b_5461_);
v_sz_5504_ = lean_array_size(v_vs_5501_);
v___x_5505_ = ((size_t)0ULL);
v___x_5506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5501_, v_sz_5504_, v___x_5505_, v___x_5503_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_);
if (lean_obj_tag(v___x_5506_) == 0)
{
lean_object* v_a_5507_; lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5521_; 
v_a_5507_ = lean_ctor_get(v___x_5506_, 0);
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5506_);
if (v_isSharedCheck_5521_ == 0)
{
v___x_5509_ = v___x_5506_;
v_isShared_5510_ = v_isSharedCheck_5521_;
goto v_resetjp_5508_;
}
else
{
lean_inc(v_a_5507_);
lean_dec(v___x_5506_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5521_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v_fst_5511_; 
v_fst_5511_ = lean_ctor_get(v_a_5507_, 0);
if (lean_obj_tag(v_fst_5511_) == 0)
{
lean_object* v_snd_5512_; lean_object* v___x_5513_; lean_object* v___x_5515_; 
v_snd_5512_ = lean_ctor_get(v_a_5507_, 1);
lean_inc(v_snd_5512_);
lean_dec(v_a_5507_);
v___x_5513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5513_, 0, v_snd_5512_);
if (v_isShared_5510_ == 0)
{
lean_ctor_set(v___x_5509_, 0, v___x_5513_);
v___x_5515_ = v___x_5509_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v___x_5513_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
else
{
lean_object* v_val_5517_; lean_object* v___x_5519_; 
lean_inc_ref(v_fst_5511_);
lean_dec(v_a_5507_);
v_val_5517_ = lean_ctor_get(v_fst_5511_, 0);
lean_inc(v_val_5517_);
lean_dec_ref_known(v_fst_5511_, 1);
if (v_isShared_5510_ == 0)
{
lean_ctor_set(v___x_5509_, 0, v_val_5517_);
v___x_5519_ = v___x_5509_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_val_5517_);
v___x_5519_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5518_;
}
v_reusejp_5518_:
{
return v___x_5519_;
}
}
}
}
else
{
lean_object* v_a_5522_; lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5529_; 
v_a_5522_ = lean_ctor_get(v___x_5506_, 0);
v_isSharedCheck_5529_ = !lean_is_exclusive(v___x_5506_);
if (v_isSharedCheck_5529_ == 0)
{
v___x_5524_ = v___x_5506_;
v_isShared_5525_ = v_isSharedCheck_5529_;
goto v_resetjp_5523_;
}
else
{
lean_inc(v_a_5522_);
lean_dec(v___x_5506_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5530_, lean_object* v_as_5531_, size_t v_sz_5532_, size_t v_i_5533_, lean_object* v_b_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_){
_start:
{
uint8_t v___x_5545_; 
v___x_5545_ = lean_usize_dec_lt(v_i_5533_, v_sz_5532_);
if (v___x_5545_ == 0)
{
lean_object* v___x_5546_; 
v___x_5546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5546_, 0, v_b_5534_);
return v___x_5546_;
}
else
{
lean_object* v_snd_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5581_; 
v_snd_5547_ = lean_ctor_get(v_b_5534_, 1);
v_isSharedCheck_5581_ = !lean_is_exclusive(v_b_5534_);
if (v_isSharedCheck_5581_ == 0)
{
lean_object* v_unused_5582_; 
v_unused_5582_ = lean_ctor_get(v_b_5534_, 0);
lean_dec(v_unused_5582_);
v___x_5549_ = v_b_5534_;
v_isShared_5550_ = v_isSharedCheck_5581_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_snd_5547_);
lean_dec(v_b_5534_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5581_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5551_; lean_object* v_a_5552_; lean_object* v___x_5553_; 
v___x_5551_ = lean_box(0);
v_a_5552_ = lean_array_uget_borrowed(v_as_5531_, v_i_5533_);
lean_inc(v_snd_5547_);
v___x_5553_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5530_, v_a_5552_, v_snd_5547_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_);
if (lean_obj_tag(v___x_5553_) == 0)
{
lean_object* v_a_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5572_; 
v_a_5554_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5556_ = v___x_5553_;
v_isShared_5557_ = v_isSharedCheck_5572_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_a_5554_);
lean_dec(v___x_5553_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5572_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
if (lean_obj_tag(v_a_5554_) == 0)
{
lean_object* v___x_5558_; lean_object* v___x_5560_; 
v___x_5558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5558_, 0, v_a_5554_);
if (v_isShared_5550_ == 0)
{
lean_ctor_set(v___x_5549_, 0, v___x_5558_);
v___x_5560_ = v___x_5549_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v___x_5558_);
lean_ctor_set(v_reuseFailAlloc_5564_, 1, v_snd_5547_);
v___x_5560_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
lean_object* v___x_5562_; 
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 0, v___x_5560_);
v___x_5562_ = v___x_5556_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v___x_5560_);
v___x_5562_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
return v___x_5562_;
}
}
}
else
{
lean_object* v_a_5565_; lean_object* v___x_5567_; 
lean_del_object(v___x_5556_);
lean_dec(v_snd_5547_);
v_a_5565_ = lean_ctor_get(v_a_5554_, 0);
lean_inc(v_a_5565_);
lean_dec_ref_known(v_a_5554_, 1);
if (v_isShared_5550_ == 0)
{
lean_ctor_set(v___x_5549_, 1, v_a_5565_);
lean_ctor_set(v___x_5549_, 0, v___x_5551_);
v___x_5567_ = v___x_5549_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5551_);
lean_ctor_set(v_reuseFailAlloc_5571_, 1, v_a_5565_);
v___x_5567_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
size_t v___x_5568_; size_t v___x_5569_; 
v___x_5568_ = ((size_t)1ULL);
v___x_5569_ = lean_usize_add(v_i_5533_, v___x_5568_);
v_i_5533_ = v___x_5569_;
v_b_5534_ = v___x_5567_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5580_; 
lean_del_object(v___x_5549_);
lean_dec(v_snd_5547_);
v_a_5573_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5575_ = v___x_5553_;
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_a_5573_);
lean_dec(v___x_5553_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5583_, lean_object* v_as_5584_, lean_object* v_sz_5585_, lean_object* v_i_5586_, lean_object* v_b_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_){
_start:
{
size_t v_sz_boxed_5598_; size_t v_i_boxed_5599_; lean_object* v_res_5600_; 
v_sz_boxed_5598_ = lean_unbox_usize(v_sz_5585_);
lean_dec(v_sz_5585_);
v_i_boxed_5599_ = lean_unbox_usize(v_i_5586_);
lean_dec(v_i_5586_);
v_res_5600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5583_, v_as_5584_, v_sz_boxed_5598_, v_i_boxed_5599_, v_b_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
lean_dec(v___y_5592_);
lean_dec_ref(v___y_5591_);
lean_dec(v___y_5590_);
lean_dec_ref(v___y_5589_);
lean_dec(v___y_5588_);
lean_dec_ref(v_as_5584_);
lean_dec_ref(v_init_5583_);
return v_res_5600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5601_, lean_object* v_n_5602_, lean_object* v_b_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_){
_start:
{
lean_object* v_res_5614_; 
v_res_5614_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5601_, v_n_5602_, v_b_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_);
lean_dec(v___y_5612_);
lean_dec_ref(v___y_5611_);
lean_dec(v___y_5610_);
lean_dec_ref(v___y_5609_);
lean_dec(v___y_5608_);
lean_dec_ref(v___y_5607_);
lean_dec(v___y_5606_);
lean_dec_ref(v___y_5605_);
lean_dec(v___y_5604_);
lean_dec_ref(v_n_5602_);
lean_dec_ref(v_init_5601_);
return v_res_5614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5615_, lean_object* v_init_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_){
_start:
{
lean_object* v_root_5627_; lean_object* v_tail_5628_; lean_object* v___x_5629_; 
v_root_5627_ = lean_ctor_get(v_t_5615_, 0);
v_tail_5628_ = lean_ctor_get(v_t_5615_, 1);
lean_inc_ref(v_init_5616_);
v___x_5629_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5616_, v_root_5627_, v_init_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_);
lean_dec_ref(v_init_5616_);
if (lean_obj_tag(v___x_5629_) == 0)
{
lean_object* v_a_5630_; lean_object* v___x_5632_; uint8_t v_isShared_5633_; uint8_t v_isSharedCheck_5666_; 
v_a_5630_ = lean_ctor_get(v___x_5629_, 0);
v_isSharedCheck_5666_ = !lean_is_exclusive(v___x_5629_);
if (v_isSharedCheck_5666_ == 0)
{
v___x_5632_ = v___x_5629_;
v_isShared_5633_ = v_isSharedCheck_5666_;
goto v_resetjp_5631_;
}
else
{
lean_inc(v_a_5630_);
lean_dec(v___x_5629_);
v___x_5632_ = lean_box(0);
v_isShared_5633_ = v_isSharedCheck_5666_;
goto v_resetjp_5631_;
}
v_resetjp_5631_:
{
if (lean_obj_tag(v_a_5630_) == 0)
{
lean_object* v_a_5634_; lean_object* v___x_5636_; 
v_a_5634_ = lean_ctor_get(v_a_5630_, 0);
lean_inc(v_a_5634_);
lean_dec_ref_known(v_a_5630_, 1);
if (v_isShared_5633_ == 0)
{
lean_ctor_set(v___x_5632_, 0, v_a_5634_);
v___x_5636_ = v___x_5632_;
goto v_reusejp_5635_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_a_5634_);
v___x_5636_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5635_;
}
v_reusejp_5635_:
{
return v___x_5636_;
}
}
else
{
lean_object* v_a_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; size_t v_sz_5641_; size_t v___x_5642_; lean_object* v___x_5643_; 
lean_del_object(v___x_5632_);
v_a_5638_ = lean_ctor_get(v_a_5630_, 0);
lean_inc(v_a_5638_);
lean_dec_ref_known(v_a_5630_, 1);
v___x_5639_ = lean_box(0);
v___x_5640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___x_5639_);
lean_ctor_set(v___x_5640_, 1, v_a_5638_);
v_sz_5641_ = lean_array_size(v_tail_5628_);
v___x_5642_ = ((size_t)0ULL);
v___x_5643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5628_, v_sz_5641_, v___x_5642_, v___x_5640_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_);
if (lean_obj_tag(v___x_5643_) == 0)
{
lean_object* v_a_5644_; lean_object* v___x_5646_; uint8_t v_isShared_5647_; uint8_t v_isSharedCheck_5657_; 
v_a_5644_ = lean_ctor_get(v___x_5643_, 0);
v_isSharedCheck_5657_ = !lean_is_exclusive(v___x_5643_);
if (v_isSharedCheck_5657_ == 0)
{
v___x_5646_ = v___x_5643_;
v_isShared_5647_ = v_isSharedCheck_5657_;
goto v_resetjp_5645_;
}
else
{
lean_inc(v_a_5644_);
lean_dec(v___x_5643_);
v___x_5646_ = lean_box(0);
v_isShared_5647_ = v_isSharedCheck_5657_;
goto v_resetjp_5645_;
}
v_resetjp_5645_:
{
lean_object* v_fst_5648_; 
v_fst_5648_ = lean_ctor_get(v_a_5644_, 0);
if (lean_obj_tag(v_fst_5648_) == 0)
{
lean_object* v_snd_5649_; lean_object* v___x_5651_; 
v_snd_5649_ = lean_ctor_get(v_a_5644_, 1);
lean_inc(v_snd_5649_);
lean_dec(v_a_5644_);
if (v_isShared_5647_ == 0)
{
lean_ctor_set(v___x_5646_, 0, v_snd_5649_);
v___x_5651_ = v___x_5646_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_snd_5649_);
v___x_5651_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
return v___x_5651_;
}
}
else
{
lean_object* v_val_5653_; lean_object* v___x_5655_; 
lean_inc_ref(v_fst_5648_);
lean_dec(v_a_5644_);
v_val_5653_ = lean_ctor_get(v_fst_5648_, 0);
lean_inc(v_val_5653_);
lean_dec_ref_known(v_fst_5648_, 1);
if (v_isShared_5647_ == 0)
{
lean_ctor_set(v___x_5646_, 0, v_val_5653_);
v___x_5655_ = v___x_5646_;
goto v_reusejp_5654_;
}
else
{
lean_object* v_reuseFailAlloc_5656_; 
v_reuseFailAlloc_5656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_val_5653_);
v___x_5655_ = v_reuseFailAlloc_5656_;
goto v_reusejp_5654_;
}
v_reusejp_5654_:
{
return v___x_5655_;
}
}
}
}
else
{
lean_object* v_a_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
v_a_5658_ = lean_ctor_get(v___x_5643_, 0);
v_isSharedCheck_5665_ = !lean_is_exclusive(v___x_5643_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5660_ = v___x_5643_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_a_5658_);
lean_dec(v___x_5643_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5663_; 
if (v_isShared_5661_ == 0)
{
v___x_5663_ = v___x_5660_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5658_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
}
}
else
{
lean_object* v_a_5667_; lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5674_; 
v_a_5667_ = lean_ctor_get(v___x_5629_, 0);
v_isSharedCheck_5674_ = !lean_is_exclusive(v___x_5629_);
if (v_isSharedCheck_5674_ == 0)
{
v___x_5669_ = v___x_5629_;
v_isShared_5670_ = v_isSharedCheck_5674_;
goto v_resetjp_5668_;
}
else
{
lean_inc(v_a_5667_);
lean_dec(v___x_5629_);
v___x_5669_ = lean_box(0);
v_isShared_5670_ = v_isSharedCheck_5674_;
goto v_resetjp_5668_;
}
v_resetjp_5668_:
{
lean_object* v___x_5672_; 
if (v_isShared_5670_ == 0)
{
v___x_5672_ = v___x_5669_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5673_; 
v_reuseFailAlloc_5673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5673_, 0, v_a_5667_);
v___x_5672_ = v_reuseFailAlloc_5673_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
return v___x_5672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5675_, lean_object* v_init_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_){
_start:
{
lean_object* v_res_5687_; 
v_res_5687_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5675_, v_init_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5684_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5678_);
lean_dec(v___y_5677_);
lean_dec_ref(v_t_5675_);
return v_res_5687_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; 
v___x_5688_ = lean_unsigned_to_nat(32u);
v___x_5689_ = lean_mk_empty_array_with_capacity(v___x_5688_);
v___x_5690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5689_);
return v___x_5690_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v_result_5696_; 
v___x_5691_ = ((size_t)5ULL);
v___x_5692_ = lean_unsigned_to_nat(0u);
v___x_5693_ = lean_unsigned_to_nat(32u);
v___x_5694_ = lean_mk_empty_array_with_capacity(v___x_5693_);
v___x_5695_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5696_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5696_, 0, v___x_5695_);
lean_ctor_set(v_result_5696_, 1, v___x_5694_);
lean_ctor_set(v_result_5696_, 2, v___x_5692_);
lean_ctor_set(v_result_5696_, 3, v___x_5692_);
lean_ctor_set_usize(v_result_5696_, 4, v___x_5691_);
return v_result_5696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_){
_start:
{
lean_object* v_result_5708_; lean_object* v___x_5709_; 
v_result_5708_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5709_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5697_, v_result_5708_, v_a_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_);
return v___x_5709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_){
_start:
{
lean_object* v_res_5721_; 
v_res_5721_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5710_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_, v_a_5719_);
lean_dec(v_a_5719_);
lean_dec_ref(v_a_5718_);
lean_dec(v_a_5717_);
lean_dec_ref(v_a_5716_);
lean_dec(v_a_5715_);
lean_dec_ref(v_a_5714_);
lean_dec(v_a_5713_);
lean_dec_ref(v_a_5712_);
lean_dec(v_a_5711_);
lean_dec_ref(v_thms_5710_);
return v_res_5721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(lean_object* v___x_5722_, uint8_t v___x_5723_, lean_object* v_keepIdentParam_5724_, lean_object* v_x_5725_, lean_object* v_mod_x3f_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_){
_start:
{
lean_object* v___x_5734_; lean_object* v_id_5735_; lean_object* v___x_5736_; uint8_t v___x_5737_; 
v___x_5734_ = lean_unsigned_to_nat(2u);
v_id_5735_ = l_Lean_Syntax_getArg(v___x_5722_, v___x_5734_);
v___x_5736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v_id_5735_);
v___x_5737_ = l_Lean_Syntax_isOfKind(v_id_5735_, v___x_5736_);
if (v___x_5737_ == 0)
{
lean_object* v___x_5738_; lean_object* v___x_5739_; 
lean_dec(v_id_5735_);
lean_dec(v_mod_x3f_5726_);
lean_dec_ref(v_keepIdentParam_5724_);
v___x_5738_ = lean_box(v___x_5723_);
v___x_5739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5739_, 0, v___x_5738_);
return v___x_5739_;
}
else
{
lean_object* v___x_5740_; 
lean_inc(v___y_5732_);
lean_inc_ref(v___y_5731_);
lean_inc(v___y_5730_);
lean_inc_ref(v___y_5729_);
lean_inc(v___y_5728_);
lean_inc_ref(v___y_5727_);
v___x_5740_ = lean_apply_9(v_keepIdentParam_5724_, v_mod_x3f_5726_, v_id_5735_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, lean_box(0));
return v___x_5740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1___boxed(lean_object* v___x_5741_, lean_object* v___x_5742_, lean_object* v_keepIdentParam_5743_, lean_object* v_x_5744_, lean_object* v_mod_x3f_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_){
_start:
{
uint8_t v___x_6759__boxed_5753_; lean_object* v_res_5754_; 
v___x_6759__boxed_5753_ = lean_unbox(v___x_5742_);
v_res_5754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(v___x_5741_, v___x_6759__boxed_5753_, v_keepIdentParam_5743_, v_x_5744_, v_mod_x3f_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_, v___y_5751_);
lean_dec(v___y_5751_);
lean_dec_ref(v___y_5750_);
lean_dec(v___y_5749_);
lean_dec_ref(v___y_5748_);
lean_dec(v___y_5747_);
lean_dec_ref(v___y_5746_);
lean_dec(v___x_5741_);
return v_res_5754_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0(void){
_start:
{
lean_object* v___x_5755_; lean_object* v___x_5756_; 
v___x_5755_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_5756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5755_);
return v___x_5756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0(uint8_t v___x_5757_, uint8_t v___x_5758_, lean_object* v_mod_x3f_5759_, lean_object* v_id_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_){
_start:
{
lean_object* v___y_5769_; lean_object* v___y_5770_; lean_object* v___y_5771_; lean_object* v___y_5772_; lean_object* v___x_5825_; lean_object* v___x_5826_; 
v___x_5825_ = l_Lean_TSyntax_getId(v_id_5760_);
v___x_5826_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_5825_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_);
if (lean_obj_tag(v___x_5826_) == 0)
{
lean_object* v_a_5827_; lean_object* v___x_5829_; uint8_t v_isShared_5830_; uint8_t v_isSharedCheck_5837_; 
v_a_5827_ = lean_ctor_get(v___x_5826_, 0);
v_isSharedCheck_5837_ = !lean_is_exclusive(v___x_5826_);
if (v_isSharedCheck_5837_ == 0)
{
v___x_5829_ = v___x_5826_;
v_isShared_5830_ = v_isSharedCheck_5837_;
goto v_resetjp_5828_;
}
else
{
lean_inc(v_a_5827_);
lean_dec(v___x_5826_);
v___x_5829_ = lean_box(0);
v_isShared_5830_ = v_isSharedCheck_5837_;
goto v_resetjp_5828_;
}
v_resetjp_5828_:
{
if (lean_obj_tag(v_a_5827_) == 1)
{
lean_object* v_val_5831_; lean_object* v_snd_5832_; 
v_val_5831_ = lean_ctor_get(v_a_5827_, 0);
lean_inc(v_val_5831_);
lean_dec_ref_known(v_a_5827_, 1);
v_snd_5832_ = lean_ctor_get(v_val_5831_, 1);
lean_inc(v_snd_5832_);
lean_dec(v_val_5831_);
if (lean_obj_tag(v_snd_5832_) == 1)
{
lean_object* v___x_5833_; lean_object* v___x_5835_; 
lean_dec_ref_known(v_snd_5832_, 2);
lean_dec(v_id_5760_);
lean_dec(v_mod_x3f_5759_);
v___x_5833_ = lean_box(v___x_5758_);
if (v_isShared_5830_ == 0)
{
lean_ctor_set(v___x_5829_, 0, v___x_5833_);
v___x_5835_ = v___x_5829_;
goto v_reusejp_5834_;
}
else
{
lean_object* v_reuseFailAlloc_5836_; 
v_reuseFailAlloc_5836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5836_, 0, v___x_5833_);
v___x_5835_ = v_reuseFailAlloc_5836_;
goto v_reusejp_5834_;
}
v_reusejp_5834_:
{
return v___x_5835_;
}
}
else
{
lean_dec(v_snd_5832_);
lean_del_object(v___x_5829_);
goto v___jp_5797_;
}
}
else
{
lean_del_object(v___x_5829_);
lean_dec(v_a_5827_);
goto v___jp_5797_;
}
}
}
else
{
lean_object* v_a_5838_; lean_object* v___x_5840_; uint8_t v_isShared_5841_; uint8_t v_isSharedCheck_5845_; 
lean_dec(v_id_5760_);
lean_dec(v_mod_x3f_5759_);
v_a_5838_ = lean_ctor_get(v___x_5826_, 0);
v_isSharedCheck_5845_ = !lean_is_exclusive(v___x_5826_);
if (v_isSharedCheck_5845_ == 0)
{
v___x_5840_ = v___x_5826_;
v_isShared_5841_ = v_isSharedCheck_5845_;
goto v_resetjp_5839_;
}
else
{
lean_inc(v_a_5838_);
lean_dec(v___x_5826_);
v___x_5840_ = lean_box(0);
v_isShared_5841_ = v_isSharedCheck_5845_;
goto v_resetjp_5839_;
}
v_resetjp_5839_:
{
lean_object* v___x_5843_; 
if (v_isShared_5841_ == 0)
{
v___x_5843_ = v___x_5840_;
goto v_reusejp_5842_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v_a_5838_);
v___x_5843_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5842_;
}
v_reusejp_5842_:
{
return v___x_5843_;
}
}
}
v___jp_5768_:
{
lean_object* v___x_5773_; 
v___x_5773_ = l_Lean_realizeGlobalConstNoOverload(v_id_5760_, v___y_5771_, v___y_5772_);
if (lean_obj_tag(v___x_5773_) == 0)
{
lean_object* v_a_5774_; lean_object* v___x_5775_; 
v_a_5774_ = lean_ctor_get(v___x_5773_, 0);
lean_inc_n(v_a_5774_, 2);
lean_dec_ref_known(v___x_5773_, 1);
v___x_5775_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_a_5774_, v___x_5757_, v___y_5771_, v___y_5772_);
if (lean_obj_tag(v___x_5775_) == 0)
{
lean_object* v_a_5776_; uint8_t v___x_5777_; 
v_a_5776_ = lean_ctor_get(v___x_5775_, 0);
v___x_5777_ = lean_unbox(v_a_5776_);
if (v___x_5777_ == 0)
{
lean_object* v___x_5778_; lean_object* v___x_5779_; 
lean_dec_ref_known(v___x_5775_, 1);
v___x_5778_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0);
v___x_5779_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(v_a_5774_, v___x_5778_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
return v___x_5779_;
}
else
{
lean_dec(v_a_5774_);
return v___x_5775_;
}
}
else
{
lean_dec(v_a_5774_);
return v___x_5775_;
}
}
else
{
lean_object* v_a_5780_; lean_object* v___x_5782_; uint8_t v_isShared_5783_; uint8_t v_isSharedCheck_5796_; 
v_a_5780_ = lean_ctor_get(v___x_5773_, 0);
v_isSharedCheck_5796_ = !lean_is_exclusive(v___x_5773_);
if (v_isSharedCheck_5796_ == 0)
{
v___x_5782_ = v___x_5773_;
v_isShared_5783_ = v_isSharedCheck_5796_;
goto v_resetjp_5781_;
}
else
{
lean_inc(v_a_5780_);
lean_dec(v___x_5773_);
v___x_5782_ = lean_box(0);
v_isShared_5783_ = v_isSharedCheck_5796_;
goto v_resetjp_5781_;
}
v_resetjp_5781_:
{
uint8_t v___x_5784_; 
v___x_5784_ = l_Lean_Exception_isInterrupt(v_a_5780_);
if (v___x_5784_ == 0)
{
uint8_t v___x_5785_; 
lean_inc(v_a_5780_);
v___x_5785_ = l_Lean_Exception_isRuntime(v_a_5780_);
if (v___x_5785_ == 0)
{
lean_object* v___x_5786_; lean_object* v___x_5788_; 
lean_dec(v_a_5780_);
v___x_5786_ = lean_box(v___x_5785_);
if (v_isShared_5783_ == 0)
{
lean_ctor_set_tag(v___x_5782_, 0);
lean_ctor_set(v___x_5782_, 0, v___x_5786_);
v___x_5788_ = v___x_5782_;
goto v_reusejp_5787_;
}
else
{
lean_object* v_reuseFailAlloc_5789_; 
v_reuseFailAlloc_5789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5789_, 0, v___x_5786_);
v___x_5788_ = v_reuseFailAlloc_5789_;
goto v_reusejp_5787_;
}
v_reusejp_5787_:
{
return v___x_5788_;
}
}
else
{
lean_object* v___x_5791_; 
if (v_isShared_5783_ == 0)
{
v___x_5791_ = v___x_5782_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v_a_5780_);
v___x_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
return v___x_5791_;
}
}
}
else
{
lean_object* v___x_5794_; 
if (v_isShared_5783_ == 0)
{
v___x_5794_ = v___x_5782_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v_a_5780_);
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
v___jp_5797_:
{
if (lean_obj_tag(v_mod_x3f_5759_) == 1)
{
lean_object* v_val_5798_; lean_object* v___x_5799_; 
v_val_5798_ = lean_ctor_get(v_mod_x3f_5759_, 0);
lean_inc(v_val_5798_);
lean_dec_ref_known(v_mod_x3f_5759_, 1);
v___x_5799_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_5798_, v___y_5765_, v___y_5766_);
if (lean_obj_tag(v___x_5799_) == 0)
{
lean_object* v_a_5800_; lean_object* v___x_5802_; uint8_t v_isShared_5803_; uint8_t v_isSharedCheck_5816_; 
v_a_5800_ = lean_ctor_get(v___x_5799_, 0);
v_isSharedCheck_5816_ = !lean_is_exclusive(v___x_5799_);
if (v_isSharedCheck_5816_ == 0)
{
v___x_5802_ = v___x_5799_;
v_isShared_5803_ = v_isSharedCheck_5816_;
goto v_resetjp_5801_;
}
else
{
lean_inc(v_a_5800_);
lean_dec(v___x_5799_);
v___x_5802_ = lean_box(0);
v_isShared_5803_ = v_isSharedCheck_5816_;
goto v_resetjp_5801_;
}
v_resetjp_5801_:
{
switch(lean_obj_tag(v_a_5800_))
{
case 0:
{
lean_object* v___x_5804_; lean_object* v___x_5806_; 
lean_dec_ref_known(v_a_5800_, 1);
lean_dec(v_id_5760_);
v___x_5804_ = lean_box(v___x_5757_);
if (v_isShared_5803_ == 0)
{
lean_ctor_set(v___x_5802_, 0, v___x_5804_);
v___x_5806_ = v___x_5802_;
goto v_reusejp_5805_;
}
else
{
lean_object* v_reuseFailAlloc_5807_; 
v_reuseFailAlloc_5807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5807_, 0, v___x_5804_);
v___x_5806_ = v_reuseFailAlloc_5807_;
goto v_reusejp_5805_;
}
v_reusejp_5805_:
{
return v___x_5806_;
}
}
case 2:
{
lean_object* v___x_5808_; lean_object* v___x_5810_; 
lean_dec(v_id_5760_);
v___x_5808_ = lean_box(v___x_5757_);
if (v_isShared_5803_ == 0)
{
lean_ctor_set(v___x_5802_, 0, v___x_5808_);
v___x_5810_ = v___x_5802_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5811_; 
v_reuseFailAlloc_5811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5811_, 0, v___x_5808_);
v___x_5810_ = v_reuseFailAlloc_5811_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
return v___x_5810_;
}
}
case 3:
{
lean_del_object(v___x_5802_);
v___y_5769_ = v___y_5763_;
v___y_5770_ = v___y_5764_;
v___y_5771_ = v___y_5765_;
v___y_5772_ = v___y_5766_;
goto v___jp_5768_;
}
default: 
{
lean_object* v___x_5812_; lean_object* v___x_5814_; 
lean_dec(v_a_5800_);
lean_dec(v_id_5760_);
v___x_5812_ = lean_box(v___x_5758_);
if (v_isShared_5803_ == 0)
{
lean_ctor_set(v___x_5802_, 0, v___x_5812_);
v___x_5814_ = v___x_5802_;
goto v_reusejp_5813_;
}
else
{
lean_object* v_reuseFailAlloc_5815_; 
v_reuseFailAlloc_5815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5815_, 0, v___x_5812_);
v___x_5814_ = v_reuseFailAlloc_5815_;
goto v_reusejp_5813_;
}
v_reusejp_5813_:
{
return v___x_5814_;
}
}
}
}
}
else
{
lean_object* v_a_5817_; lean_object* v___x_5819_; uint8_t v_isShared_5820_; uint8_t v_isSharedCheck_5824_; 
lean_dec(v_id_5760_);
v_a_5817_ = lean_ctor_get(v___x_5799_, 0);
v_isSharedCheck_5824_ = !lean_is_exclusive(v___x_5799_);
if (v_isSharedCheck_5824_ == 0)
{
v___x_5819_ = v___x_5799_;
v_isShared_5820_ = v_isSharedCheck_5824_;
goto v_resetjp_5818_;
}
else
{
lean_inc(v_a_5817_);
lean_dec(v___x_5799_);
v___x_5819_ = lean_box(0);
v_isShared_5820_ = v_isSharedCheck_5824_;
goto v_resetjp_5818_;
}
v_resetjp_5818_:
{
lean_object* v___x_5822_; 
if (v_isShared_5820_ == 0)
{
v___x_5822_ = v___x_5819_;
goto v_reusejp_5821_;
}
else
{
lean_object* v_reuseFailAlloc_5823_; 
v_reuseFailAlloc_5823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5823_, 0, v_a_5817_);
v___x_5822_ = v_reuseFailAlloc_5823_;
goto v_reusejp_5821_;
}
v_reusejp_5821_:
{
return v___x_5822_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_5759_);
v___y_5769_ = v___y_5763_;
v___y_5770_ = v___y_5764_;
v___y_5771_ = v___y_5765_;
v___y_5772_ = v___y_5766_;
goto v___jp_5768_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___boxed(lean_object* v___x_5846_, lean_object* v___x_5847_, lean_object* v_mod_x3f_5848_, lean_object* v_id_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_){
_start:
{
uint8_t v___x_6806__boxed_5857_; uint8_t v___x_6807__boxed_5858_; lean_object* v_res_5859_; 
v___x_6806__boxed_5857_ = lean_unbox(v___x_5846_);
v___x_6807__boxed_5858_ = lean_unbox(v___x_5847_);
v_res_5859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0(v___x_6806__boxed_5857_, v___x_6807__boxed_5858_, v_mod_x3f_5848_, v_id_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_, v___y_5855_);
lean_dec(v___y_5855_);
lean_dec_ref(v___y_5854_);
lean_dec(v___y_5853_);
lean_dec_ref(v___y_5852_);
lean_dec(v___y_5851_);
lean_dec_ref(v___y_5850_);
return v_res_5859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(lean_object* v___x_5860_, uint8_t v___x_5861_, lean_object* v_keepIdentParam_5862_, lean_object* v_x_5863_, lean_object* v_mod_x3f_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_){
_start:
{
lean_object* v___x_5872_; lean_object* v_id_5873_; lean_object* v___x_5874_; uint8_t v___x_5875_; 
v___x_5872_ = lean_unsigned_to_nat(1u);
v_id_5873_ = l_Lean_Syntax_getArg(v___x_5860_, v___x_5872_);
v___x_5874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v_id_5873_);
v___x_5875_ = l_Lean_Syntax_isOfKind(v_id_5873_, v___x_5874_);
if (v___x_5875_ == 0)
{
lean_object* v___x_5876_; lean_object* v___x_5877_; 
lean_dec(v_id_5873_);
lean_dec(v_mod_x3f_5864_);
lean_dec_ref(v_keepIdentParam_5862_);
v___x_5876_ = lean_box(v___x_5861_);
v___x_5877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5877_, 0, v___x_5876_);
return v___x_5877_;
}
else
{
lean_object* v___x_5878_; 
lean_inc(v___y_5870_);
lean_inc_ref(v___y_5869_);
lean_inc(v___y_5868_);
lean_inc_ref(v___y_5867_);
lean_inc(v___y_5866_);
lean_inc_ref(v___y_5865_);
v___x_5878_ = lean_apply_9(v_keepIdentParam_5862_, v_mod_x3f_5864_, v_id_5873_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_, lean_box(0));
return v___x_5878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2___boxed(lean_object* v___x_5879_, lean_object* v___x_5880_, lean_object* v_keepIdentParam_5881_, lean_object* v_x_5882_, lean_object* v_mod_x3f_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_){
_start:
{
uint8_t v___x_6999__boxed_5891_; lean_object* v_res_5892_; 
v___x_6999__boxed_5891_ = lean_unbox(v___x_5880_);
v_res_5892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(v___x_5879_, v___x_6999__boxed_5891_, v_keepIdentParam_5881_, v_x_5882_, v_mod_x3f_5883_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_, v___y_5889_);
lean_dec(v___y_5889_);
lean_dec_ref(v___y_5888_);
lean_dec(v___y_5887_);
lean_dec_ref(v___y_5886_);
lean_dec(v___y_5885_);
lean_dec_ref(v___y_5884_);
lean_dec(v___x_5879_);
return v_res_5892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(lean_object* v_as_5893_, size_t v_i_5894_, size_t v_stop_5895_, lean_object* v_b_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_, lean_object* v___y_5900_, lean_object* v___y_5901_, lean_object* v___y_5902_){
_start:
{
lean_object* v_a_5905_; uint8_t v___x_5909_; 
v___x_5909_ = lean_usize_dec_eq(v_i_5894_, v_stop_5895_);
if (v___x_5909_ == 0)
{
lean_object* v___x_5910_; lean_object* v___y_5914_; lean_object* v___x_5925_; uint8_t v___x_5926_; 
v___x_5910_ = lean_array_uget_borrowed(v_as_5893_, v_i_5894_);
v___x_5925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v___x_5910_);
v___x_5926_ = l_Lean_Syntax_isOfKind(v___x_5910_, v___x_5925_);
if (v___x_5926_ == 0)
{
goto v___jp_5911_;
}
else
{
lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v_keepIdentParam_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; uint8_t v___x_5933_; 
v___x_5927_ = lean_box(v___x_5909_);
v___x_5928_ = lean_box(v___x_5926_);
v_keepIdentParam_5929_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___boxed), 11, 2);
lean_closure_set(v_keepIdentParam_5929_, 0, v___x_5927_);
lean_closure_set(v_keepIdentParam_5929_, 1, v___x_5928_);
v___x_5930_ = lean_unsigned_to_nat(0u);
v___x_5931_ = l_Lean_Syntax_getArg(v___x_5910_, v___x_5930_);
v___x_5932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_5931_);
v___x_5933_ = l_Lean_Syntax_isOfKind(v___x_5931_, v___x_5932_);
if (v___x_5933_ == 0)
{
lean_object* v___x_5934_; uint8_t v___x_5935_; 
v___x_5934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_5931_);
v___x_5935_ = l_Lean_Syntax_isOfKind(v___x_5931_, v___x_5934_);
if (v___x_5935_ == 0)
{
lean_object* v___x_5936_; uint8_t v___x_5937_; 
lean_dec_ref(v_keepIdentParam_5929_);
v___x_5936_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_5931_);
v___x_5937_ = l_Lean_Syntax_isOfKind(v___x_5931_, v___x_5936_);
if (v___x_5937_ == 0)
{
lean_object* v___x_5938_; uint8_t v___x_5939_; 
v___x_5938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_5931_);
v___x_5939_ = l_Lean_Syntax_isOfKind(v___x_5931_, v___x_5938_);
if (v___x_5939_ == 0)
{
lean_dec(v___x_5931_);
goto v___jp_5911_;
}
else
{
lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; uint8_t v___x_5943_; 
v___x_5940_ = lean_unsigned_to_nat(1u);
v___x_5941_ = l_Lean_Syntax_getArg(v___x_5931_, v___x_5940_);
lean_dec(v___x_5931_);
v___x_5942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13));
v___x_5943_ = l_Lean_Syntax_isOfKind(v___x_5941_, v___x_5942_);
if (v___x_5943_ == 0)
{
goto v___jp_5911_;
}
else
{
v_a_5905_ = v_b_5896_;
goto v___jp_5904_;
}
}
}
else
{
lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; uint8_t v___x_5947_; 
v___x_5944_ = lean_unsigned_to_nat(1u);
v___x_5945_ = l_Lean_Syntax_getArg(v___x_5931_, v___x_5944_);
lean_dec(v___x_5931_);
v___x_5946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
v___x_5947_ = l_Lean_Syntax_isOfKind(v___x_5945_, v___x_5946_);
if (v___x_5947_ == 0)
{
goto v___jp_5911_;
}
else
{
v_a_5905_ = v_b_5896_;
goto v___jp_5904_;
}
}
}
else
{
lean_object* v___x_5948_; lean_object* v___x_5949_; uint8_t v___x_5950_; 
v___x_5948_ = lean_unsigned_to_nat(1u);
v___x_5949_ = l_Lean_Syntax_getArg(v___x_5931_, v___x_5948_);
v___x_5950_ = l_Lean_Syntax_isNone(v___x_5949_);
if (v___x_5950_ == 0)
{
uint8_t v___x_5951_; 
lean_inc(v___x_5949_);
v___x_5951_ = l_Lean_Syntax_matchesNull(v___x_5949_, v___x_5948_);
if (v___x_5951_ == 0)
{
lean_dec(v___x_5949_);
lean_dec(v___x_5931_);
lean_dec_ref(v_keepIdentParam_5929_);
goto v___jp_5911_;
}
else
{
lean_object* v_mod_x3f_5952_; lean_object* v___x_5953_; uint8_t v___x_5954_; 
v_mod_x3f_5952_ = l_Lean_Syntax_getArg(v___x_5949_, v___x_5930_);
lean_dec(v___x_5949_);
v___x_5953_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v_mod_x3f_5952_);
v___x_5954_ = l_Lean_Syntax_isOfKind(v_mod_x3f_5952_, v___x_5953_);
if (v___x_5954_ == 0)
{
lean_dec(v_mod_x3f_5952_);
lean_dec(v___x_5931_);
lean_dec_ref(v_keepIdentParam_5929_);
goto v___jp_5911_;
}
else
{
lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; 
v___x_5955_ = lean_box(0);
v___x_5956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5956_, 0, v_mod_x3f_5952_);
v___x_5957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(v___x_5931_, v___x_5926_, v_keepIdentParam_5929_, v___x_5955_, v___x_5956_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_, v___y_5902_);
lean_dec(v___x_5931_);
v___y_5914_ = v___x_5957_;
goto v___jp_5913_;
}
}
}
else
{
lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; 
lean_dec(v___x_5949_);
v___x_5958_ = lean_box(0);
v___x_5959_ = lean_box(0);
v___x_5960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(v___x_5931_, v___x_5926_, v_keepIdentParam_5929_, v___x_5958_, v___x_5959_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_, v___y_5902_);
lean_dec(v___x_5931_);
v___y_5914_ = v___x_5960_;
goto v___jp_5913_;
}
}
}
else
{
lean_object* v___x_5961_; uint8_t v___x_5962_; 
v___x_5961_ = l_Lean_Syntax_getArg(v___x_5931_, v___x_5930_);
v___x_5962_ = l_Lean_Syntax_isNone(v___x_5961_);
if (v___x_5962_ == 0)
{
lean_object* v___x_5963_; uint8_t v___x_5964_; 
v___x_5963_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_5961_);
v___x_5964_ = l_Lean_Syntax_matchesNull(v___x_5961_, v___x_5963_);
if (v___x_5964_ == 0)
{
lean_dec(v___x_5961_);
lean_dec(v___x_5931_);
lean_dec_ref(v_keepIdentParam_5929_);
goto v___jp_5911_;
}
else
{
lean_object* v_mod_x3f_5965_; lean_object* v___x_5966_; uint8_t v___x_5967_; 
v_mod_x3f_5965_ = l_Lean_Syntax_getArg(v___x_5961_, v___x_5930_);
lean_dec(v___x_5961_);
v___x_5966_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v_mod_x3f_5965_);
v___x_5967_ = l_Lean_Syntax_isOfKind(v_mod_x3f_5965_, v___x_5966_);
if (v___x_5967_ == 0)
{
lean_dec(v_mod_x3f_5965_);
lean_dec(v___x_5931_);
lean_dec_ref(v_keepIdentParam_5929_);
goto v___jp_5911_;
}
else
{
lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; 
v___x_5968_ = lean_box(0);
v___x_5969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5969_, 0, v_mod_x3f_5965_);
v___x_5970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(v___x_5931_, v___x_5926_, v_keepIdentParam_5929_, v___x_5968_, v___x_5969_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_, v___y_5902_);
lean_dec(v___x_5931_);
v___y_5914_ = v___x_5970_;
goto v___jp_5913_;
}
}
}
else
{
lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; 
lean_dec(v___x_5961_);
v___x_5971_ = lean_box(0);
v___x_5972_ = lean_box(0);
v___x_5973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(v___x_5931_, v___x_5926_, v_keepIdentParam_5929_, v___x_5971_, v___x_5972_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_, v___y_5902_);
lean_dec(v___x_5931_);
v___y_5914_ = v___x_5973_;
goto v___jp_5913_;
}
}
}
v___jp_5911_:
{
lean_object* v___x_5912_; 
lean_inc(v___x_5910_);
v___x_5912_ = lean_array_push(v_b_5896_, v___x_5910_);
v_a_5905_ = v___x_5912_;
goto v___jp_5904_;
}
v___jp_5913_:
{
if (lean_obj_tag(v___y_5914_) == 0)
{
lean_object* v_a_5915_; uint8_t v___x_5916_; 
v_a_5915_ = lean_ctor_get(v___y_5914_, 0);
lean_inc(v_a_5915_);
lean_dec_ref_known(v___y_5914_, 1);
v___x_5916_ = lean_unbox(v_a_5915_);
lean_dec(v_a_5915_);
if (v___x_5916_ == 0)
{
v_a_5905_ = v_b_5896_;
goto v___jp_5904_;
}
else
{
goto v___jp_5911_;
}
}
else
{
lean_object* v_a_5917_; lean_object* v___x_5919_; uint8_t v_isShared_5920_; uint8_t v_isSharedCheck_5924_; 
lean_dec_ref(v_b_5896_);
v_a_5917_ = lean_ctor_get(v___y_5914_, 0);
v_isSharedCheck_5924_ = !lean_is_exclusive(v___y_5914_);
if (v_isSharedCheck_5924_ == 0)
{
v___x_5919_ = v___y_5914_;
v_isShared_5920_ = v_isSharedCheck_5924_;
goto v_resetjp_5918_;
}
else
{
lean_inc(v_a_5917_);
lean_dec(v___y_5914_);
v___x_5919_ = lean_box(0);
v_isShared_5920_ = v_isSharedCheck_5924_;
goto v_resetjp_5918_;
}
v_resetjp_5918_:
{
lean_object* v___x_5922_; 
if (v_isShared_5920_ == 0)
{
v___x_5922_ = v___x_5919_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5923_; 
v_reuseFailAlloc_5923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5923_, 0, v_a_5917_);
v___x_5922_ = v_reuseFailAlloc_5923_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
return v___x_5922_;
}
}
}
}
}
else
{
lean_object* v___x_5974_; 
v___x_5974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5974_, 0, v_b_5896_);
return v___x_5974_;
}
v___jp_5904_:
{
size_t v___x_5906_; size_t v___x_5907_; 
v___x_5906_ = ((size_t)1ULL);
v___x_5907_ = lean_usize_add(v_i_5894_, v___x_5906_);
v_i_5894_ = v___x_5907_;
v_b_5896_ = v_a_5905_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___boxed(lean_object* v_as_5975_, lean_object* v_i_5976_, lean_object* v_stop_5977_, lean_object* v_b_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_){
_start:
{
size_t v_i_boxed_5986_; size_t v_stop_boxed_5987_; lean_object* v_res_5988_; 
v_i_boxed_5986_ = lean_unbox_usize(v_i_5976_);
lean_dec(v_i_5976_);
v_stop_boxed_5987_ = lean_unbox_usize(v_stop_5977_);
lean_dec(v_stop_5977_);
v_res_5988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(v_as_5975_, v_i_boxed_5986_, v_stop_boxed_5987_, v_b_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_);
lean_dec(v___y_5984_);
lean_dec_ref(v___y_5983_);
lean_dec(v___y_5982_);
lean_dec_ref(v___y_5981_);
lean_dec(v___y_5980_);
lean_dec_ref(v___y_5979_);
lean_dec_ref(v_as_5975_);
return v_res_5988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_getPreservedParams(lean_object* v_params_5991_, lean_object* v_a_5992_, lean_object* v_a_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_){
_start:
{
lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; uint8_t v___x_6002_; 
v___x_5999_ = lean_unsigned_to_nat(0u);
v___x_6000_ = lean_array_get_size(v_params_5991_);
v___x_6001_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_getPreservedParams___closed__0));
v___x_6002_ = lean_nat_dec_lt(v___x_5999_, v___x_6000_);
if (v___x_6002_ == 0)
{
lean_object* v___x_6003_; 
v___x_6003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6001_);
return v___x_6003_;
}
else
{
size_t v___x_6004_; size_t v___x_6005_; lean_object* v___x_6006_; 
v___x_6004_ = ((size_t)0ULL);
v___x_6005_ = lean_usize_of_nat(v___x_6000_);
v___x_6006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(v_params_5991_, v___x_6004_, v___x_6005_, v___x_6001_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_);
return v___x_6006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_getPreservedParams___boxed(lean_object* v_params_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_, lean_object* v_a_6012_, lean_object* v_a_6013_, lean_object* v_a_6014_){
_start:
{
lean_object* v_res_6015_; 
v_res_6015_ = l_Lean_Elab_Tactic_Grind_getPreservedParams(v_params_6007_, v_a_6008_, v_a_6009_, v_a_6010_, v_a_6011_, v_a_6012_, v_a_6013_);
lean_dec(v_a_6013_);
lean_dec_ref(v_a_6012_);
lean_dec(v_a_6011_);
lean_dec_ref(v_a_6010_);
lean_dec(v_a_6009_);
lean_dec_ref(v_a_6008_);
lean_dec_ref(v_params_6007_);
return v_res_6015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_6018_, lean_object* v_newThms_6019_, lean_object* v_gmt_6020_, lean_object* v_numInstances_6021_, lean_object* v_numDelayedInstances_6022_, lean_object* v_num_6023_, lean_object* v_preInstances_6024_, lean_object* v_nextThmIdx_6025_, lean_object* v_matchEqNames_6026_, lean_object* v_delayedThmInsts_6027_, lean_object* v_nextDeclIdx_6028_, lean_object* v_enodeMap_6029_, lean_object* v_exprs_6030_, lean_object* v_parents_6031_, lean_object* v_congrTable_6032_, lean_object* v_appMap_6033_, lean_object* v_indicesFound_6034_, lean_object* v_toProcess_6035_, lean_object* v_internalizing_6036_, uint8_t v_inconsistent_6037_, lean_object* v_nextIdx_6038_, lean_object* v_newRawFacts_6039_, lean_object* v_facts_6040_, lean_object* v_extThms_6041_, lean_object* v_inj_6042_, lean_object* v_split_6043_, lean_object* v_clean_6044_, lean_object* v_sstates_6045_, lean_object* v_mvarId_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_){
_start:
{
lean_object* v___x_6057_; 
v___x_6057_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_6018_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_);
if (lean_obj_tag(v___x_6057_) == 0)
{
lean_object* v_a_6058_; lean_object* v___x_6059_; 
v_a_6058_ = lean_ctor_get(v___x_6057_, 0);
lean_inc(v_a_6058_);
lean_dec_ref_known(v___x_6057_, 1);
v___x_6059_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_6019_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_);
if (lean_obj_tag(v___x_6059_) == 0)
{
lean_object* v_a_6060_; lean_object* v___x_6062_; uint8_t v_isShared_6063_; uint8_t v_isSharedCheck_6071_; 
v_a_6060_ = lean_ctor_get(v___x_6059_, 0);
v_isSharedCheck_6071_ = !lean_is_exclusive(v___x_6059_);
if (v_isSharedCheck_6071_ == 0)
{
v___x_6062_ = v___x_6059_;
v_isShared_6063_ = v_isSharedCheck_6071_;
goto v_resetjp_6061_;
}
else
{
lean_inc(v_a_6060_);
lean_dec(v___x_6059_);
v___x_6062_ = lean_box(0);
v_isShared_6063_ = v_isSharedCheck_6071_;
goto v_resetjp_6061_;
}
v_resetjp_6061_:
{
lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6069_; 
v___x_6064_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_6065_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6064_);
lean_ctor_set(v___x_6065_, 1, v_gmt_6020_);
lean_ctor_set(v___x_6065_, 2, v_a_6058_);
lean_ctor_set(v___x_6065_, 3, v_a_6060_);
lean_ctor_set(v___x_6065_, 4, v_numInstances_6021_);
lean_ctor_set(v___x_6065_, 5, v_numDelayedInstances_6022_);
lean_ctor_set(v___x_6065_, 6, v_num_6023_);
lean_ctor_set(v___x_6065_, 7, v_preInstances_6024_);
lean_ctor_set(v___x_6065_, 8, v_nextThmIdx_6025_);
lean_ctor_set(v___x_6065_, 9, v_matchEqNames_6026_);
lean_ctor_set(v___x_6065_, 10, v_delayedThmInsts_6027_);
v___x_6066_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v___x_6066_, 0, v_nextDeclIdx_6028_);
lean_ctor_set(v___x_6066_, 1, v_enodeMap_6029_);
lean_ctor_set(v___x_6066_, 2, v_exprs_6030_);
lean_ctor_set(v___x_6066_, 3, v_parents_6031_);
lean_ctor_set(v___x_6066_, 4, v_congrTable_6032_);
lean_ctor_set(v___x_6066_, 5, v_appMap_6033_);
lean_ctor_set(v___x_6066_, 6, v_indicesFound_6034_);
lean_ctor_set(v___x_6066_, 7, v_toProcess_6035_);
lean_ctor_set(v___x_6066_, 8, v_internalizing_6036_);
lean_ctor_set(v___x_6066_, 9, v_nextIdx_6038_);
lean_ctor_set(v___x_6066_, 10, v_newRawFacts_6039_);
lean_ctor_set(v___x_6066_, 11, v_facts_6040_);
lean_ctor_set(v___x_6066_, 12, v_extThms_6041_);
lean_ctor_set(v___x_6066_, 13, v___x_6065_);
lean_ctor_set(v___x_6066_, 14, v_inj_6042_);
lean_ctor_set(v___x_6066_, 15, v_split_6043_);
lean_ctor_set(v___x_6066_, 16, v_clean_6044_);
lean_ctor_set(v___x_6066_, 17, v_sstates_6045_);
lean_ctor_set_uint8(v___x_6066_, sizeof(void*)*18, v_inconsistent_6037_);
v___x_6067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6066_);
lean_ctor_set(v___x_6067_, 1, v_mvarId_6046_);
if (v_isShared_6063_ == 0)
{
lean_ctor_set(v___x_6062_, 0, v___x_6067_);
v___x_6069_ = v___x_6062_;
goto v_reusejp_6068_;
}
else
{
lean_object* v_reuseFailAlloc_6070_; 
v_reuseFailAlloc_6070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6070_, 0, v___x_6067_);
v___x_6069_ = v_reuseFailAlloc_6070_;
goto v_reusejp_6068_;
}
v_reusejp_6068_:
{
return v___x_6069_;
}
}
}
else
{
lean_object* v_a_6072_; lean_object* v___x_6074_; uint8_t v_isShared_6075_; uint8_t v_isSharedCheck_6079_; 
lean_dec(v_a_6058_);
lean_dec(v_mvarId_6046_);
lean_dec_ref(v_sstates_6045_);
lean_dec_ref(v_clean_6044_);
lean_dec_ref(v_split_6043_);
lean_dec_ref(v_inj_6042_);
lean_dec_ref(v_extThms_6041_);
lean_dec_ref(v_facts_6040_);
lean_dec_ref(v_newRawFacts_6039_);
lean_dec(v_nextIdx_6038_);
lean_dec_ref(v_internalizing_6036_);
lean_dec_ref(v_toProcess_6035_);
lean_dec_ref(v_indicesFound_6034_);
lean_dec_ref(v_appMap_6033_);
lean_dec_ref(v_congrTable_6032_);
lean_dec_ref(v_parents_6031_);
lean_dec_ref(v_exprs_6030_);
lean_dec_ref(v_enodeMap_6029_);
lean_dec(v_nextDeclIdx_6028_);
lean_dec_ref(v_delayedThmInsts_6027_);
lean_dec_ref(v_matchEqNames_6026_);
lean_dec(v_nextThmIdx_6025_);
lean_dec_ref(v_preInstances_6024_);
lean_dec(v_num_6023_);
lean_dec(v_numDelayedInstances_6022_);
lean_dec(v_numInstances_6021_);
lean_dec(v_gmt_6020_);
v_a_6072_ = lean_ctor_get(v___x_6059_, 0);
v_isSharedCheck_6079_ = !lean_is_exclusive(v___x_6059_);
if (v_isSharedCheck_6079_ == 0)
{
v___x_6074_ = v___x_6059_;
v_isShared_6075_ = v_isSharedCheck_6079_;
goto v_resetjp_6073_;
}
else
{
lean_inc(v_a_6072_);
lean_dec(v___x_6059_);
v___x_6074_ = lean_box(0);
v_isShared_6075_ = v_isSharedCheck_6079_;
goto v_resetjp_6073_;
}
v_resetjp_6073_:
{
lean_object* v___x_6077_; 
if (v_isShared_6075_ == 0)
{
v___x_6077_ = v___x_6074_;
goto v_reusejp_6076_;
}
else
{
lean_object* v_reuseFailAlloc_6078_; 
v_reuseFailAlloc_6078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6078_, 0, v_a_6072_);
v___x_6077_ = v_reuseFailAlloc_6078_;
goto v_reusejp_6076_;
}
v_reusejp_6076_:
{
return v___x_6077_;
}
}
}
}
else
{
lean_object* v_a_6080_; lean_object* v___x_6082_; uint8_t v_isShared_6083_; uint8_t v_isSharedCheck_6087_; 
lean_dec(v_mvarId_6046_);
lean_dec_ref(v_sstates_6045_);
lean_dec_ref(v_clean_6044_);
lean_dec_ref(v_split_6043_);
lean_dec_ref(v_inj_6042_);
lean_dec_ref(v_extThms_6041_);
lean_dec_ref(v_facts_6040_);
lean_dec_ref(v_newRawFacts_6039_);
lean_dec(v_nextIdx_6038_);
lean_dec_ref(v_internalizing_6036_);
lean_dec_ref(v_toProcess_6035_);
lean_dec_ref(v_indicesFound_6034_);
lean_dec_ref(v_appMap_6033_);
lean_dec_ref(v_congrTable_6032_);
lean_dec_ref(v_parents_6031_);
lean_dec_ref(v_exprs_6030_);
lean_dec_ref(v_enodeMap_6029_);
lean_dec(v_nextDeclIdx_6028_);
lean_dec_ref(v_delayedThmInsts_6027_);
lean_dec_ref(v_matchEqNames_6026_);
lean_dec(v_nextThmIdx_6025_);
lean_dec_ref(v_preInstances_6024_);
lean_dec(v_num_6023_);
lean_dec(v_numDelayedInstances_6022_);
lean_dec(v_numInstances_6021_);
lean_dec(v_gmt_6020_);
v_a_6080_ = lean_ctor_get(v___x_6057_, 0);
v_isSharedCheck_6087_ = !lean_is_exclusive(v___x_6057_);
if (v_isSharedCheck_6087_ == 0)
{
v___x_6082_ = v___x_6057_;
v_isShared_6083_ = v_isSharedCheck_6087_;
goto v_resetjp_6081_;
}
else
{
lean_inc(v_a_6080_);
lean_dec(v___x_6057_);
v___x_6082_ = lean_box(0);
v_isShared_6083_ = v_isSharedCheck_6087_;
goto v_resetjp_6081_;
}
v_resetjp_6081_:
{
lean_object* v___x_6085_; 
if (v_isShared_6083_ == 0)
{
v___x_6085_ = v___x_6082_;
goto v_reusejp_6084_;
}
else
{
lean_object* v_reuseFailAlloc_6086_; 
v_reuseFailAlloc_6086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6086_, 0, v_a_6080_);
v___x_6085_ = v_reuseFailAlloc_6086_;
goto v_reusejp_6084_;
}
v_reusejp_6084_:
{
return v___x_6085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_6088_ = _args[0];
lean_object* v_newThms_6089_ = _args[1];
lean_object* v_gmt_6090_ = _args[2];
lean_object* v_numInstances_6091_ = _args[3];
lean_object* v_numDelayedInstances_6092_ = _args[4];
lean_object* v_num_6093_ = _args[5];
lean_object* v_preInstances_6094_ = _args[6];
lean_object* v_nextThmIdx_6095_ = _args[7];
lean_object* v_matchEqNames_6096_ = _args[8];
lean_object* v_delayedThmInsts_6097_ = _args[9];
lean_object* v_nextDeclIdx_6098_ = _args[10];
lean_object* v_enodeMap_6099_ = _args[11];
lean_object* v_exprs_6100_ = _args[12];
lean_object* v_parents_6101_ = _args[13];
lean_object* v_congrTable_6102_ = _args[14];
lean_object* v_appMap_6103_ = _args[15];
lean_object* v_indicesFound_6104_ = _args[16];
lean_object* v_toProcess_6105_ = _args[17];
lean_object* v_internalizing_6106_ = _args[18];
lean_object* v_inconsistent_6107_ = _args[19];
lean_object* v_nextIdx_6108_ = _args[20];
lean_object* v_newRawFacts_6109_ = _args[21];
lean_object* v_facts_6110_ = _args[22];
lean_object* v_extThms_6111_ = _args[23];
lean_object* v_inj_6112_ = _args[24];
lean_object* v_split_6113_ = _args[25];
lean_object* v_clean_6114_ = _args[26];
lean_object* v_sstates_6115_ = _args[27];
lean_object* v_mvarId_6116_ = _args[28];
lean_object* v___y_6117_ = _args[29];
lean_object* v___y_6118_ = _args[30];
lean_object* v___y_6119_ = _args[31];
lean_object* v___y_6120_ = _args[32];
lean_object* v___y_6121_ = _args[33];
lean_object* v___y_6122_ = _args[34];
lean_object* v___y_6123_ = _args[35];
lean_object* v___y_6124_ = _args[36];
lean_object* v___y_6125_ = _args[37];
lean_object* v___y_6126_ = _args[38];
_start:
{
uint8_t v_inconsistent_boxed_6127_; lean_object* v_res_6128_; 
v_inconsistent_boxed_6127_ = lean_unbox(v_inconsistent_6107_);
v_res_6128_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_6088_, v_newThms_6089_, v_gmt_6090_, v_numInstances_6091_, v_numDelayedInstances_6092_, v_num_6093_, v_preInstances_6094_, v_nextThmIdx_6095_, v_matchEqNames_6096_, v_delayedThmInsts_6097_, v_nextDeclIdx_6098_, v_enodeMap_6099_, v_exprs_6100_, v_parents_6101_, v_congrTable_6102_, v_appMap_6103_, v_indicesFound_6104_, v_toProcess_6105_, v_internalizing_6106_, v_inconsistent_boxed_6127_, v_nextIdx_6108_, v_newRawFacts_6109_, v_facts_6110_, v_extThms_6111_, v_inj_6112_, v_split_6113_, v_clean_6114_, v_sstates_6115_, v_mvarId_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_);
lean_dec(v___y_6125_);
lean_dec_ref(v___y_6124_);
lean_dec(v___y_6123_);
lean_dec_ref(v___y_6122_);
lean_dec(v___y_6121_);
lean_dec_ref(v___y_6120_);
lean_dec(v___y_6119_);
lean_dec_ref(v___y_6118_);
lean_dec(v___y_6117_);
lean_dec_ref(v_newThms_6089_);
lean_dec_ref(v_thms_6088_);
return v_res_6128_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_6129_; 
v___x_6129_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_6129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_6130_, size_t v_i_6131_, lean_object* v_bs_6132_){
_start:
{
uint8_t v___x_6133_; 
v___x_6133_ = lean_usize_dec_lt(v_i_6131_, v_sz_6130_);
if (v___x_6133_ == 0)
{
return v_bs_6132_;
}
else
{
lean_object* v_v_6134_; lean_object* v_casesTypes_6135_; lean_object* v_extThms_6136_; lean_object* v_funCC_6137_; lean_object* v_inj_6138_; lean_object* v___x_6140_; uint8_t v_isShared_6141_; uint8_t v_isSharedCheck_6152_; 
v_v_6134_ = lean_array_uget(v_bs_6132_, v_i_6131_);
v_casesTypes_6135_ = lean_ctor_get(v_v_6134_, 0);
v_extThms_6136_ = lean_ctor_get(v_v_6134_, 1);
v_funCC_6137_ = lean_ctor_get(v_v_6134_, 2);
v_inj_6138_ = lean_ctor_get(v_v_6134_, 4);
v_isSharedCheck_6152_ = !lean_is_exclusive(v_v_6134_);
if (v_isSharedCheck_6152_ == 0)
{
lean_object* v_unused_6153_; 
v_unused_6153_ = lean_ctor_get(v_v_6134_, 3);
lean_dec(v_unused_6153_);
v___x_6140_ = v_v_6134_;
v_isShared_6141_ = v_isSharedCheck_6152_;
goto v_resetjp_6139_;
}
else
{
lean_inc(v_inj_6138_);
lean_inc(v_funCC_6137_);
lean_inc(v_extThms_6136_);
lean_inc(v_casesTypes_6135_);
lean_dec(v_v_6134_);
v___x_6140_ = lean_box(0);
v_isShared_6141_ = v_isSharedCheck_6152_;
goto v_resetjp_6139_;
}
v_resetjp_6139_:
{
lean_object* v___x_6142_; lean_object* v_bs_x27_6143_; lean_object* v___x_6144_; lean_object* v___x_6146_; 
v___x_6142_ = lean_unsigned_to_nat(0u);
v_bs_x27_6143_ = lean_array_uset(v_bs_6132_, v_i_6131_, v___x_6142_);
v___x_6144_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_6141_ == 0)
{
lean_ctor_set(v___x_6140_, 3, v___x_6144_);
v___x_6146_ = v___x_6140_;
goto v_reusejp_6145_;
}
else
{
lean_object* v_reuseFailAlloc_6151_; 
v_reuseFailAlloc_6151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6151_, 0, v_casesTypes_6135_);
lean_ctor_set(v_reuseFailAlloc_6151_, 1, v_extThms_6136_);
lean_ctor_set(v_reuseFailAlloc_6151_, 2, v_funCC_6137_);
lean_ctor_set(v_reuseFailAlloc_6151_, 3, v___x_6144_);
lean_ctor_set(v_reuseFailAlloc_6151_, 4, v_inj_6138_);
v___x_6146_ = v_reuseFailAlloc_6151_;
goto v_reusejp_6145_;
}
v_reusejp_6145_:
{
size_t v___x_6147_; size_t v___x_6148_; lean_object* v___x_6149_; 
v___x_6147_ = ((size_t)1ULL);
v___x_6148_ = lean_usize_add(v_i_6131_, v___x_6147_);
v___x_6149_ = lean_array_uset(v_bs_x27_6143_, v_i_6131_, v___x_6146_);
v_i_6131_ = v___x_6148_;
v_bs_6132_ = v___x_6149_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_6154_, lean_object* v_i_6155_, lean_object* v_bs_6156_){
_start:
{
size_t v_sz_boxed_6157_; size_t v_i_boxed_6158_; lean_object* v_res_6159_; 
v_sz_boxed_6157_ = lean_unbox_usize(v_sz_6154_);
lean_dec(v_sz_6154_);
v_i_boxed_6158_ = lean_unbox_usize(v_i_6155_);
lean_dec(v_i_6155_);
v_res_6159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_6157_, v_i_boxed_6158_, v_bs_6156_);
return v_res_6159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_6160_, lean_object* v_ps_6161_, uint8_t v_only_6162_, lean_object* v_k_6163_, lean_object* v_a_6164_, lean_object* v_a_6165_, lean_object* v_a_6166_, lean_object* v_a_6167_, lean_object* v_a_6168_, lean_object* v_a_6169_, lean_object* v_a_6170_, lean_object* v_a_6171_){
_start:
{
lean_object* v___y_6174_; lean_object* v___y_6175_; lean_object* v___y_6176_; lean_object* v___y_6177_; lean_object* v___y_6178_; lean_object* v___y_6179_; lean_object* v___y_6180_; lean_object* v___y_6181_; lean_object* v___y_6182_; uint8_t v___y_6195_; uint8_t v___y_6196_; lean_object* v_params_6197_; lean_object* v___y_6198_; lean_object* v___y_6199_; lean_object* v___y_6200_; lean_object* v___y_6201_; lean_object* v___y_6202_; lean_object* v___y_6203_; lean_object* v___y_6204_; lean_object* v___y_6205_; uint8_t v___y_6309_; 
if (v_only_6162_ == 0)
{
lean_object* v___x_6331_; lean_object* v___x_6332_; uint8_t v___x_6333_; 
v___x_6331_ = lean_array_get_size(v_ps_6161_);
v___x_6332_ = lean_unsigned_to_nat(0u);
v___x_6333_ = lean_nat_dec_eq(v___x_6331_, v___x_6332_);
if (v___x_6333_ == 0)
{
v___y_6309_ = v___x_6333_;
goto v___jp_6308_;
}
else
{
lean_object* v___x_6334_; 
lean_dec_ref(v_params_6160_);
lean_inc(v_a_6171_);
lean_inc_ref(v_a_6170_);
lean_inc(v_a_6169_);
lean_inc_ref(v_a_6168_);
lean_inc(v_a_6167_);
lean_inc_ref(v_a_6166_);
lean_inc(v_a_6165_);
lean_inc_ref(v_a_6164_);
v___x_6334_ = lean_apply_9(v_k_6163_, v_a_6164_, v_a_6165_, v_a_6166_, v_a_6167_, v_a_6168_, v_a_6169_, v_a_6170_, v_a_6171_, lean_box(0));
return v___x_6334_;
}
}
else
{
uint8_t v___x_6335_; 
v___x_6335_ = 0;
v___y_6309_ = v___x_6335_;
goto v___jp_6308_;
}
v___jp_6173_:
{
lean_object* v___x_6183_; lean_object* v___x_6184_; 
v___x_6183_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_6183_, 0, v___y_6174_);
v___x_6184_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_6183_, v___y_6175_, v___y_6176_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_);
if (lean_obj_tag(v___x_6184_) == 0)
{
lean_object* v___x_6185_; 
lean_dec_ref_known(v___x_6184_, 1);
lean_inc(v___y_6182_);
lean_inc_ref(v___y_6181_);
lean_inc(v___y_6180_);
lean_inc_ref(v___y_6179_);
lean_inc(v___y_6178_);
lean_inc_ref(v___y_6177_);
lean_inc(v___y_6176_);
v___x_6185_ = lean_apply_9(v_k_6163_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_, lean_box(0));
return v___x_6185_;
}
else
{
lean_object* v_a_6186_; lean_object* v___x_6188_; uint8_t v_isShared_6189_; uint8_t v_isSharedCheck_6193_; 
lean_dec_ref(v___y_6175_);
lean_dec_ref(v_k_6163_);
v_a_6186_ = lean_ctor_get(v___x_6184_, 0);
v_isSharedCheck_6193_ = !lean_is_exclusive(v___x_6184_);
if (v_isSharedCheck_6193_ == 0)
{
v___x_6188_ = v___x_6184_;
v_isShared_6189_ = v_isSharedCheck_6193_;
goto v_resetjp_6187_;
}
else
{
lean_inc(v_a_6186_);
lean_dec(v___x_6184_);
v___x_6188_ = lean_box(0);
v_isShared_6189_ = v_isSharedCheck_6193_;
goto v_resetjp_6187_;
}
v_resetjp_6187_:
{
lean_object* v___x_6191_; 
if (v_isShared_6189_ == 0)
{
v___x_6191_ = v___x_6188_;
goto v_reusejp_6190_;
}
else
{
lean_object* v_reuseFailAlloc_6192_; 
v_reuseFailAlloc_6192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6192_, 0, v_a_6186_);
v___x_6191_ = v_reuseFailAlloc_6192_;
goto v_reusejp_6190_;
}
v_reusejp_6190_:
{
return v___x_6191_;
}
}
}
}
v___jp_6194_:
{
lean_object* v___x_6206_; 
v___x_6206_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_6197_, v_ps_6161_, v_only_6162_, v___y_6195_, v___y_6196_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_);
if (lean_obj_tag(v___x_6206_) == 0)
{
lean_object* v_a_6207_; lean_object* v_ctx_6208_; lean_object* v_anchorRefs_x3f_6209_; lean_object* v_toContext_6210_; lean_object* v_sctx_6211_; lean_object* v_methods_6212_; uint8_t v_sym_6213_; lean_object* v_simp_6214_; lean_object* v_simpMethods_6215_; lean_object* v_symSimpMethods_6216_; lean_object* v_symDSimpMethods_6217_; lean_object* v_config_6218_; uint8_t v_cheapCases_6219_; uint8_t v_reportMVarIssue_6220_; lean_object* v_splitSource_6221_; lean_object* v_ematchDiagSource_6222_; lean_object* v_symPrios_6223_; lean_object* v_extensions_6224_; uint8_t v_debug_6225_; uint8_t v_ematchDiag_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; 
v_a_6207_ = lean_ctor_get(v___x_6206_, 0);
lean_inc_n(v_a_6207_, 2);
lean_dec_ref_known(v___x_6206_, 1);
v_ctx_6208_ = lean_ctor_get(v___y_6198_, 1);
v_anchorRefs_x3f_6209_ = lean_ctor_get(v_a_6207_, 8);
v_toContext_6210_ = lean_ctor_get(v___y_6198_, 0);
v_sctx_6211_ = lean_ctor_get(v___y_6198_, 2);
v_methods_6212_ = lean_ctor_get(v___y_6198_, 3);
v_sym_6213_ = lean_ctor_get_uint8(v___y_6198_, sizeof(void*)*5);
v_simp_6214_ = lean_ctor_get(v_ctx_6208_, 0);
v_simpMethods_6215_ = lean_ctor_get(v_ctx_6208_, 1);
v_symSimpMethods_6216_ = lean_ctor_get(v_ctx_6208_, 2);
v_symDSimpMethods_6217_ = lean_ctor_get(v_ctx_6208_, 3);
v_config_6218_ = lean_ctor_get(v_ctx_6208_, 4);
v_cheapCases_6219_ = lean_ctor_get_uint8(v_ctx_6208_, sizeof(void*)*10);
v_reportMVarIssue_6220_ = lean_ctor_get_uint8(v_ctx_6208_, sizeof(void*)*10 + 1);
v_splitSource_6221_ = lean_ctor_get(v_ctx_6208_, 6);
v_ematchDiagSource_6222_ = lean_ctor_get(v_ctx_6208_, 7);
v_symPrios_6223_ = lean_ctor_get(v_ctx_6208_, 8);
v_extensions_6224_ = lean_ctor_get(v_ctx_6208_, 9);
v_debug_6225_ = lean_ctor_get_uint8(v_ctx_6208_, sizeof(void*)*10 + 2);
v_ematchDiag_6226_ = lean_ctor_get_uint8(v_ctx_6208_, sizeof(void*)*10 + 3);
lean_inc_ref(v_extensions_6224_);
lean_inc_ref(v_symPrios_6223_);
lean_inc(v_ematchDiagSource_6222_);
lean_inc(v_splitSource_6221_);
lean_inc(v_anchorRefs_x3f_6209_);
lean_inc_ref(v_config_6218_);
lean_inc_ref(v_symDSimpMethods_6217_);
lean_inc_ref(v_symSimpMethods_6216_);
lean_inc_ref(v_simpMethods_6215_);
lean_inc_ref(v_simp_6214_);
v___x_6227_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_6227_, 0, v_simp_6214_);
lean_ctor_set(v___x_6227_, 1, v_simpMethods_6215_);
lean_ctor_set(v___x_6227_, 2, v_symSimpMethods_6216_);
lean_ctor_set(v___x_6227_, 3, v_symDSimpMethods_6217_);
lean_ctor_set(v___x_6227_, 4, v_config_6218_);
lean_ctor_set(v___x_6227_, 5, v_anchorRefs_x3f_6209_);
lean_ctor_set(v___x_6227_, 6, v_splitSource_6221_);
lean_ctor_set(v___x_6227_, 7, v_ematchDiagSource_6222_);
lean_ctor_set(v___x_6227_, 8, v_symPrios_6223_);
lean_ctor_set(v___x_6227_, 9, v_extensions_6224_);
lean_ctor_set_uint8(v___x_6227_, sizeof(void*)*10, v_cheapCases_6219_);
lean_ctor_set_uint8(v___x_6227_, sizeof(void*)*10 + 1, v_reportMVarIssue_6220_);
lean_ctor_set_uint8(v___x_6227_, sizeof(void*)*10 + 2, v_debug_6225_);
lean_ctor_set_uint8(v___x_6227_, sizeof(void*)*10 + 3, v_ematchDiag_6226_);
lean_inc_ref(v_methods_6212_);
lean_inc_ref(v_sctx_6211_);
lean_inc_ref(v_toContext_6210_);
v___x_6228_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_6228_, 0, v_toContext_6210_);
lean_ctor_set(v___x_6228_, 1, v___x_6227_);
lean_ctor_set(v___x_6228_, 2, v_sctx_6211_);
lean_ctor_set(v___x_6228_, 3, v_methods_6212_);
lean_ctor_set(v___x_6228_, 4, v_a_6207_);
lean_ctor_set_uint8(v___x_6228_, sizeof(void*)*5, v_sym_6213_);
if (v_only_6162_ == 0)
{
v___y_6174_ = v_a_6207_;
v___y_6175_ = v___x_6228_;
v___y_6176_ = v___y_6199_;
v___y_6177_ = v___y_6200_;
v___y_6178_ = v___y_6201_;
v___y_6179_ = v___y_6202_;
v___y_6180_ = v___y_6203_;
v___y_6181_ = v___y_6204_;
v___y_6182_ = v___y_6205_;
goto v___jp_6173_;
}
else
{
lean_object* v___x_6229_; 
v___x_6229_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_6199_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_);
if (lean_obj_tag(v___x_6229_) == 0)
{
lean_object* v_a_6230_; lean_object* v_toGoalState_6231_; lean_object* v_ematch_6232_; lean_object* v_mvarId_6233_; lean_object* v___x_6235_; uint8_t v_isShared_6236_; uint8_t v_isSharedCheck_6290_; 
v_a_6230_ = lean_ctor_get(v___x_6229_, 0);
lean_inc(v_a_6230_);
lean_dec_ref_known(v___x_6229_, 1);
v_toGoalState_6231_ = lean_ctor_get(v_a_6230_, 0);
lean_inc_ref(v_toGoalState_6231_);
v_ematch_6232_ = lean_ctor_get(v_toGoalState_6231_, 13);
lean_inc_ref(v_ematch_6232_);
v_mvarId_6233_ = lean_ctor_get(v_a_6230_, 1);
v_isSharedCheck_6290_ = !lean_is_exclusive(v_a_6230_);
if (v_isSharedCheck_6290_ == 0)
{
lean_object* v_unused_6291_; 
v_unused_6291_ = lean_ctor_get(v_a_6230_, 0);
lean_dec(v_unused_6291_);
v___x_6235_ = v_a_6230_;
v_isShared_6236_ = v_isSharedCheck_6290_;
goto v_resetjp_6234_;
}
else
{
lean_inc(v_mvarId_6233_);
lean_dec(v_a_6230_);
v___x_6235_ = lean_box(0);
v_isShared_6236_ = v_isSharedCheck_6290_;
goto v_resetjp_6234_;
}
v_resetjp_6234_:
{
lean_object* v_nextDeclIdx_6237_; lean_object* v_enodeMap_6238_; lean_object* v_exprs_6239_; lean_object* v_parents_6240_; lean_object* v_congrTable_6241_; lean_object* v_appMap_6242_; lean_object* v_indicesFound_6243_; lean_object* v_toProcess_6244_; lean_object* v_internalizing_6245_; uint8_t v_inconsistent_6246_; lean_object* v_nextIdx_6247_; lean_object* v_newRawFacts_6248_; lean_object* v_facts_6249_; lean_object* v_extThms_6250_; lean_object* v_inj_6251_; lean_object* v_split_6252_; lean_object* v_clean_6253_; lean_object* v_sstates_6254_; lean_object* v_gmt_6255_; lean_object* v_thms_6256_; lean_object* v_newThms_6257_; lean_object* v_numInstances_6258_; lean_object* v_numDelayedInstances_6259_; lean_object* v_num_6260_; lean_object* v_preInstances_6261_; lean_object* v_nextThmIdx_6262_; lean_object* v_matchEqNames_6263_; lean_object* v_delayedThmInsts_6264_; lean_object* v___x_6265_; lean_object* v___f_6266_; lean_object* v___x_6267_; 
v_nextDeclIdx_6237_ = lean_ctor_get(v_toGoalState_6231_, 0);
lean_inc(v_nextDeclIdx_6237_);
v_enodeMap_6238_ = lean_ctor_get(v_toGoalState_6231_, 1);
lean_inc_ref(v_enodeMap_6238_);
v_exprs_6239_ = lean_ctor_get(v_toGoalState_6231_, 2);
lean_inc_ref(v_exprs_6239_);
v_parents_6240_ = lean_ctor_get(v_toGoalState_6231_, 3);
lean_inc_ref(v_parents_6240_);
v_congrTable_6241_ = lean_ctor_get(v_toGoalState_6231_, 4);
lean_inc_ref(v_congrTable_6241_);
v_appMap_6242_ = lean_ctor_get(v_toGoalState_6231_, 5);
lean_inc_ref(v_appMap_6242_);
v_indicesFound_6243_ = lean_ctor_get(v_toGoalState_6231_, 6);
lean_inc_ref(v_indicesFound_6243_);
v_toProcess_6244_ = lean_ctor_get(v_toGoalState_6231_, 7);
lean_inc_ref(v_toProcess_6244_);
v_internalizing_6245_ = lean_ctor_get(v_toGoalState_6231_, 8);
lean_inc_ref(v_internalizing_6245_);
v_inconsistent_6246_ = lean_ctor_get_uint8(v_toGoalState_6231_, sizeof(void*)*18);
v_nextIdx_6247_ = lean_ctor_get(v_toGoalState_6231_, 9);
lean_inc(v_nextIdx_6247_);
v_newRawFacts_6248_ = lean_ctor_get(v_toGoalState_6231_, 10);
lean_inc_ref(v_newRawFacts_6248_);
v_facts_6249_ = lean_ctor_get(v_toGoalState_6231_, 11);
lean_inc_ref(v_facts_6249_);
v_extThms_6250_ = lean_ctor_get(v_toGoalState_6231_, 12);
lean_inc_ref(v_extThms_6250_);
v_inj_6251_ = lean_ctor_get(v_toGoalState_6231_, 14);
lean_inc_ref(v_inj_6251_);
v_split_6252_ = lean_ctor_get(v_toGoalState_6231_, 15);
lean_inc_ref(v_split_6252_);
v_clean_6253_ = lean_ctor_get(v_toGoalState_6231_, 16);
lean_inc_ref(v_clean_6253_);
v_sstates_6254_ = lean_ctor_get(v_toGoalState_6231_, 17);
lean_inc_ref(v_sstates_6254_);
lean_dec_ref(v_toGoalState_6231_);
v_gmt_6255_ = lean_ctor_get(v_ematch_6232_, 1);
lean_inc(v_gmt_6255_);
v_thms_6256_ = lean_ctor_get(v_ematch_6232_, 2);
lean_inc_ref(v_thms_6256_);
v_newThms_6257_ = lean_ctor_get(v_ematch_6232_, 3);
lean_inc_ref(v_newThms_6257_);
v_numInstances_6258_ = lean_ctor_get(v_ematch_6232_, 4);
lean_inc(v_numInstances_6258_);
v_numDelayedInstances_6259_ = lean_ctor_get(v_ematch_6232_, 5);
lean_inc(v_numDelayedInstances_6259_);
v_num_6260_ = lean_ctor_get(v_ematch_6232_, 6);
lean_inc(v_num_6260_);
v_preInstances_6261_ = lean_ctor_get(v_ematch_6232_, 7);
lean_inc_ref(v_preInstances_6261_);
v_nextThmIdx_6262_ = lean_ctor_get(v_ematch_6232_, 8);
lean_inc(v_nextThmIdx_6262_);
v_matchEqNames_6263_ = lean_ctor_get(v_ematch_6232_, 9);
lean_inc_ref(v_matchEqNames_6263_);
v_delayedThmInsts_6264_ = lean_ctor_get(v_ematch_6232_, 10);
lean_inc_ref(v_delayedThmInsts_6264_);
lean_dec_ref(v_ematch_6232_);
v___x_6265_ = lean_box(v_inconsistent_6246_);
v___f_6266_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 39, 29);
lean_closure_set(v___f_6266_, 0, v_thms_6256_);
lean_closure_set(v___f_6266_, 1, v_newThms_6257_);
lean_closure_set(v___f_6266_, 2, v_gmt_6255_);
lean_closure_set(v___f_6266_, 3, v_numInstances_6258_);
lean_closure_set(v___f_6266_, 4, v_numDelayedInstances_6259_);
lean_closure_set(v___f_6266_, 5, v_num_6260_);
lean_closure_set(v___f_6266_, 6, v_preInstances_6261_);
lean_closure_set(v___f_6266_, 7, v_nextThmIdx_6262_);
lean_closure_set(v___f_6266_, 8, v_matchEqNames_6263_);
lean_closure_set(v___f_6266_, 9, v_delayedThmInsts_6264_);
lean_closure_set(v___f_6266_, 10, v_nextDeclIdx_6237_);
lean_closure_set(v___f_6266_, 11, v_enodeMap_6238_);
lean_closure_set(v___f_6266_, 12, v_exprs_6239_);
lean_closure_set(v___f_6266_, 13, v_parents_6240_);
lean_closure_set(v___f_6266_, 14, v_congrTable_6241_);
lean_closure_set(v___f_6266_, 15, v_appMap_6242_);
lean_closure_set(v___f_6266_, 16, v_indicesFound_6243_);
lean_closure_set(v___f_6266_, 17, v_toProcess_6244_);
lean_closure_set(v___f_6266_, 18, v_internalizing_6245_);
lean_closure_set(v___f_6266_, 19, v___x_6265_);
lean_closure_set(v___f_6266_, 20, v_nextIdx_6247_);
lean_closure_set(v___f_6266_, 21, v_newRawFacts_6248_);
lean_closure_set(v___f_6266_, 22, v_facts_6249_);
lean_closure_set(v___f_6266_, 23, v_extThms_6250_);
lean_closure_set(v___f_6266_, 24, v_inj_6251_);
lean_closure_set(v___f_6266_, 25, v_split_6252_);
lean_closure_set(v___f_6266_, 26, v_clean_6253_);
lean_closure_set(v___f_6266_, 27, v_sstates_6254_);
lean_closure_set(v___f_6266_, 28, v_mvarId_6233_);
v___x_6267_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_6266_, v___x_6228_, v___y_6199_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_);
if (lean_obj_tag(v___x_6267_) == 0)
{
lean_object* v_a_6268_; lean_object* v___x_6269_; lean_object* v___x_6271_; 
v_a_6268_ = lean_ctor_get(v___x_6267_, 0);
lean_inc(v_a_6268_);
lean_dec_ref_known(v___x_6267_, 1);
v___x_6269_ = lean_box(0);
if (v_isShared_6236_ == 0)
{
lean_ctor_set_tag(v___x_6235_, 1);
lean_ctor_set(v___x_6235_, 1, v___x_6269_);
lean_ctor_set(v___x_6235_, 0, v_a_6268_);
v___x_6271_ = v___x_6235_;
goto v_reusejp_6270_;
}
else
{
lean_object* v_reuseFailAlloc_6281_; 
v_reuseFailAlloc_6281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6281_, 0, v_a_6268_);
lean_ctor_set(v_reuseFailAlloc_6281_, 1, v___x_6269_);
v___x_6271_ = v_reuseFailAlloc_6281_;
goto v_reusejp_6270_;
}
v_reusejp_6270_:
{
lean_object* v___x_6272_; 
v___x_6272_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_6271_, v___y_6199_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_);
if (lean_obj_tag(v___x_6272_) == 0)
{
lean_dec_ref_known(v___x_6272_, 1);
v___y_6174_ = v_a_6207_;
v___y_6175_ = v___x_6228_;
v___y_6176_ = v___y_6199_;
v___y_6177_ = v___y_6200_;
v___y_6178_ = v___y_6201_;
v___y_6179_ = v___y_6202_;
v___y_6180_ = v___y_6203_;
v___y_6181_ = v___y_6204_;
v___y_6182_ = v___y_6205_;
goto v___jp_6173_;
}
else
{
lean_object* v_a_6273_; lean_object* v___x_6275_; uint8_t v_isShared_6276_; uint8_t v_isSharedCheck_6280_; 
lean_dec_ref_known(v___x_6228_, 5);
lean_dec(v_a_6207_);
lean_dec_ref(v_k_6163_);
v_a_6273_ = lean_ctor_get(v___x_6272_, 0);
v_isSharedCheck_6280_ = !lean_is_exclusive(v___x_6272_);
if (v_isSharedCheck_6280_ == 0)
{
v___x_6275_ = v___x_6272_;
v_isShared_6276_ = v_isSharedCheck_6280_;
goto v_resetjp_6274_;
}
else
{
lean_inc(v_a_6273_);
lean_dec(v___x_6272_);
v___x_6275_ = lean_box(0);
v_isShared_6276_ = v_isSharedCheck_6280_;
goto v_resetjp_6274_;
}
v_resetjp_6274_:
{
lean_object* v___x_6278_; 
if (v_isShared_6276_ == 0)
{
v___x_6278_ = v___x_6275_;
goto v_reusejp_6277_;
}
else
{
lean_object* v_reuseFailAlloc_6279_; 
v_reuseFailAlloc_6279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6279_, 0, v_a_6273_);
v___x_6278_ = v_reuseFailAlloc_6279_;
goto v_reusejp_6277_;
}
v_reusejp_6277_:
{
return v___x_6278_;
}
}
}
}
}
else
{
lean_object* v_a_6282_; lean_object* v___x_6284_; uint8_t v_isShared_6285_; uint8_t v_isSharedCheck_6289_; 
lean_del_object(v___x_6235_);
lean_dec_ref_known(v___x_6228_, 5);
lean_dec(v_a_6207_);
lean_dec_ref(v_k_6163_);
v_a_6282_ = lean_ctor_get(v___x_6267_, 0);
v_isSharedCheck_6289_ = !lean_is_exclusive(v___x_6267_);
if (v_isSharedCheck_6289_ == 0)
{
v___x_6284_ = v___x_6267_;
v_isShared_6285_ = v_isSharedCheck_6289_;
goto v_resetjp_6283_;
}
else
{
lean_inc(v_a_6282_);
lean_dec(v___x_6267_);
v___x_6284_ = lean_box(0);
v_isShared_6285_ = v_isSharedCheck_6289_;
goto v_resetjp_6283_;
}
v_resetjp_6283_:
{
lean_object* v___x_6287_; 
if (v_isShared_6285_ == 0)
{
v___x_6287_ = v___x_6284_;
goto v_reusejp_6286_;
}
else
{
lean_object* v_reuseFailAlloc_6288_; 
v_reuseFailAlloc_6288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6288_, 0, v_a_6282_);
v___x_6287_ = v_reuseFailAlloc_6288_;
goto v_reusejp_6286_;
}
v_reusejp_6286_:
{
return v___x_6287_;
}
}
}
}
}
else
{
lean_object* v_a_6292_; lean_object* v___x_6294_; uint8_t v_isShared_6295_; uint8_t v_isSharedCheck_6299_; 
lean_dec_ref_known(v___x_6228_, 5);
lean_dec(v_a_6207_);
lean_dec_ref(v_k_6163_);
v_a_6292_ = lean_ctor_get(v___x_6229_, 0);
v_isSharedCheck_6299_ = !lean_is_exclusive(v___x_6229_);
if (v_isSharedCheck_6299_ == 0)
{
v___x_6294_ = v___x_6229_;
v_isShared_6295_ = v_isSharedCheck_6299_;
goto v_resetjp_6293_;
}
else
{
lean_inc(v_a_6292_);
lean_dec(v___x_6229_);
v___x_6294_ = lean_box(0);
v_isShared_6295_ = v_isSharedCheck_6299_;
goto v_resetjp_6293_;
}
v_resetjp_6293_:
{
lean_object* v___x_6297_; 
if (v_isShared_6295_ == 0)
{
v___x_6297_ = v___x_6294_;
goto v_reusejp_6296_;
}
else
{
lean_object* v_reuseFailAlloc_6298_; 
v_reuseFailAlloc_6298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6298_, 0, v_a_6292_);
v___x_6297_ = v_reuseFailAlloc_6298_;
goto v_reusejp_6296_;
}
v_reusejp_6296_:
{
return v___x_6297_;
}
}
}
}
}
else
{
lean_object* v_a_6300_; lean_object* v___x_6302_; uint8_t v_isShared_6303_; uint8_t v_isSharedCheck_6307_; 
lean_dec_ref(v_k_6163_);
v_a_6300_ = lean_ctor_get(v___x_6206_, 0);
v_isSharedCheck_6307_ = !lean_is_exclusive(v___x_6206_);
if (v_isSharedCheck_6307_ == 0)
{
v___x_6302_ = v___x_6206_;
v_isShared_6303_ = v_isSharedCheck_6307_;
goto v_resetjp_6301_;
}
else
{
lean_inc(v_a_6300_);
lean_dec(v___x_6206_);
v___x_6302_ = lean_box(0);
v_isShared_6303_ = v_isSharedCheck_6307_;
goto v_resetjp_6301_;
}
v_resetjp_6301_:
{
lean_object* v___x_6305_; 
if (v_isShared_6303_ == 0)
{
v___x_6305_ = v___x_6302_;
goto v_reusejp_6304_;
}
else
{
lean_object* v_reuseFailAlloc_6306_; 
v_reuseFailAlloc_6306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6306_, 0, v_a_6300_);
v___x_6305_ = v_reuseFailAlloc_6306_;
goto v_reusejp_6304_;
}
v_reusejp_6304_:
{
return v___x_6305_;
}
}
}
}
v___jp_6308_:
{
uint8_t v___x_6310_; 
v___x_6310_ = 1;
if (v_only_6162_ == 0)
{
v___y_6195_ = v___y_6309_;
v___y_6196_ = v___x_6310_;
v_params_6197_ = v_params_6160_;
v___y_6198_ = v_a_6164_;
v___y_6199_ = v_a_6165_;
v___y_6200_ = v_a_6166_;
v___y_6201_ = v_a_6167_;
v___y_6202_ = v_a_6168_;
v___y_6203_ = v_a_6169_;
v___y_6204_ = v_a_6170_;
v___y_6205_ = v_a_6171_;
goto v___jp_6194_;
}
else
{
lean_object* v_config_6311_; lean_object* v_extensions_6312_; lean_object* v_extra_6313_; lean_object* v_extraInj_6314_; lean_object* v_extraFacts_6315_; lean_object* v_symPrios_6316_; lean_object* v_norm_6317_; lean_object* v_normProcs_6318_; lean_object* v___x_6320_; uint8_t v_isShared_6321_; uint8_t v_isSharedCheck_6329_; 
v_config_6311_ = lean_ctor_get(v_params_6160_, 0);
v_extensions_6312_ = lean_ctor_get(v_params_6160_, 1);
v_extra_6313_ = lean_ctor_get(v_params_6160_, 2);
v_extraInj_6314_ = lean_ctor_get(v_params_6160_, 3);
v_extraFacts_6315_ = lean_ctor_get(v_params_6160_, 4);
v_symPrios_6316_ = lean_ctor_get(v_params_6160_, 5);
v_norm_6317_ = lean_ctor_get(v_params_6160_, 6);
v_normProcs_6318_ = lean_ctor_get(v_params_6160_, 7);
v_isSharedCheck_6329_ = !lean_is_exclusive(v_params_6160_);
if (v_isSharedCheck_6329_ == 0)
{
lean_object* v_unused_6330_; 
v_unused_6330_ = lean_ctor_get(v_params_6160_, 8);
lean_dec(v_unused_6330_);
v___x_6320_ = v_params_6160_;
v_isShared_6321_ = v_isSharedCheck_6329_;
goto v_resetjp_6319_;
}
else
{
lean_inc(v_normProcs_6318_);
lean_inc(v_norm_6317_);
lean_inc(v_symPrios_6316_);
lean_inc(v_extraFacts_6315_);
lean_inc(v_extraInj_6314_);
lean_inc(v_extra_6313_);
lean_inc(v_extensions_6312_);
lean_inc(v_config_6311_);
lean_dec(v_params_6160_);
v___x_6320_ = lean_box(0);
v_isShared_6321_ = v_isSharedCheck_6329_;
goto v_resetjp_6319_;
}
v_resetjp_6319_:
{
size_t v_sz_6322_; size_t v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; lean_object* v_params_6327_; 
v_sz_6322_ = lean_array_size(v_extensions_6312_);
v___x_6323_ = ((size_t)0ULL);
v___x_6324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_6322_, v___x_6323_, v_extensions_6312_);
v___x_6325_ = lean_box(0);
if (v_isShared_6321_ == 0)
{
lean_ctor_set(v___x_6320_, 8, v___x_6325_);
lean_ctor_set(v___x_6320_, 1, v___x_6324_);
v_params_6327_ = v___x_6320_;
goto v_reusejp_6326_;
}
else
{
lean_object* v_reuseFailAlloc_6328_; 
v_reuseFailAlloc_6328_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6328_, 0, v_config_6311_);
lean_ctor_set(v_reuseFailAlloc_6328_, 1, v___x_6324_);
lean_ctor_set(v_reuseFailAlloc_6328_, 2, v_extra_6313_);
lean_ctor_set(v_reuseFailAlloc_6328_, 3, v_extraInj_6314_);
lean_ctor_set(v_reuseFailAlloc_6328_, 4, v_extraFacts_6315_);
lean_ctor_set(v_reuseFailAlloc_6328_, 5, v_symPrios_6316_);
lean_ctor_set(v_reuseFailAlloc_6328_, 6, v_norm_6317_);
lean_ctor_set(v_reuseFailAlloc_6328_, 7, v_normProcs_6318_);
lean_ctor_set(v_reuseFailAlloc_6328_, 8, v___x_6325_);
v_params_6327_ = v_reuseFailAlloc_6328_;
goto v_reusejp_6326_;
}
v_reusejp_6326_:
{
v___y_6195_ = v___y_6309_;
v___y_6196_ = v___x_6310_;
v_params_6197_ = v_params_6327_;
v___y_6198_ = v_a_6164_;
v___y_6199_ = v_a_6165_;
v___y_6200_ = v_a_6166_;
v___y_6201_ = v_a_6167_;
v___y_6202_ = v_a_6168_;
v___y_6203_ = v_a_6169_;
v___y_6204_ = v_a_6170_;
v___y_6205_ = v_a_6171_;
goto v___jp_6194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_6336_, lean_object* v_ps_6337_, lean_object* v_only_6338_, lean_object* v_k_6339_, lean_object* v_a_6340_, lean_object* v_a_6341_, lean_object* v_a_6342_, lean_object* v_a_6343_, lean_object* v_a_6344_, lean_object* v_a_6345_, lean_object* v_a_6346_, lean_object* v_a_6347_, lean_object* v_a_6348_){
_start:
{
uint8_t v_only_boxed_6349_; lean_object* v_res_6350_; 
v_only_boxed_6349_ = lean_unbox(v_only_6338_);
v_res_6350_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_6336_, v_ps_6337_, v_only_boxed_6349_, v_k_6339_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_, v_a_6345_, v_a_6346_, v_a_6347_);
lean_dec(v_a_6347_);
lean_dec_ref(v_a_6346_);
lean_dec(v_a_6345_);
lean_dec_ref(v_a_6344_);
lean_dec(v_a_6343_);
lean_dec_ref(v_a_6342_);
lean_dec(v_a_6341_);
lean_dec_ref(v_a_6340_);
lean_dec_ref(v_ps_6337_);
return v_res_6350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_6351_, lean_object* v_params_6352_, lean_object* v_ps_6353_, uint8_t v_only_6354_, lean_object* v_k_6355_, lean_object* v_a_6356_, lean_object* v_a_6357_, lean_object* v_a_6358_, lean_object* v_a_6359_, lean_object* v_a_6360_, lean_object* v_a_6361_, lean_object* v_a_6362_, lean_object* v_a_6363_){
_start:
{
lean_object* v___x_6365_; 
v___x_6365_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_6352_, v_ps_6353_, v_only_6354_, v_k_6355_, v_a_6356_, v_a_6357_, v_a_6358_, v_a_6359_, v_a_6360_, v_a_6361_, v_a_6362_, v_a_6363_);
return v___x_6365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_6366_, lean_object* v_params_6367_, lean_object* v_ps_6368_, lean_object* v_only_6369_, lean_object* v_k_6370_, lean_object* v_a_6371_, lean_object* v_a_6372_, lean_object* v_a_6373_, lean_object* v_a_6374_, lean_object* v_a_6375_, lean_object* v_a_6376_, lean_object* v_a_6377_, lean_object* v_a_6378_, lean_object* v_a_6379_){
_start:
{
uint8_t v_only_boxed_6380_; lean_object* v_res_6381_; 
v_only_boxed_6380_ = lean_unbox(v_only_6369_);
v_res_6381_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_6366_, v_params_6367_, v_ps_6368_, v_only_boxed_6380_, v_k_6370_, v_a_6371_, v_a_6372_, v_a_6373_, v_a_6374_, v_a_6375_, v_a_6376_, v_a_6377_, v_a_6378_);
lean_dec(v_a_6378_);
lean_dec_ref(v_a_6377_);
lean_dec(v_a_6376_);
lean_dec_ref(v_a_6375_);
lean_dec(v_a_6374_);
lean_dec_ref(v_a_6373_);
lean_dec(v_a_6372_);
lean_dec_ref(v_a_6371_);
lean_dec_ref(v_ps_6368_);
return v_res_6381_;
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
