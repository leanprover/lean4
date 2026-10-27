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
lean_object* l_Lean_Elab_Term_checkDeprecatedCore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SymbolPriorities_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_List_lengthTR___redArg(lean_object*);
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
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_config_4_; lean_object* v_identity_5_; lean_object* v_extensions_6_; lean_object* v_extra_7_; lean_object* v_extraInj_8_; lean_object* v_extraFacts_9_; lean_object* v_symPrios_10_; lean_object* v_norm_11_; lean_object* v_normProcs_12_; lean_object* v_anchorRefs_x3f_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v_config_4_ = lean_ctor_get(v_params_1_, 0);
v_identity_5_ = lean_ctor_get(v_params_1_, 1);
v_extensions_6_ = lean_ctor_get(v_params_1_, 2);
v_extra_7_ = lean_ctor_get(v_params_1_, 3);
v_extraInj_8_ = lean_ctor_get(v_params_1_, 4);
v_extraFacts_9_ = lean_ctor_get(v_params_1_, 5);
v_symPrios_10_ = lean_ctor_get(v_params_1_, 6);
v_norm_11_ = lean_ctor_get(v_params_1_, 7);
v_normProcs_12_ = lean_ctor_get(v_params_1_, 8);
v_anchorRefs_x3f_13_ = lean_ctor_get(v_params_1_, 9);
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_array_get_size(v_extensions_6_);
v___x_16_ = lean_nat_dec_lt(v___x_14_, v___x_15_);
if (v___x_16_ == 0)
{
lean_dec(v_declName_2_);
return v_params_1_;
}
else
{
lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_40_; 
lean_inc(v_anchorRefs_x3f_13_);
lean_inc_ref(v_normProcs_12_);
lean_inc_ref(v_norm_11_);
lean_inc_ref(v_symPrios_10_);
lean_inc_ref(v_extraFacts_9_);
lean_inc_ref(v_extraInj_8_);
lean_inc_ref(v_extra_7_);
lean_inc_ref(v_extensions_6_);
lean_inc(v_identity_5_);
lean_inc_ref(v_config_4_);
v_isSharedCheck_40_ = !lean_is_exclusive(v_params_1_);
if (v_isSharedCheck_40_ == 0)
{
lean_object* v_unused_41_; lean_object* v_unused_42_; lean_object* v_unused_43_; lean_object* v_unused_44_; lean_object* v_unused_45_; lean_object* v_unused_46_; lean_object* v_unused_47_; lean_object* v_unused_48_; lean_object* v_unused_49_; lean_object* v_unused_50_; 
v_unused_41_ = lean_ctor_get(v_params_1_, 9);
lean_dec(v_unused_41_);
v_unused_42_ = lean_ctor_get(v_params_1_, 8);
lean_dec(v_unused_42_);
v_unused_43_ = lean_ctor_get(v_params_1_, 7);
lean_dec(v_unused_43_);
v_unused_44_ = lean_ctor_get(v_params_1_, 6);
lean_dec(v_unused_44_);
v_unused_45_ = lean_ctor_get(v_params_1_, 5);
lean_dec(v_unused_45_);
v_unused_46_ = lean_ctor_get(v_params_1_, 4);
lean_dec(v_unused_46_);
v_unused_47_ = lean_ctor_get(v_params_1_, 3);
lean_dec(v_unused_47_);
v_unused_48_ = lean_ctor_get(v_params_1_, 2);
lean_dec(v_unused_48_);
v_unused_49_ = lean_ctor_get(v_params_1_, 1);
lean_dec(v_unused_49_);
v_unused_50_ = lean_ctor_get(v_params_1_, 0);
lean_dec(v_unused_50_);
v___x_18_ = v_params_1_;
v_isShared_19_ = v_isSharedCheck_40_;
goto v_resetjp_17_;
}
else
{
lean_dec(v_params_1_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_40_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v_v_20_; lean_object* v_casesTypes_21_; lean_object* v_extThms_22_; lean_object* v_funCC_23_; lean_object* v_ematch_24_; lean_object* v_inj_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_39_; 
v_v_20_ = lean_array_fget(v_extensions_6_, v___x_14_);
v_casesTypes_21_ = lean_ctor_get(v_v_20_, 0);
v_extThms_22_ = lean_ctor_get(v_v_20_, 1);
v_funCC_23_ = lean_ctor_get(v_v_20_, 2);
v_ematch_24_ = lean_ctor_get(v_v_20_, 3);
v_inj_25_ = lean_ctor_get(v_v_20_, 4);
v_isSharedCheck_39_ = !lean_is_exclusive(v_v_20_);
if (v_isSharedCheck_39_ == 0)
{
v___x_27_ = v_v_20_;
v_isShared_28_ = v_isSharedCheck_39_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_inj_25_);
lean_inc(v_ematch_24_);
lean_inc(v_funCC_23_);
lean_inc(v_extThms_22_);
lean_inc(v_casesTypes_21_);
lean_dec(v_v_20_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_39_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_29_; lean_object* v_xs_x27_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_29_ = lean_box(0);
v_xs_x27_30_ = lean_array_fset(v_extensions_6_, v___x_14_, v___x_29_);
v___x_31_ = l_Lean_Meta_Grind_CasesTypes_insert(v_casesTypes_21_, v_declName_2_, v_eager_3_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_31_);
v___x_33_ = v___x_27_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_extThms_22_);
lean_ctor_set(v_reuseFailAlloc_38_, 2, v_funCC_23_);
lean_ctor_set(v_reuseFailAlloc_38_, 3, v_ematch_24_);
lean_ctor_set(v_reuseFailAlloc_38_, 4, v_inj_25_);
v___x_33_ = v_reuseFailAlloc_38_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_34_ = lean_array_fset(v_xs_x27_30_, v___x_14_, v___x_33_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 2, v___x_34_);
v___x_36_ = v___x_18_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_config_4_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_identity_5_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_37_, 3, v_extra_7_);
lean_ctor_set(v_reuseFailAlloc_37_, 4, v_extraInj_8_);
lean_ctor_set(v_reuseFailAlloc_37_, 5, v_extraFacts_9_);
lean_ctor_set(v_reuseFailAlloc_37_, 6, v_symPrios_10_);
lean_ctor_set(v_reuseFailAlloc_37_, 7, v_norm_11_);
lean_ctor_set(v_reuseFailAlloc_37_, 8, v_normProcs_12_);
lean_ctor_set(v_reuseFailAlloc_37_, 9, v_anchorRefs_x3f_13_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes___boxed(lean_object* v_params_51_, lean_object* v_declName_52_, lean_object* v_eager_53_){
_start:
{
uint8_t v_eager_boxed_54_; lean_object* v_res_55_; 
v_eager_boxed_54_ = lean_unbox(v_eager_53_);
v_res_55_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_51_, v_declName_52_, v_eager_boxed_54_);
return v_res_55_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(lean_object* v_declName_56_, lean_object* v_as_57_, size_t v_i_58_, size_t v_stop_59_){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = lean_usize_dec_eq(v_i_58_, v_stop_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v_casesTypes_62_; uint8_t v___x_63_; 
v___x_61_ = lean_array_uget_borrowed(v_as_57_, v_i_58_);
v_casesTypes_62_ = lean_ctor_get(v___x_61_, 0);
v___x_63_ = l_Lean_Meta_Grind_CasesTypes_contains(v_casesTypes_62_, v_declName_56_);
if (v___x_63_ == 0)
{
size_t v___x_64_; size_t v___x_65_; 
v___x_64_ = ((size_t)1ULL);
v___x_65_ = lean_usize_add(v_i_58_, v___x_64_);
v_i_58_ = v___x_65_;
goto _start;
}
else
{
return v___x_63_;
}
}
else
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(lean_object* v_params_76_, lean_object* v_declName_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___y_82_; lean_object* v___y_83_; lean_object* v___y_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v___y_89_; lean_object* v___y_90_; lean_object* v___y_91_; lean_object* v_config_94_; lean_object* v_identity_95_; lean_object* v_extensions_96_; lean_object* v_extra_97_; lean_object* v_extraInj_98_; lean_object* v_extraFacts_99_; lean_object* v_symPrios_100_; lean_object* v_norm_101_; lean_object* v_normProcs_102_; lean_object* v_anchorRefs_x3f_103_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_config_94_ = lean_ctor_get(v_params_76_, 0);
lean_inc_ref(v_config_94_);
v_identity_95_ = lean_ctor_get(v_params_76_, 1);
lean_inc(v_identity_95_);
v_extensions_96_ = lean_ctor_get(v_params_76_, 2);
lean_inc_ref(v_extensions_96_);
v_extra_97_ = lean_ctor_get(v_params_76_, 3);
lean_inc_ref(v_extra_97_);
v_extraInj_98_ = lean_ctor_get(v_params_76_, 4);
lean_inc_ref(v_extraInj_98_);
v_extraFacts_99_ = lean_ctor_get(v_params_76_, 5);
lean_inc_ref(v_extraFacts_99_);
v_symPrios_100_ = lean_ctor_get(v_params_76_, 6);
lean_inc_ref(v_symPrios_100_);
v_norm_101_ = lean_ctor_get(v_params_76_, 7);
lean_inc_ref(v_norm_101_);
v_normProcs_102_ = lean_ctor_get(v_params_76_, 8);
lean_inc_ref(v_normProcs_102_);
v_anchorRefs_x3f_103_ = lean_ctor_get(v_params_76_, 9);
lean_inc(v_anchorRefs_x3f_103_);
lean_dec_ref(v_params_76_);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_array_get_size(v_extensions_96_);
v___x_137_ = lean_nat_dec_lt(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
goto v___jp_125_;
}
else
{
if (v___x_137_ == 0)
{
goto v___jp_125_;
}
else
{
size_t v___x_138_; size_t v___x_139_; uint8_t v___x_140_; 
v___x_138_ = ((size_t)0ULL);
v___x_139_ = lean_usize_of_nat(v___x_136_);
v___x_140_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(v_declName_77_, v_extensions_96_, v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
goto v___jp_125_;
}
else
{
goto v___jp_104_;
}
}
}
v___jp_81_:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_92_, 0, v___y_90_);
lean_ctor_set(v___x_92_, 1, v___y_89_);
lean_ctor_set(v___x_92_, 2, v___y_91_);
lean_ctor_set(v___x_92_, 3, v___y_84_);
lean_ctor_set(v___x_92_, 4, v___y_86_);
lean_ctor_set(v___x_92_, 5, v___y_83_);
lean_ctor_set(v___x_92_, 6, v___y_85_);
lean_ctor_set(v___x_92_, 7, v___y_82_);
lean_ctor_set(v___x_92_, 8, v___y_87_);
lean_ctor_set(v___x_92_, 9, v___y_88_);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
v___jp_104_:
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_array_get_size(v_extensions_96_);
v___x_107_ = lean_nat_dec_lt(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
lean_dec(v_declName_77_);
v___y_82_ = v_norm_101_;
v___y_83_ = v_extraFacts_99_;
v___y_84_ = v_extra_97_;
v___y_85_ = v_symPrios_100_;
v___y_86_ = v_extraInj_98_;
v___y_87_ = v_normProcs_102_;
v___y_88_ = v_anchorRefs_x3f_103_;
v___y_89_ = v_identity_95_;
v___y_90_ = v_config_94_;
v___y_91_ = v_extensions_96_;
goto v___jp_81_;
}
else
{
lean_object* v_v_108_; lean_object* v_casesTypes_109_; lean_object* v_extThms_110_; lean_object* v_funCC_111_; lean_object* v_ematch_112_; lean_object* v_inj_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_124_; 
v_v_108_ = lean_array_fget(v_extensions_96_, v___x_105_);
v_casesTypes_109_ = lean_ctor_get(v_v_108_, 0);
v_extThms_110_ = lean_ctor_get(v_v_108_, 1);
v_funCC_111_ = lean_ctor_get(v_v_108_, 2);
v_ematch_112_ = lean_ctor_get(v_v_108_, 3);
v_inj_113_ = lean_ctor_get(v_v_108_, 4);
v_isSharedCheck_124_ = !lean_is_exclusive(v_v_108_);
if (v_isSharedCheck_124_ == 0)
{
v___x_115_ = v_v_108_;
v_isShared_116_ = v_isSharedCheck_124_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_inj_113_);
lean_inc(v_ematch_112_);
lean_inc(v_funCC_111_);
lean_inc(v_extThms_110_);
lean_inc(v_casesTypes_109_);
lean_dec(v_v_108_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_124_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v_xs_x27_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_117_ = lean_box(0);
v_xs_x27_118_ = lean_array_fset(v_extensions_96_, v___x_105_, v___x_117_);
v___x_119_ = l_Lean_Meta_Grind_CasesTypes_erase(v_casesTypes_109_, v_declName_77_);
lean_dec(v_declName_77_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v___x_119_);
v___x_121_ = v___x_115_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_extThms_110_);
lean_ctor_set(v_reuseFailAlloc_123_, 2, v_funCC_111_);
lean_ctor_set(v_reuseFailAlloc_123_, 3, v_ematch_112_);
lean_ctor_set(v_reuseFailAlloc_123_, 4, v_inj_113_);
v___x_121_ = v_reuseFailAlloc_123_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_122_; 
v___x_122_ = lean_array_fset(v_xs_x27_118_, v___x_105_, v___x_121_);
v___y_82_ = v_norm_101_;
v___y_83_ = v_extraFacts_99_;
v___y_84_ = v_extra_97_;
v___y_85_ = v_symPrios_100_;
v___y_86_ = v_extraInj_98_;
v___y_87_ = v_normProcs_102_;
v___y_88_ = v_anchorRefs_x3f_103_;
v___y_89_ = v_identity_95_;
v___y_90_ = v_config_94_;
v___y_91_ = v___x_122_;
goto v___jp_81_;
}
}
}
}
v___jp_125_:
{
lean_object* v___x_126_; 
lean_inc(v_declName_77_);
v___x_126_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_77_, v_a_78_, v_a_79_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_dec_ref_known(v___x_126_, 1);
goto v___jp_104_;
}
else
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
lean_dec(v_anchorRefs_x3f_103_);
lean_dec_ref(v_normProcs_102_);
lean_dec_ref(v_norm_101_);
lean_dec_ref(v_symPrios_100_);
lean_dec_ref(v_extraFacts_99_);
lean_dec_ref(v_extraInj_98_);
lean_dec_ref(v_extra_97_);
lean_dec_ref(v_extensions_96_);
lean_dec(v_identity_95_);
lean_dec_ref(v_config_94_);
lean_dec(v_declName_77_);
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes___boxed(lean_object* v_params_141_, lean_object* v_declName_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_params_141_, v_declName_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(lean_object* v_params_147_, lean_object* v_declName_148_){
_start:
{
lean_object* v_config_149_; lean_object* v_identity_150_; lean_object* v_extensions_151_; lean_object* v_extra_152_; lean_object* v_extraInj_153_; lean_object* v_extraFacts_154_; lean_object* v_symPrios_155_; lean_object* v_norm_156_; lean_object* v_normProcs_157_; lean_object* v_anchorRefs_x3f_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v_config_149_ = lean_ctor_get(v_params_147_, 0);
v_identity_150_ = lean_ctor_get(v_params_147_, 1);
v_extensions_151_ = lean_ctor_get(v_params_147_, 2);
v_extra_152_ = lean_ctor_get(v_params_147_, 3);
v_extraInj_153_ = lean_ctor_get(v_params_147_, 4);
v_extraFacts_154_ = lean_ctor_get(v_params_147_, 5);
v_symPrios_155_ = lean_ctor_get(v_params_147_, 6);
v_norm_156_ = lean_ctor_get(v_params_147_, 7);
v_normProcs_157_ = lean_ctor_get(v_params_147_, 8);
v_anchorRefs_x3f_158_ = lean_ctor_get(v_params_147_, 9);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_array_get_size(v_extensions_151_);
v___x_161_ = lean_nat_dec_lt(v___x_159_, v___x_160_);
if (v___x_161_ == 0)
{
lean_dec(v_declName_148_);
return v_params_147_;
}
else
{
lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_185_; 
lean_inc(v_anchorRefs_x3f_158_);
lean_inc_ref(v_normProcs_157_);
lean_inc_ref(v_norm_156_);
lean_inc_ref(v_symPrios_155_);
lean_inc_ref(v_extraFacts_154_);
lean_inc_ref(v_extraInj_153_);
lean_inc_ref(v_extra_152_);
lean_inc_ref(v_extensions_151_);
lean_inc(v_identity_150_);
lean_inc_ref(v_config_149_);
v_isSharedCheck_185_ = !lean_is_exclusive(v_params_147_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; lean_object* v_unused_187_; lean_object* v_unused_188_; lean_object* v_unused_189_; lean_object* v_unused_190_; lean_object* v_unused_191_; lean_object* v_unused_192_; lean_object* v_unused_193_; lean_object* v_unused_194_; lean_object* v_unused_195_; 
v_unused_186_ = lean_ctor_get(v_params_147_, 9);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_params_147_, 8);
lean_dec(v_unused_187_);
v_unused_188_ = lean_ctor_get(v_params_147_, 7);
lean_dec(v_unused_188_);
v_unused_189_ = lean_ctor_get(v_params_147_, 6);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_params_147_, 5);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_params_147_, 4);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_params_147_, 3);
lean_dec(v_unused_192_);
v_unused_193_ = lean_ctor_get(v_params_147_, 2);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_params_147_, 1);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v_params_147_, 0);
lean_dec(v_unused_195_);
v___x_163_ = v_params_147_;
v_isShared_164_ = v_isSharedCheck_185_;
goto v_resetjp_162_;
}
else
{
lean_dec(v_params_147_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_185_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_v_165_; lean_object* v_casesTypes_166_; lean_object* v_extThms_167_; lean_object* v_funCC_168_; lean_object* v_ematch_169_; lean_object* v_inj_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_184_; 
v_v_165_ = lean_array_fget(v_extensions_151_, v___x_159_);
v_casesTypes_166_ = lean_ctor_get(v_v_165_, 0);
v_extThms_167_ = lean_ctor_get(v_v_165_, 1);
v_funCC_168_ = lean_ctor_get(v_v_165_, 2);
v_ematch_169_ = lean_ctor_get(v_v_165_, 3);
v_inj_170_ = lean_ctor_get(v_v_165_, 4);
v_isSharedCheck_184_ = !lean_is_exclusive(v_v_165_);
if (v_isSharedCheck_184_ == 0)
{
v___x_172_ = v_v_165_;
v_isShared_173_ = v_isSharedCheck_184_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_inj_170_);
lean_inc(v_ematch_169_);
lean_inc(v_funCC_168_);
lean_inc(v_extThms_167_);
lean_inc(v_casesTypes_166_);
lean_dec(v_v_165_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_184_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v_xs_x27_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_174_ = lean_box(0);
v_xs_x27_175_ = lean_array_fset(v_extensions_151_, v___x_159_, v___x_174_);
v___x_176_ = l_Lean_NameSet_insert(v_funCC_168_, v_declName_148_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 2, v___x_176_);
v___x_178_ = v___x_172_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_casesTypes_166_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_extThms_167_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_183_, 3, v_ematch_169_);
lean_ctor_set(v_reuseFailAlloc_183_, 4, v_inj_170_);
v___x_178_ = v_reuseFailAlloc_183_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_array_fset(v_xs_x27_175_, v___x_159_, v___x_178_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 2, v___x_179_);
v___x_181_ = v___x_163_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_config_149_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_identity_150_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_182_, 3, v_extra_152_);
lean_ctor_set(v_reuseFailAlloc_182_, 4, v_extraInj_153_);
lean_ctor_set(v_reuseFailAlloc_182_, 5, v_extraFacts_154_);
lean_ctor_set(v_reuseFailAlloc_182_, 6, v_symPrios_155_);
lean_ctor_set(v_reuseFailAlloc_182_, 7, v_norm_156_);
lean_ctor_set(v_reuseFailAlloc_182_, 8, v_normProcs_157_);
lean_ctor_set(v_reuseFailAlloc_182_, 9, v_anchorRefs_x3f_158_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(lean_object* v_declName_196_, lean_object* v_as_197_, size_t v_i_198_, size_t v_stop_199_){
_start:
{
uint8_t v___x_200_; 
v___x_200_ = lean_usize_dec_eq(v_i_198_, v_stop_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v_ematch_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_201_ = lean_array_uget_borrowed(v_as_197_, v_i_198_);
v_ematch_202_ = lean_ctor_get(v___x_201_, 3);
lean_inc(v_declName_196_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v_declName_196_);
v___x_204_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_ematch_202_, v___x_203_);
lean_dec_ref_known(v___x_203_, 1);
if (v___x_204_ == 0)
{
size_t v___x_205_; size_t v___x_206_; 
v___x_205_ = ((size_t)1ULL);
v___x_206_ = lean_usize_add(v_i_198_, v___x_205_);
v_i_198_ = v___x_206_;
goto _start;
}
else
{
lean_dec(v_declName_196_);
return v___x_204_;
}
}
else
{
uint8_t v___x_208_; 
lean_dec(v_declName_196_);
v___x_208_ = 0;
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0___boxed(lean_object* v_declName_209_, lean_object* v_as_210_, lean_object* v_i_211_, lean_object* v_stop_212_){
_start:
{
size_t v_i_boxed_213_; size_t v_stop_boxed_214_; uint8_t v_res_215_; lean_object* v_r_216_; 
v_i_boxed_213_ = lean_unbox_usize(v_i_211_);
lean_dec(v_i_211_);
v_stop_boxed_214_ = lean_unbox_usize(v_stop_212_);
lean_dec(v_stop_212_);
v_res_215_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(v_declName_209_, v_as_210_, v_i_boxed_213_, v_stop_boxed_214_);
lean_dec_ref(v_as_210_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(lean_object* v_params_217_, lean_object* v_declName_218_){
_start:
{
lean_object* v_extensions_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v_extensions_219_ = lean_ctor_get(v_params_217_, 2);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_array_get_size(v_extensions_219_);
v___x_222_ = lean_nat_dec_lt(v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_dec(v_declName_218_);
return v___x_222_;
}
else
{
if (v___x_222_ == 0)
{
lean_dec(v_declName_218_);
return v___x_222_;
}
else
{
size_t v___x_223_; size_t v___x_224_; uint8_t v___x_225_; 
v___x_223_ = ((size_t)0ULL);
v___x_224_ = lean_usize_of_nat(v___x_221_);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(v_declName_218_, v_extensions_219_, v___x_223_, v___x_224_);
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch___boxed(lean_object* v_params_226_, lean_object* v_declName_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_226_, v_declName_227_);
lean_dec_ref(v_params_226_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(lean_object* v_declName_230_, lean_object* v_as_231_, size_t v_i_232_, size_t v_stop_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = lean_usize_dec_eq(v_i_232_, v_stop_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v_inj_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_235_ = lean_array_uget_borrowed(v_as_231_, v_i_232_);
v_inj_236_ = lean_ctor_get(v___x_235_, 4);
lean_inc(v_declName_230_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v_declName_230_);
v___x_238_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_236_, v___x_237_);
lean_dec_ref_known(v___x_237_, 1);
if (v___x_238_ == 0)
{
size_t v___x_239_; size_t v___x_240_; 
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_add(v_i_232_, v___x_239_);
v_i_232_ = v___x_240_;
goto _start;
}
else
{
lean_dec(v_declName_230_);
return v___x_238_;
}
}
else
{
uint8_t v___x_242_; 
lean_dec(v_declName_230_);
v___x_242_ = 0;
return v___x_242_;
}
}
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(lean_object* v_params_251_, lean_object* v_declName_252_){
_start:
{
lean_object* v_extensions_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_extensions_253_ = lean_ctor_get(v_params_251_, 2);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem___boxed(lean_object* v_params_260_, lean_object* v_declName_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_params_260_, v_declName_261_);
lean_dec_ref(v_params_260_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(lean_object* v_params_264_, lean_object* v_declName_265_){
_start:
{
lean_object* v_config_266_; lean_object* v_identity_267_; lean_object* v_extensions_268_; lean_object* v_extra_269_; lean_object* v_extraInj_270_; lean_object* v_extraFacts_271_; lean_object* v_symPrios_272_; lean_object* v_norm_273_; lean_object* v_normProcs_274_; lean_object* v_anchorRefs_x3f_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_config_266_ = lean_ctor_get(v_params_264_, 0);
v_identity_267_ = lean_ctor_get(v_params_264_, 1);
v_extensions_268_ = lean_ctor_get(v_params_264_, 2);
v_extra_269_ = lean_ctor_get(v_params_264_, 3);
v_extraInj_270_ = lean_ctor_get(v_params_264_, 4);
v_extraFacts_271_ = lean_ctor_get(v_params_264_, 5);
v_symPrios_272_ = lean_ctor_get(v_params_264_, 6);
v_norm_273_ = lean_ctor_get(v_params_264_, 7);
v_normProcs_274_ = lean_ctor_get(v_params_264_, 8);
v_anchorRefs_x3f_275_ = lean_ctor_get(v_params_264_, 9);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_array_get_size(v_extensions_268_);
v___x_278_ = lean_nat_dec_lt(v___x_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_dec(v_declName_265_);
return v_params_264_;
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
lean_inc(v_identity_267_);
lean_inc_ref(v_config_266_);
v_isSharedCheck_303_ = !lean_is_exclusive(v_params_264_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; lean_object* v_unused_305_; lean_object* v_unused_306_; lean_object* v_unused_307_; lean_object* v_unused_308_; lean_object* v_unused_309_; lean_object* v_unused_310_; lean_object* v_unused_311_; lean_object* v_unused_312_; lean_object* v_unused_313_; 
v_unused_304_ = lean_ctor_get(v_params_264_, 9);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_params_264_, 8);
lean_dec(v_unused_305_);
v_unused_306_ = lean_ctor_get(v_params_264_, 7);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_params_264_, 6);
lean_dec(v_unused_307_);
v_unused_308_ = lean_ctor_get(v_params_264_, 5);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_params_264_, 4);
lean_dec(v_unused_309_);
v_unused_310_ = lean_ctor_get(v_params_264_, 3);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v_params_264_, 2);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_params_264_, 1);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_params_264_, 0);
lean_dec(v_unused_313_);
v___x_280_ = v_params_264_;
v_isShared_281_ = v_isSharedCheck_303_;
goto v_resetjp_279_;
}
else
{
lean_dec(v_params_264_);
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
lean_ctor_set(v___x_293_, 0, v_declName_265_);
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
lean_ctor_set(v___x_280_, 2, v___x_297_);
v___x_299_ = v___x_280_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_config_266_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_identity_267_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_300_, 3, v_extra_269_);
lean_ctor_set(v_reuseFailAlloc_300_, 4, v_extraInj_270_);
lean_ctor_set(v_reuseFailAlloc_300_, 5, v_extraFacts_271_);
lean_ctor_set(v_reuseFailAlloc_300_, 6, v_symPrios_272_);
lean_ctor_set(v_reuseFailAlloc_300_, 7, v_norm_273_);
lean_ctor_set(v_reuseFailAlloc_300_, 8, v_normProcs_274_);
lean_ctor_set(v_reuseFailAlloc_300_, 9, v_anchorRefs_x3f_275_);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(lean_object* v_params_314_, uint8_t v___x_315_, lean_object* v_as_316_, size_t v_i_317_, size_t v_stop_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = lean_usize_dec_eq(v_i_317_, v_stop_318_);
if (v___x_319_ == 0)
{
uint8_t v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_320_ = 1;
v___x_321_ = lean_array_uget_borrowed(v_as_316_, v_i_317_);
lean_inc(v___x_321_);
v___x_322_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_314_, v___x_321_);
if (v___x_322_ == 0)
{
return v___x_320_;
}
else
{
if (v___x_315_ == 0)
{
size_t v___x_323_; size_t v___x_324_; 
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_add(v_i_317_, v___x_323_);
v_i_317_ = v___x_324_;
goto _start;
}
else
{
return v___x_320_;
}
}
}
else
{
uint8_t v___x_326_; 
v___x_326_ = 0;
return v___x_326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1___boxed(lean_object* v_params_327_, lean_object* v___x_328_, lean_object* v_as_329_, lean_object* v_i_330_, lean_object* v_stop_331_){
_start:
{
uint8_t v___x_1649__boxed_332_; size_t v_i_boxed_333_; size_t v_stop_boxed_334_; uint8_t v_res_335_; lean_object* v_r_336_; 
v___x_1649__boxed_332_ = lean_unbox(v___x_328_);
v_i_boxed_333_ = lean_unbox_usize(v_i_330_);
lean_dec(v_i_330_);
v_stop_boxed_334_ = lean_unbox_usize(v_stop_331_);
lean_dec(v_stop_331_);
v_res_335_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_327_, v___x_1649__boxed_332_, v_as_329_, v_i_boxed_333_, v_stop_boxed_334_);
lean_dec_ref(v_as_329_);
lean_dec_ref(v_params_327_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(lean_object* v_as_337_, size_t v_i_338_, size_t v_stop_339_, lean_object* v_b_340_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0___boxed(lean_object* v_as_347_, lean_object* v_i_348_, lean_object* v_stop_349_, lean_object* v_b_350_){
_start:
{
size_t v_i_boxed_351_; size_t v_stop_boxed_352_; lean_object* v_res_353_; 
v_i_boxed_351_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_stop_boxed_352_ = lean_unbox_usize(v_stop_349_);
lean_dec(v_stop_349_);
v_res_353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_as_347_, v_i_boxed_351_, v_stop_boxed_352_, v_b_350_);
lean_dec_ref(v_as_347_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(lean_object* v_params_354_, lean_object* v_declName_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_364_; lean_object* v_env_365_; uint8_t v___x_366_; 
v___x_364_ = lean_st_ref_get(v_a_359_);
v_env_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_ref(v_env_365_);
lean_dec(v___x_364_);
lean_inc(v_declName_355_);
v___x_366_ = l_Lean_wasOriginallyTheorem(v_env_365_, v_declName_355_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
lean_inc(v_declName_355_);
v___x_367_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_402_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_402_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_402_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_402_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
if (lean_obj_tag(v_a_368_) == 1)
{
lean_object* v_val_372_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_val_372_ = lean_ctor_get(v_a_368_, 0);
lean_inc(v_val_372_);
lean_dec_ref_known(v_a_368_, 1);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_array_get_size(v_val_372_);
v___x_388_ = lean_nat_dec_lt(v___x_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_dec(v_declName_355_);
goto v___jp_373_;
}
else
{
if (v___x_388_ == 0)
{
lean_dec(v_declName_355_);
goto v___jp_373_;
}
else
{
size_t v___x_389_; size_t v___x_390_; uint8_t v___x_391_; 
v___x_389_ = ((size_t)0ULL);
v___x_390_ = lean_usize_of_nat(v___x_387_);
v___x_391_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_354_, v___x_366_, v_val_372_, v___x_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_dec(v_declName_355_);
goto v___jp_373_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_355_, v_a_358_, v_a_359_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_dec_ref_known(v___x_392_, 1);
goto v___jp_373_;
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_val_372_);
lean_del_object(v___x_370_);
lean_dec_ref(v_params_354_);
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
v___jp_373_:
{
lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_array_get_size(v_val_372_);
v___x_376_ = lean_nat_dec_lt(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_378_; 
lean_dec(v_val_372_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v_params_354_);
v___x_378_ = v___x_370_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_params_354_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
else
{
size_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_380_ = ((size_t)0ULL);
v___x_381_ = lean_usize_of_nat(v___x_375_);
v___x_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_val_372_, v___x_380_, v___x_381_, v_params_354_);
lean_dec(v_val_372_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_382_);
v___x_384_ = v___x_370_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v___x_401_; 
lean_del_object(v___x_370_);
lean_dec(v_a_368_);
lean_dec_ref(v_params_354_);
v___x_401_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_355_, v_a_358_, v_a_359_);
return v___x_401_;
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec(v_declName_355_);
lean_dec_ref(v_params_354_);
v_a_403_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_367_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_367_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
else
{
uint8_t v___x_411_; 
lean_inc(v_declName_355_);
v___x_411_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_354_, v_declName_355_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_inc(v_declName_355_);
v___x_412_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_355_, v_a_358_, v_a_359_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_dec_ref_known(v___x_412_, 1);
goto v___jp_361_;
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_declName_355_);
lean_dec_ref(v_params_354_);
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
goto v___jp_361_;
}
}
v___jp_361_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(v_params_354_, v_declName_355_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch___boxed(lean_object* v_params_421_, lean_object* v_declName_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_params_421_, v_declName_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(lean_object* v_params_429_, lean_object* v_declName_430_){
_start:
{
lean_object* v_config_431_; lean_object* v_identity_432_; lean_object* v_extensions_433_; lean_object* v_extra_434_; lean_object* v_extraInj_435_; lean_object* v_extraFacts_436_; lean_object* v_symPrios_437_; lean_object* v_norm_438_; lean_object* v_normProcs_439_; lean_object* v_anchorRefs_x3f_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v_config_431_ = lean_ctor_get(v_params_429_, 0);
v_identity_432_ = lean_ctor_get(v_params_429_, 1);
v_extensions_433_ = lean_ctor_get(v_params_429_, 2);
v_extra_434_ = lean_ctor_get(v_params_429_, 3);
v_extraInj_435_ = lean_ctor_get(v_params_429_, 4);
v_extraFacts_436_ = lean_ctor_get(v_params_429_, 5);
v_symPrios_437_ = lean_ctor_get(v_params_429_, 6);
v_norm_438_ = lean_ctor_get(v_params_429_, 7);
v_normProcs_439_ = lean_ctor_get(v_params_429_, 8);
v_anchorRefs_x3f_440_ = lean_ctor_get(v_params_429_, 9);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_array_get_size(v_extensions_433_);
v___x_443_ = lean_nat_dec_lt(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
lean_dec(v_declName_430_);
return v_params_429_;
}
else
{
lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_468_; 
lean_inc(v_anchorRefs_x3f_440_);
lean_inc_ref(v_normProcs_439_);
lean_inc_ref(v_norm_438_);
lean_inc_ref(v_symPrios_437_);
lean_inc_ref(v_extraFacts_436_);
lean_inc_ref(v_extraInj_435_);
lean_inc_ref(v_extra_434_);
lean_inc_ref(v_extensions_433_);
lean_inc(v_identity_432_);
lean_inc_ref(v_config_431_);
v_isSharedCheck_468_ = !lean_is_exclusive(v_params_429_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_469_ = lean_ctor_get(v_params_429_, 9);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_params_429_, 8);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_params_429_, 7);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_params_429_, 6);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_params_429_, 5);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_params_429_, 4);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_params_429_, 3);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_params_429_, 2);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_params_429_, 1);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_params_429_, 0);
lean_dec(v_unused_478_);
v___x_445_ = v_params_429_;
v_isShared_446_ = v_isSharedCheck_468_;
goto v_resetjp_444_;
}
else
{
lean_dec(v_params_429_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_468_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_v_447_; lean_object* v_casesTypes_448_; lean_object* v_extThms_449_; lean_object* v_funCC_450_; lean_object* v_ematch_451_; lean_object* v_inj_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_467_; 
v_v_447_ = lean_array_fget(v_extensions_433_, v___x_441_);
v_casesTypes_448_ = lean_ctor_get(v_v_447_, 0);
v_extThms_449_ = lean_ctor_get(v_v_447_, 1);
v_funCC_450_ = lean_ctor_get(v_v_447_, 2);
v_ematch_451_ = lean_ctor_get(v_v_447_, 3);
v_inj_452_ = lean_ctor_get(v_v_447_, 4);
v_isSharedCheck_467_ = !lean_is_exclusive(v_v_447_);
if (v_isSharedCheck_467_ == 0)
{
v___x_454_ = v_v_447_;
v_isShared_455_ = v_isSharedCheck_467_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_inj_452_);
lean_inc(v_ematch_451_);
lean_inc(v_funCC_450_);
lean_inc(v_extThms_449_);
lean_inc(v_casesTypes_448_);
lean_dec(v_v_447_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_467_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v_xs_x27_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_456_ = lean_box(0);
v_xs_x27_457_ = lean_array_fset(v_extensions_433_, v___x_441_, v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v_declName_430_);
v___x_459_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_inj_452_, v___x_458_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 4, v___x_459_);
v___x_461_ = v___x_454_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_casesTypes_448_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_extThms_449_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_funCC_450_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_ematch_451_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v___x_459_);
v___x_461_ = v_reuseFailAlloc_466_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_array_fset(v_xs_x27_457_, v___x_441_, v___x_461_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 2, v___x_462_);
v___x_464_ = v___x_445_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_config_431_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_identity_432_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_extra_434_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_extraInj_435_);
lean_ctor_set(v_reuseFailAlloc_465_, 5, v_extraFacts_436_);
lean_ctor_set(v_reuseFailAlloc_465_, 6, v_symPrios_437_);
lean_ctor_set(v_reuseFailAlloc_465_, 7, v_norm_438_);
lean_ctor_set(v_reuseFailAlloc_465_, 8, v_normProcs_439_);
lean_ctor_set(v_reuseFailAlloc_465_, 9, v_anchorRefs_x3f_440_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_608_, lean_object* v_x_609_){
_start:
{
if (lean_obj_tag(v_x_609_) == 1)
{
lean_object* v_pre_610_; 
v_pre_610_ = lean_ctor_get(v_x_609_, 0);
switch(lean_obj_tag(v_pre_610_))
{
case 1:
{
lean_object* v_pre_611_; 
v_pre_611_ = lean_ctor_get(v_pre_610_, 0);
switch(lean_obj_tag(v_pre_611_))
{
case 0:
{
lean_object* v_str_612_; lean_object* v_str_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_str_612_ = lean_ctor_get(v_x_609_, 1);
v_str_613_ = lean_ctor_get(v_pre_610_, 1);
v___x_614_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_615_ = lean_string_dec_eq(v_str_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_617_ = lean_string_dec_eq(v_str_613_, v___x_616_);
if (v___x_617_ == 0)
{
return v___x_617_;
}
else
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_619_ = lean_string_dec_eq(v_str_612_, v___x_618_);
if (v___x_619_ == 0)
{
return v___x_619_;
}
else
{
return v_suppressElabErrors_608_;
}
}
}
else
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_621_ = lean_string_dec_eq(v_str_612_, v___x_620_);
if (v___x_621_ == 0)
{
return v___x_621_;
}
else
{
return v_suppressElabErrors_608_;
}
}
}
case 1:
{
lean_object* v_pre_622_; 
v_pre_622_ = lean_ctor_get(v_pre_611_, 0);
if (lean_obj_tag(v_pre_622_) == 0)
{
lean_object* v_str_623_; lean_object* v_str_624_; lean_object* v_str_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v_str_623_ = lean_ctor_get(v_x_609_, 1);
v_str_624_ = lean_ctor_get(v_pre_610_, 1);
v_str_625_ = lean_ctor_get(v_pre_611_, 1);
v___x_626_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_627_ = lean_string_dec_eq(v_str_625_, v___x_626_);
if (v___x_627_ == 0)
{
return v___x_627_;
}
else
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_629_ = lean_string_dec_eq(v_str_624_, v___x_628_);
if (v___x_629_ == 0)
{
return v___x_629_;
}
else
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_631_ = lean_string_dec_eq(v_str_623_, v___x_630_);
if (v___x_631_ == 0)
{
return v___x_631_;
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
uint8_t v___x_632_; 
v___x_632_ = 0;
return v___x_632_;
}
}
default: 
{
uint8_t v___x_633_; 
v___x_633_ = 0;
return v___x_633_;
}
}
}
case 0:
{
lean_object* v_str_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_str_634_ = lean_ctor_get(v_x_609_, 1);
v___x_635_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_636_ = lean_string_dec_eq(v_str_634_, v___x_635_);
if (v___x_636_ == 0)
{
return v___x_636_;
}
else
{
return v_suppressElabErrors_608_;
}
}
default: 
{
uint8_t v___x_637_; 
v___x_637_ = 0;
return v___x_637_;
}
}
}
else
{
uint8_t v___x_638_; 
v___x_638_ = 0;
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_639_, lean_object* v_x_640_){
_start:
{
uint8_t v_suppressElabErrors_boxed_641_; uint8_t v_res_642_; lean_object* v_r_643_; 
v_suppressElabErrors_boxed_641_ = lean_unbox(v_suppressElabErrors_639_);
v_res_642_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_641_, v_x_640_);
lean_dec(v_x_640_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* v_ref_645_, lean_object* v_msgData_646_, uint8_t v_severity_647_, uint8_t v_isSilent_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
uint8_t v___y_655_; lean_object* v___y_656_; uint8_t v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v_toCold_662_; lean_object* v___y_663_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; uint8_t v___y_696_; uint8_t v___y_697_; uint8_t v___y_698_; lean_object* v___y_699_; lean_object* v___y_719_; lean_object* v___y_720_; uint8_t v___y_721_; lean_object* v___y_722_; uint8_t v___y_723_; uint8_t v___y_724_; lean_object* v___y_725_; uint8_t v___y_729_; uint8_t v___y_730_; uint8_t v___x_740_; uint8_t v___y_742_; uint8_t v___x_748_; 
v___x_740_ = 2;
v___x_748_ = l_Lean_instBEqMessageSeverity_beq(v_severity_647_, v___x_740_);
if (v___x_748_ == 0)
{
v___y_742_ = v___x_748_;
goto v___jp_741_;
}
else
{
uint8_t v___x_749_; 
lean_inc_ref(v_msgData_646_);
v___x_749_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_646_);
if (v___x_749_ == 0)
{
v___y_742_ = v___x_749_;
goto v___jp_741_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec_ref(v_msgData_646_);
v___x_750_ = lean_box(0);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
v___jp_654_:
{
lean_object* v_currNamespace_664_; lean_object* v_openDecls_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_env_670_; lean_object* v_nextMacroScope_671_; lean_object* v_ngen_672_; lean_object* v_auxDeclNGen_673_; lean_object* v_traceState_674_; lean_object* v_cache_675_; lean_object* v_recordedDeps_676_; lean_object* v_messages_677_; lean_object* v_infoState_678_; lean_object* v_snapshotTasks_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_690_; 
v_currNamespace_664_ = lean_ctor_get(v_toCold_662_, 4);
v_openDecls_665_ = lean_ctor_get(v_toCold_662_, 5);
lean_inc(v_openDecls_665_);
lean_inc(v_currNamespace_664_);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_currNamespace_664_);
lean_ctor_set(v___x_666_, 1, v_openDecls_665_);
v___x_667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v___y_661_);
lean_inc_ref(v___y_658_);
lean_inc_ref(v___y_659_);
v___x_668_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_668_, 0, v___y_659_);
lean_ctor_set(v___x_668_, 1, v___y_656_);
lean_ctor_set(v___x_668_, 2, v___y_660_);
lean_ctor_set(v___x_668_, 3, v___y_658_);
lean_ctor_set(v___x_668_, 4, v___x_667_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*5, v___y_657_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*5 + 1, v___y_655_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*5 + 2, v_isSilent_648_);
v___x_669_ = lean_st_ref_take(v___y_663_);
v_env_670_ = lean_ctor_get(v___x_669_, 0);
v_nextMacroScope_671_ = lean_ctor_get(v___x_669_, 1);
v_ngen_672_ = lean_ctor_get(v___x_669_, 2);
v_auxDeclNGen_673_ = lean_ctor_get(v___x_669_, 3);
v_traceState_674_ = lean_ctor_get(v___x_669_, 4);
v_cache_675_ = lean_ctor_get(v___x_669_, 5);
v_recordedDeps_676_ = lean_ctor_get(v___x_669_, 6);
v_messages_677_ = lean_ctor_get(v___x_669_, 7);
v_infoState_678_ = lean_ctor_get(v___x_669_, 8);
v_snapshotTasks_679_ = lean_ctor_get(v___x_669_, 9);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_690_ == 0)
{
v___x_681_ = v___x_669_;
v_isShared_682_ = v_isSharedCheck_690_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_snapshotTasks_679_);
lean_inc(v_infoState_678_);
lean_inc(v_messages_677_);
lean_inc(v_recordedDeps_676_);
lean_inc(v_cache_675_);
lean_inc(v_traceState_674_);
lean_inc(v_auxDeclNGen_673_);
lean_inc(v_ngen_672_);
lean_inc(v_nextMacroScope_671_);
lean_inc(v_env_670_);
lean_dec(v___x_669_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_690_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_683_ = lean_box(0);
v___x_684_ = l_Lean_MessageLog_add(v___x_668_, v_messages_677_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 7, v___x_684_);
v___x_686_ = v___x_681_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_env_670_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_nextMacroScope_671_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_ngen_672_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v_auxDeclNGen_673_);
lean_ctor_set(v_reuseFailAlloc_689_, 4, v_traceState_674_);
lean_ctor_set(v_reuseFailAlloc_689_, 5, v_cache_675_);
lean_ctor_set(v_reuseFailAlloc_689_, 6, v_recordedDeps_676_);
lean_ctor_set(v_reuseFailAlloc_689_, 7, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_689_, 8, v_infoState_678_);
lean_ctor_set(v_reuseFailAlloc_689_, 9, v_snapshotTasks_679_);
v___x_686_ = v_reuseFailAlloc_689_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_st_ref_put(v___y_663_, v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_683_);
return v___x_688_;
}
}
}
v___jp_691_:
{
lean_object* v_fileName_700_; lean_object* v_fileMap_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_717_; 
v_fileName_700_ = lean_ctor_get(v___y_694_, 0);
v_fileMap_701_ = lean_ctor_get(v___y_694_, 1);
v___x_702_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_646_);
v___x_703_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_702_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
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
v___x_708_ = l_Lean_FileMap_toPosition(v_fileMap_701_, v___y_695_);
lean_dec(v___y_695_);
v___x_709_ = l_Lean_FileMap_toPosition(v_fileMap_701_, v___y_699_);
lean_dec(v___y_699_);
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
v___x_711_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_698_ == 0)
{
lean_del_object(v___x_706_);
lean_dec_ref(v___y_693_);
v___y_655_ = v___y_696_;
v___y_656_ = v___x_708_;
v___y_657_ = v___y_697_;
v___y_658_ = v___x_711_;
v___y_659_ = v_fileName_700_;
v___y_660_ = v___x_710_;
v___y_661_ = v_a_704_;
v_toCold_662_ = v___y_692_;
v___y_663_ = v___y_652_;
goto v___jp_654_;
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
v___y_655_ = v___y_696_;
v___y_656_ = v___x_708_;
v___y_657_ = v___y_697_;
v___y_658_ = v___x_711_;
v___y_659_ = v_fileName_700_;
v___y_660_ = v___x_710_;
v___y_661_ = v_a_704_;
v_toCold_662_ = v___y_692_;
v___y_663_ = v___y_652_;
goto v___jp_654_;
}
}
}
}
v___jp_718_:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Syntax_getTailPos_x3f(v___y_722_, v___y_724_);
lean_dec(v___y_722_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_inc(v___y_725_);
v___y_692_ = v___y_719_;
v___y_693_ = v___y_720_;
v___y_694_ = v___y_719_;
v___y_695_ = v___y_725_;
v___y_696_ = v___y_723_;
v___y_697_ = v___y_724_;
v___y_698_ = v___y_721_;
v___y_699_ = v___y_725_;
goto v___jp_691_;
}
else
{
lean_object* v_val_727_; 
v_val_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_val_727_);
lean_dec_ref_known(v___x_726_, 1);
v___y_692_ = v___y_719_;
v___y_693_ = v___y_720_;
v___y_694_ = v___y_719_;
v___y_695_ = v___y_725_;
v___y_696_ = v___y_723_;
v___y_697_ = v___y_724_;
v___y_698_ = v___y_721_;
v___y_699_ = v_val_727_;
goto v___jp_691_;
}
}
v___jp_728_:
{
lean_object* v_toCold_731_; lean_object* v_ref_732_; uint8_t v_suppressElabErrors_733_; lean_object* v___x_734_; lean_object* v___f_735_; lean_object* v_ref_736_; lean_object* v___x_737_; 
v_toCold_731_ = lean_ctor_get(v___y_651_, 0);
v_ref_732_ = lean_ctor_get(v___y_651_, 2);
v_suppressElabErrors_733_ = lean_ctor_get_uint8(v___y_651_, sizeof(void*)*3 + 2);
v___x_734_ = lean_box(v_suppressElabErrors_733_);
v___f_735_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_735_, 0, v___x_734_);
v_ref_736_ = l_Lean_replaceRef(v_ref_645_, v_ref_732_);
v___x_737_ = l_Lean_Syntax_getPos_x3f(v_ref_736_, v___y_729_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v___x_738_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v___y_719_ = v_toCold_731_;
v___y_720_ = v___f_735_;
v___y_721_ = v_suppressElabErrors_733_;
v___y_722_ = v_ref_736_;
v___y_723_ = v___y_730_;
v___y_724_ = v___y_729_;
v___y_725_ = v___x_738_;
goto v___jp_718_;
}
else
{
lean_object* v_val_739_; 
v_val_739_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v___x_737_, 1);
v___y_719_ = v_toCold_731_;
v___y_720_ = v___f_735_;
v___y_721_ = v_suppressElabErrors_733_;
v___y_722_ = v_ref_736_;
v___y_723_ = v___y_730_;
v___y_724_ = v___y_729_;
v___y_725_ = v_val_739_;
goto v___jp_718_;
}
}
v___jp_741_:
{
uint8_t v___x_743_; uint8_t v___x_744_; 
v___x_743_ = 1;
v___x_744_ = l_Lean_instBEqMessageSeverity_beq(v_severity_647_, v___x_743_);
if (v___x_744_ == 0)
{
v___y_729_ = v___y_742_;
v___y_730_ = v_severity_647_;
goto v___jp_728_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_745_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_651_);
v___x_746_ = l_Lean_warningAsError;
v___x_747_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_745_, v___x_746_);
lean_dec_ref(v___x_745_);
if (v___x_747_ == 0)
{
v___y_729_ = v___y_742_;
v___y_730_ = v_severity_647_;
goto v___jp_728_;
}
else
{
v___y_729_ = v___y_742_;
v___y_730_ = v___x_740_;
goto v___jp_728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_752_, lean_object* v_msgData_753_, lean_object* v_severity_754_, lean_object* v_isSilent_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
uint8_t v_severity_boxed_761_; uint8_t v_isSilent_boxed_762_; lean_object* v_res_763_; 
v_severity_boxed_761_ = lean_unbox(v_severity_754_);
v_isSilent_boxed_762_ = lean_unbox(v_isSilent_755_);
v_res_763_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_752_, v_msgData_753_, v_severity_boxed_761_, v_isSilent_boxed_762_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v_ref_752_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object* v_msgData_764_, uint8_t v_severity_765_, uint8_t v_isSilent_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_ref_772_; lean_object* v___x_773_; 
v_ref_772_ = lean_ctor_get(v___y_769_, 2);
v___x_773_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_772_, v_msgData_764_, v_severity_765_, v_isSilent_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object* v_msgData_774_, lean_object* v_severity_775_, lean_object* v_isSilent_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
uint8_t v_severity_boxed_782_; uint8_t v_isSilent_boxed_783_; lean_object* v_res_784_; 
v_severity_boxed_782_ = lean_unbox(v_severity_775_);
v_isSilent_boxed_783_ = lean_unbox(v_isSilent_776_);
v_res_784_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_774_, v_severity_boxed_782_, v_isSilent_boxed_783_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object* v_msgData_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
uint8_t v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; 
v___x_791_ = 1;
v___x_792_ = 0;
v___x_793_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_785_, v___x_791_, v___x_792_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object* v_msgData_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v_msgData_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_800_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0));
v___x_803_ = l_Lean_stringToMessageData(v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
if (lean_obj_tag(v_a_804_) == 0)
{
lean_object* v___x_806_; 
v___x_806_ = l_List_reverse___redArg(v_a_805_);
return v___x_806_;
}
else
{
lean_object* v_head_807_; lean_object* v_tail_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_821_; 
v_head_807_ = lean_ctor_get(v_a_804_, 0);
v_tail_808_ = lean_ctor_get(v_a_804_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_a_804_);
if (v_isSharedCheck_821_ == 0)
{
v___x_810_ = v_a_804_;
v_isShared_811_ = v_isSharedCheck_821_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_tail_808_);
lean_inc(v_head_807_);
lean_dec(v_a_804_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_821_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
uint8_t v_minIndexable_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v_minIndexable_812_ = 0;
v___x_813_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_814_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_807_, v_minIndexable_812_);
lean_dec(v_head_807_);
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_813_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 1, v_a_805_);
lean_ctor_set(v___x_810_, 0, v___x_816_);
v___x_818_ = v___x_810_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_a_805_);
v___x_818_ = v_reuseFailAlloc_820_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
v_a_804_ = v_tail_808_;
v_a_805_ = v___x_818_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object* v_a_822_, lean_object* v_a_823_){
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
lean_object* v_head_825_; lean_object* v_tail_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_834_; 
v_head_825_ = lean_ctor_get(v_a_822_, 0);
v_tail_826_ = lean_ctor_get(v_a_822_, 1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_a_822_);
if (v_isSharedCheck_834_ == 0)
{
v___x_828_ = v_a_822_;
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_tail_826_);
lean_inc(v_head_825_);
lean_dec(v_a_822_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v_a_823_);
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_head_825_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_a_823_);
v___x_831_ = v_reuseFailAlloc_833_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
v_a_822_ = v_tail_826_;
v_a_823_ = v___x_831_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0));
v___x_837_ = l_Lean_stringToMessageData(v___x_836_);
return v___x_837_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2));
v___x_840_ = l_Lean_stringToMessageData(v___x_839_);
return v___x_840_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4));
v___x_843_ = l_Lean_stringToMessageData(v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object* v_s_844_, lean_object* v_declName_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_kinds_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v_ks_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_inc(v_declName_845_);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v_declName_845_);
v___x_877_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_844_, v___x_876_);
lean_dec_ref_known(v___x_876_, 1);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec(v_declName_845_);
v___x_878_ = lean_box(0);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
else
{
lean_object* v_head_880_; lean_object* v_tail_881_; uint8_t v_minIndexable_882_; uint8_t v_gen_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; 
v_head_880_ = lean_ctor_get(v___x_877_, 0);
v_tail_881_ = lean_ctor_get(v___x_877_, 1);
v_minIndexable_882_ = 0;
if (lean_obj_tag(v_tail_881_) == 0)
{
lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_903_; 
lean_inc(v_head_880_);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; lean_object* v_unused_905_; 
v_unused_904_ = lean_ctor_get(v___x_877_, 1);
lean_dec(v_unused_904_);
v_unused_905_ = lean_ctor_get(v___x_877_, 0);
lean_dec(v_unused_905_);
v___x_895_ = v___x_877_;
v_isShared_896_ = v_isSharedCheck_903_;
goto v_resetjp_894_;
}
else
{
lean_dec(v___x_877_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_903_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_897_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_898_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_880_, v_minIndexable_882_);
lean_dec(v_head_880_);
v___x_899_ = l_Lean_stringToMessageData(v___x_898_);
if (v_isShared_896_ == 0)
{
lean_ctor_set_tag(v___x_895_, 7);
lean_ctor_set(v___x_895_, 1, v___x_899_);
lean_ctor_set(v___x_895_, 0, v___x_897_);
v___x_901_ = v___x_895_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
v_kinds_852_ = v___x_901_;
v___y_853_ = v_a_846_;
v___y_854_ = v_a_847_;
v___y_855_ = v_a_848_;
v___y_856_ = v_a_849_;
goto v___jp_851_;
}
}
}
else
{
lean_object* v_head_906_; 
v_head_906_ = lean_ctor_get(v_tail_881_, 0);
switch(lean_obj_tag(v_head_906_))
{
case 1:
{
lean_object* v_tail_907_; 
v_tail_907_ = lean_ctor_get(v_tail_881_, 1);
if (lean_obj_tag(v_tail_907_) == 0)
{
if (lean_obj_tag(v_head_880_) == 0)
{
uint8_t v_gen_908_; 
lean_inc_ref(v_head_880_);
lean_dec_ref_known(v___x_877_, 2);
v_gen_908_ = lean_ctor_get_uint8(v_head_880_, 0);
lean_dec_ref_known(v_head_880_, 0);
v_gen_884_ = v_gen_908_;
v___y_885_ = v_a_846_;
v___y_886_ = v_a_847_;
v___y_887_ = v_a_848_;
v___y_888_ = v_a_849_;
goto v___jp_883_;
}
else
{
v_ks_867_ = v___x_877_;
v___y_868_ = v_a_846_;
v___y_869_ = v_a_847_;
v___y_870_ = v_a_848_;
v___y_871_ = v_a_849_;
goto v___jp_866_;
}
}
else
{
v_ks_867_ = v___x_877_;
v___y_868_ = v_a_846_;
v___y_869_ = v_a_847_;
v___y_870_ = v_a_848_;
v___y_871_ = v_a_849_;
goto v___jp_866_;
}
}
case 0:
{
lean_object* v_tail_909_; 
v_tail_909_ = lean_ctor_get(v_tail_881_, 1);
if (lean_obj_tag(v_tail_909_) == 0)
{
if (lean_obj_tag(v_head_880_) == 1)
{
uint8_t v_gen_910_; 
lean_inc_ref(v_head_880_);
lean_dec_ref_known(v___x_877_, 2);
v_gen_910_ = lean_ctor_get_uint8(v_head_880_, 0);
lean_dec_ref_known(v_head_880_, 0);
v_gen_884_ = v_gen_910_;
v___y_885_ = v_a_846_;
v___y_886_ = v_a_847_;
v___y_887_ = v_a_848_;
v___y_888_ = v_a_849_;
goto v___jp_883_;
}
else
{
v_ks_867_ = v___x_877_;
v___y_868_ = v_a_846_;
v___y_869_ = v_a_847_;
v___y_870_ = v_a_848_;
v___y_871_ = v_a_849_;
goto v___jp_866_;
}
}
else
{
v_ks_867_ = v___x_877_;
v___y_868_ = v_a_846_;
v___y_869_ = v_a_847_;
v___y_870_ = v_a_848_;
v___y_871_ = v_a_849_;
goto v___jp_866_;
}
}
default: 
{
v_ks_867_ = v___x_877_;
v___y_868_ = v_a_846_;
v___y_869_ = v_a_847_;
v___y_870_ = v_a_848_;
v___y_871_ = v_a_849_;
goto v___jp_866_;
}
}
}
v___jp_883_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_889_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_890_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_890_, 0, v_gen_884_);
v___x_891_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v___x_890_, v_minIndexable_882_);
lean_dec_ref_known(v___x_890_, 0);
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_889_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v_kinds_852_ = v___x_893_;
v___y_853_ = v___y_885_;
v___y_854_ = v___y_886_;
v___y_855_ = v___y_887_;
v___y_856_ = v___y_888_;
goto v___jp_851_;
}
}
v___jp_851_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_857_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1);
v___x_858_ = l_Lean_MessageData_ofName(v_declName_845_);
v___x_859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v_kinds_852_);
v___x_863_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v___x_864_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
return v___x_865_;
}
v___jp_866_:
{
lean_object* v___x_872_; lean_object* v_ks_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_872_ = lean_box(0);
v_ks_873_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(v_ks_867_, v___x_872_);
v___x_874_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(v_ks_873_, v___x_872_);
v___x_875_ = l_Lean_MessageData_ofList(v___x_874_);
v_kinds_852_ = v___x_875_;
v___y_853_ = v___y_868_;
v___y_854_ = v___y_869_;
v___y_855_ = v___y_870_;
v___y_856_ = v___y_871_;
goto v___jp_851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object* v_s_911_, lean_object* v_declName_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_s_911_, v_declName_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec_ref(v_s_911_);
return v_res_918_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_919_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_922_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_923_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
lean_ctor_set(v___x_925_, 2, v___x_924_);
lean_ctor_set(v___x_925_, 3, v___x_924_);
lean_ctor_set(v___x_925_, 4, v___x_923_);
lean_ctor_set(v___x_925_, 5, v___x_923_);
lean_ctor_set(v___x_925_, 6, v___x_923_);
lean_ctor_set(v___x_925_, 7, v___x_923_);
lean_ctor_set(v___x_925_, 8, v___x_923_);
lean_ctor_set(v___x_925_, 9, v___x_923_);
lean_ctor_set(v___x_925_, 10, v___x_923_);
lean_ctor_set(v___x_925_, 11, v___x_922_);
return v___x_925_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_unsigned_to_nat(32u);
v___x_927_ = lean_mk_empty_array_with_capacity(v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_929_ = ((size_t)5ULL);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = lean_unsigned_to_nat(32u);
v___x_932_ = lean_mk_empty_array_with_capacity(v___x_931_);
v___x_933_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3);
v___x_934_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_932_);
lean_ctor_set(v___x_934_, 2, v___x_930_);
lean_ctor_set(v___x_934_, 3, v___x_930_);
lean_ctor_set_usize(v___x_934_, 4, v___x_929_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_935_ = lean_box(1);
v___x_936_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4);
v___x_937_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_936_);
lean_ctor_set(v___x_938_, 2, v___x_935_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object* v_msgData_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; lean_object* v_toCold_944_; lean_object* v_env_945_; lean_object* v_options_946_; uint8_t v___x_947_; lean_object* v_env_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_943_ = lean_st_ref_get(v___y_941_);
v_toCold_944_ = lean_ctor_get(v___y_940_, 0);
v_env_945_ = lean_ctor_get(v___x_943_, 0);
lean_inc_ref(v_env_945_);
lean_dec(v___x_943_);
v_options_946_ = lean_ctor_get(v_toCold_944_, 2);
v___x_947_ = 0;
v_env_948_ = l_Lean_Environment_setRecordingDeps(v_env_945_, v___x_947_);
v___x_949_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_950_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_946_);
v___x_951_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_951_, 0, v_env_948_);
lean_ctor_set(v___x_951_, 1, v___x_949_);
lean_ctor_set(v___x_951_, 2, v___x_950_);
lean_ctor_set(v___x_951_, 3, v_options_946_);
v___x_952_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v_msgData_939_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object* v_msgData_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msgData_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_ref_963_; lean_object* v___x_964_; lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_973_; 
v_ref_963_ = lean_ctor_get(v___y_960_, 2);
v___x_964_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msg_959_, v___y_960_, v___y_961_);
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_973_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
lean_inc(v_ref_963_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v_ref_963_);
lean_ctor_set(v___x_969_, 1, v_a_965_);
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 1);
lean_ctor_set(v___x_967_, 0, v___x_969_);
v___x_971_ = v___x_967_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_978_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object* v_s_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_996_; lean_object* v_env_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_996_ = lean_st_ref_get(v_a_994_);
v_env_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc_ref(v_env_997_);
lean_dec(v___x_996_);
v___x_998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
v___x_999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5));
lean_inc_ref(v_s_992_);
v___x_1000_ = l_Lean_Parser_runParserCategory(v_env_997_, v___x_998_, v_s_992_, v___x_999_);
if (lean_obj_tag(v___x_1000_) == 1)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
lean_dec_ref(v_s_992_);
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = l_Lean_Meta_Grind_getAttrKindCore(v_a_1001_, v_a_993_, v_a_994_);
return v___x_1002_;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_dec_ref(v___x_1000_);
v___x_1003_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7);
v___x_1004_ = l_Lean_stringToMessageData(v_s_992_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1005_, v_a_993_, v_a_994_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object* v_s_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(v_s_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object* v_00_u03b1_1012_, lean_object* v_msg_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_1013_, v___y_1014_, v___y_1015_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object* v_00_u03b1_1018_, lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(v_00_u03b1_1018_, v_msg_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object* v_msg_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_ref_1030_; lean_object* v___x_1031_; lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1040_; 
v_ref_1030_ = lean_ctor_get(v___y_1027_, 2);
v___x_1031_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
lean_inc(v_ref_1030_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v_ref_1030_);
lean_ctor_set(v___x_1036_, 1, v_a_1032_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set_tag(v___x_1034_, 1);
lean_ctor_set(v___x_1034_, 0, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object* v_msg_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1047_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t v_minIndexable_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
if (v_minIndexable_1051_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1);
v___x_1060_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1059_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object* v_minIndexable_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
uint8_t v_minIndexable_boxed_1067_; lean_object* v_res_1068_; 
v_minIndexable_boxed_1067_ = lean_unbox(v_minIndexable_1061_);
v_res_1068_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_boxed_1067_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object* v_00_u03b1_1069_, lean_object* v_msg_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object* v_00_u03b1_1077_, lean_object* v_msg_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(v_00_u03b1_1077_, v_msg_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1084_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_1093_ = l_Lean_stringToMessageData(v___x_1092_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1096_ = l_Lean_stringToMessageData(v___x_1095_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1099_ = l_Lean_stringToMessageData(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1106_, lean_object* v_declHint_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v_env_1112_; uint8_t v___x_1113_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_st_ref_get(v___y_1108_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = l_Lean_Name_isAnonymous(v_declHint_1107_);
if (v___x_1113_ == 0)
{
uint8_t v_isExporting_1114_; 
v_isExporting_1114_ = lean_ctor_get_uint8(v_env_1112_, sizeof(void*)*13);
if (v_isExporting_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_dec_ref(v_env_1112_);
lean_dec(v_declHint_1107_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v_msg_1106_);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
lean_inc_ref(v_env_1112_);
v___x_1116_ = l_Lean_Environment_setExporting(v_env_1112_, v___x_1113_);
lean_inc(v_declHint_1107_);
lean_inc_ref(v___x_1116_);
v___x_1117_ = l_Lean_Environment_contains(v___x_1116_, v_declHint_1107_, v_isExporting_1114_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref(v___x_1116_);
lean_dec_ref(v_env_1112_);
lean_dec(v_declHint_1107_);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_msg_1106_);
return v___x_1118_;
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v_c_1124_; lean_object* v___x_1125_; 
v___x_1119_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_1120_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
v___x_1121_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1116_);
v___x_1122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1116_);
lean_ctor_set(v___x_1122_, 1, v___x_1119_);
lean_ctor_set(v___x_1122_, 2, v___x_1120_);
lean_ctor_set(v___x_1122_, 3, v___x_1121_);
lean_inc(v_declHint_1107_);
v___x_1123_ = l_Lean_MessageData_ofConstName(v_declHint_1107_, v___x_1113_);
v_c_1124_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1124_, 0, v___x_1122_);
lean_ctor_set(v_c_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1116_, v_declHint_1107_);
lean_dec_ref(v___x_1116_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec_ref(v_env_1112_);
lean_dec(v_declHint_1107_);
v___x_1126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
lean_ctor_set(v___x_1127_, 1, v_c_1124_);
v___x_1128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_MessageData_note(v___x_1129_);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_msg_1106_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
else
{
lean_object* v_val_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1167_; 
v_val_1133_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1135_ = v___x_1125_;
v_isShared_1136_ = v_isSharedCheck_1167_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_val_1133_);
lean_dec(v___x_1125_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1167_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v_moduleNames_1138_; lean_object* v_mod_1139_; uint8_t v___x_1140_; 
v___x_1137_ = l_Lean_Environment_header(v_env_1112_);
lean_dec_ref(v_env_1112_);
v_moduleNames_1138_ = lean_ctor_get(v___x_1137_, 4);
lean_inc_ref(v_moduleNames_1138_);
lean_dec_ref(v___x_1137_);
v_mod_1139_ = lean_array_get(v___x_1110_, v_moduleNames_1138_, v_val_1133_);
lean_dec(v_val_1133_);
lean_dec_ref(v_moduleNames_1138_);
v___x_1140_ = l_Lean_isPrivateName(v_declHint_1107_);
lean_dec(v_declHint_1107_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v_c_1124_);
v___x_1143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = l_Lean_MessageData_ofName(v_mod_1139_);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_MessageData_note(v___x_1148_);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v_msg_1106_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1150_);
v___x_1152_ = v___x_1135_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1154_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v_c_1124_);
v___x_1156_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_MessageData_ofName(v_mod_1139_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = l_Lean_MessageData_note(v___x_1161_);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v_msg_1106_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1163_);
v___x_1165_ = v___x_1135_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1168_; 
lean_dec_ref(v_env_1112_);
lean_dec(v_declHint_1107_);
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_msg_1106_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1169_, lean_object* v_declHint_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1169_, v_declHint_1170_, v___y_1171_);
lean_dec(v___y_1171_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1174_, lean_object* v_declHint_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1191_; 
v___x_1181_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1174_, v_declHint_1175_, v___y_1179_);
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1191_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1191_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1186_ = l_Lean_unknownIdentifierMessageTag;
v___x_1187_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v_a_1182_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1187_);
v___x_1189_ = v___x_1184_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1192_, lean_object* v_declHint_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1192_, v_declHint_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1200_, lean_object* v_msg_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_toCold_1207_; lean_object* v_currRecDepth_1208_; lean_object* v_ref_1209_; uint16_t v_optionFlags_1210_; uint8_t v_suppressElabErrors_1211_; uint8_t v_checkDeprecated_1212_; uint8_t v_isRecordingDeps_1213_; lean_object* v_ref_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_toCold_1207_ = lean_ctor_get(v___y_1204_, 0);
v_currRecDepth_1208_ = lean_ctor_get(v___y_1204_, 1);
v_ref_1209_ = lean_ctor_get(v___y_1204_, 2);
v_optionFlags_1210_ = lean_ctor_get_uint16(v___y_1204_, sizeof(void*)*3);
v_suppressElabErrors_1211_ = lean_ctor_get_uint8(v___y_1204_, sizeof(void*)*3 + 2);
v_checkDeprecated_1212_ = lean_ctor_get_uint8(v___y_1204_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1213_ = lean_ctor_get_uint8(v___y_1204_, sizeof(void*)*3 + 4);
v_ref_1214_ = l_Lean_replaceRef(v_ref_1200_, v_ref_1209_);
lean_inc(v_currRecDepth_1208_);
lean_inc_ref(v_toCold_1207_);
v___x_1215_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1215_, 0, v_toCold_1207_);
lean_ctor_set(v___x_1215_, 1, v_currRecDepth_1208_);
lean_ctor_set(v___x_1215_, 2, v_ref_1214_);
lean_ctor_set_uint16(v___x_1215_, sizeof(void*)*3, v_optionFlags_1210_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*3 + 2, v_suppressElabErrors_1211_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*3 + 3, v_checkDeprecated_1212_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*3 + 4, v_isRecordingDeps_1213_);
v___x_1216_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1201_, v___y_1202_, v___y_1203_, v___x_1215_, v___y_1205_);
lean_dec_ref_known(v___x_1215_, 3);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1217_, lean_object* v_msg_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1217_, v_msg_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v_ref_1217_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1225_, lean_object* v_msg_1226_, lean_object* v_declHint_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1233_; lean_object* v_a_1234_; lean_object* v___x_1235_; 
v___x_1233_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1226_, v_declHint_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref(v___x_1233_);
v___x_1235_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1225_, v_a_1234_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1236_, lean_object* v_msg_1237_, lean_object* v_declHint_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1236_, v_msg_1237_, v_declHint_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v_ref_1236_);
return v_res_1244_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1247_ = l_Lean_stringToMessageData(v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1248_, lean_object* v_constName_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; uint8_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1255_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1256_ = 0;
lean_inc(v_constName_1249_);
v___x_1257_ = l_Lean_MessageData_ofConstName(v_constName_1249_, v___x_1256_);
v___x_1258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1255_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1248_, v___x_1260_, v_constName_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1262_, lean_object* v_constName_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1262_, v_constName_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v_ref_1262_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_constName_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_ref_1276_; lean_object* v___x_1277_; 
v_ref_1276_ = lean_ctor_get(v___y_1273_, 2);
v___x_1277_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1276_, v_constName_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* v_constName_1285_, uint8_t v_skipRealize_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; lean_object* v_env_1293_; lean_object* v___x_1294_; 
v___x_1292_ = lean_st_ref_get(v___y_1290_);
v_env_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc_ref(v_env_1293_);
lean_dec(v___x_1292_);
lean_inc(v_constName_1285_);
v___x_1294_ = l_Lean_Environment_findAsync_x3f(v_env_1293_, v_constName_1285_, v_skipRealize_1286_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1285_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1295_;
}
else
{
lean_object* v_val_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_constName_1285_);
v_val_1296_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1294_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_val_1296_);
lean_dec(v___x_1294_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 0);
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_val_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* v_constName_1304_, lean_object* v_skipRealize_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
uint8_t v_skipRealize_boxed_1311_; lean_object* v_res_1312_; 
v_skipRealize_boxed_1311_ = lean_unbox(v_skipRealize_1305_);
v_res_1312_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1304_, v_skipRealize_boxed_1311_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* v_declName_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; lean_object* v_env_1317_; uint8_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1316_ = lean_st_ref_get(v___y_1314_);
v_env_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc_ref(v_env_1317_);
lean_dec(v___x_1316_);
v___x_1318_ = l_Lean_getReducibilityStatusCore(v_env_1317_, v_declName_1313_);
v___x_1319_ = lean_box(v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_declName_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1321_, v___y_1322_);
lean_dec(v___y_1322_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* v_declName_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1347_; 
v___x_1331_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1325_, v___y_1329_);
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1347_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1347_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_unbox(v_a_1332_);
lean_dec(v_a_1332_);
if (v___x_1336_ == 0)
{
uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1337_ = 1;
v___x_1338_ = lean_box(v___x_1337_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1338_);
v___x_1340_ = v___x_1334_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
else
{
uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1342_ = 0;
v___x_1343_ = lean_box(v___x_1342_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1343_);
v___x_1345_ = v___x_1334_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* v_declName_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
return v_res_1354_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
v___x_1357_ = l_Lean_stringToMessageData(v___x_1356_);
return v___x_1357_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
v___x_1360_ = l_Lean_stringToMessageData(v___x_1359_);
return v___x_1360_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
v___x_1363_ = l_Lean_stringToMessageData(v___x_1362_);
return v___x_1363_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
v___x_1366_ = l_Lean_stringToMessageData(v___x_1365_);
return v___x_1366_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
v___x_1369_ = l_Lean_stringToMessageData(v___x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* v_params_1370_, lean_object* v_id_1371_, lean_object* v_declName_1372_, lean_object* v_kind_1373_, uint8_t v_minIndexable_1374_, uint8_t v_suggest_1375_, uint8_t v_warn_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v___y_1383_; lean_object* v_thm_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; uint8_t v___x_1440_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___x_1639_; 
v___x_1440_ = 0;
lean_inc(v_declName_1372_);
v___x_1639_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1372_, v___x_1440_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
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
v___y_1569_ = v_a_1377_;
v___y_1570_ = v_a_1378_;
v___y_1571_ = v_a_1379_;
v___y_1572_ = v_a_1380_;
goto v___jp_1568_;
}
case 2:
{
v___y_1569_ = v_a_1377_;
v___y_1570_ = v_a_1378_;
v___y_1571_ = v_a_1379_;
v___y_1572_ = v_a_1380_;
goto v___jp_1568_;
}
case 6:
{
v___y_1569_ = v_a_1377_;
v___y_1570_ = v_a_1378_;
v___y_1571_ = v_a_1379_;
v___y_1572_ = v_a_1380_;
goto v___jp_1568_;
}
case 0:
{
lean_object* v___x_1642_; 
lean_dec(v_id_1371_);
lean_inc(v_declName_1372_);
v___x_1642_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1372_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
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
v___y_1499_ = v_a_1377_;
v___y_1500_ = v_a_1378_;
v___y_1501_ = v_a_1379_;
v___y_1502_ = v_a_1380_;
goto v___jp_1498_;
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_kind_1373_);
lean_dec_ref(v_params_1370_);
v___x_1645_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1646_ = l_Lean_MessageData_ofConstName(v_declName_1372_, v___x_1440_);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1649_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
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
lean_dec(v_kind_1373_);
lean_dec(v_declName_1372_);
lean_dec_ref(v_params_1370_);
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
lean_dec(v_kind_1373_);
lean_dec(v_id_1371_);
lean_dec_ref(v_params_1370_);
v___x_1667_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1668_ = l_Lean_MessageData_ofConstName(v_declName_1372_, v___x_1440_);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1671_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
return v___x_1672_;
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v_kind_1373_);
lean_dec(v_declName_1372_);
lean_dec(v_id_1371_);
lean_dec_ref(v_params_1370_);
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
v___jp_1382_:
{
lean_object* v_config_1384_; lean_object* v_identity_1385_; lean_object* v_extensions_1386_; lean_object* v_extra_1387_; lean_object* v_extraInj_1388_; lean_object* v_extraFacts_1389_; lean_object* v_symPrios_1390_; lean_object* v_norm_1391_; lean_object* v_normProcs_1392_; lean_object* v_anchorRefs_x3f_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1402_; 
v_config_1384_ = lean_ctor_get(v_params_1370_, 0);
v_identity_1385_ = lean_ctor_get(v_params_1370_, 1);
v_extensions_1386_ = lean_ctor_get(v_params_1370_, 2);
v_extra_1387_ = lean_ctor_get(v_params_1370_, 3);
v_extraInj_1388_ = lean_ctor_get(v_params_1370_, 4);
v_extraFacts_1389_ = lean_ctor_get(v_params_1370_, 5);
v_symPrios_1390_ = lean_ctor_get(v_params_1370_, 6);
v_norm_1391_ = lean_ctor_get(v_params_1370_, 7);
v_normProcs_1392_ = lean_ctor_get(v_params_1370_, 8);
v_anchorRefs_x3f_1393_ = lean_ctor_get(v_params_1370_, 9);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_params_1370_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1395_ = v_params_1370_;
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_anchorRefs_x3f_1393_);
lean_inc(v_normProcs_1392_);
lean_inc(v_norm_1391_);
lean_inc(v_symPrios_1390_);
lean_inc(v_extraFacts_1389_);
lean_inc(v_extraInj_1388_);
lean_inc(v_extra_1387_);
lean_inc(v_extensions_1386_);
lean_inc(v_identity_1385_);
lean_inc(v_config_1384_);
lean_dec(v_params_1370_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = l_Lean_PersistentArray_push___redArg(v_extra_1387_, v___y_1383_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 3, v___x_1397_);
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_config_1384_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_identity_1385_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_extensions_1386_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_extraInj_1388_);
lean_ctor_set(v_reuseFailAlloc_1401_, 5, v_extraFacts_1389_);
lean_ctor_set(v_reuseFailAlloc_1401_, 6, v_symPrios_1390_);
lean_ctor_set(v_reuseFailAlloc_1401_, 7, v_norm_1391_);
lean_ctor_set(v_reuseFailAlloc_1401_, 8, v_normProcs_1392_);
lean_ctor_set(v_reuseFailAlloc_1401_, 9, v_anchorRefs_x3f_1393_);
v___x_1399_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
}
v___jp_1403_:
{
if (v_warn_1376_ == 0)
{
lean_dec(v_declName_1372_);
v___y_1383_ = v_thm_1404_;
goto v___jp_1382_;
}
else
{
lean_object* v_extensions_1409_; lean_object* v_patterns_1410_; lean_object* v_origin_1411_; lean_object* v_cnstrs_1412_; uint8_t v___x_1413_; 
v_extensions_1409_ = lean_ctor_get(v_params_1370_, 2);
v_patterns_1410_ = lean_ctor_get(v_thm_1404_, 3);
v_origin_1411_ = lean_ctor_get(v_thm_1404_, 5);
v_cnstrs_1412_ = lean_ctor_get(v_thm_1404_, 7);
v___x_1413_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1409_, v_origin_1411_, v_patterns_1410_, v_cnstrs_1412_);
if (v___x_1413_ == 0)
{
lean_dec(v_declName_1372_);
v___y_1383_ = v_thm_1404_;
goto v___jp_1382_;
}
else
{
lean_object* v___x_1414_; 
v___x_1414_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1409_, v_declName_1372_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_dec_ref_known(v___x_1414_, 1);
v___y_1383_ = v_thm_1404_;
goto v___jp_1382_;
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v_thm_1404_);
lean_dec_ref(v_params_1370_);
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
}
v___jp_1423_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1436_ = l_Lean_PersistentArray_push___redArg(v___y_1435_, v___y_1434_);
v___x_1437_ = l_Lean_PersistentArray_push___redArg(v___x_1436_, v___y_1430_);
v___x_1438_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1438_, 0, v___y_1432_);
lean_ctor_set(v___x_1438_, 1, v___y_1427_);
lean_ctor_set(v___x_1438_, 2, v___y_1426_);
lean_ctor_set(v___x_1438_, 3, v___x_1437_);
lean_ctor_set(v___x_1438_, 4, v___y_1429_);
lean_ctor_set(v___x_1438_, 5, v___y_1424_);
lean_ctor_set(v___x_1438_, 6, v___y_1425_);
lean_ctor_set(v___x_1438_, 7, v___y_1428_);
lean_ctor_set(v___x_1438_, 8, v___y_1431_);
lean_ctor_set(v___x_1438_, 9, v___y_1433_);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
v___jp_1441_:
{
lean_object* v___x_1446_; 
v___x_1446_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1374_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v___x_1447_; 
lean_dec_ref_known(v___x_1446_, 1);
lean_inc(v_declName_1372_);
v___x_1447_ = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(v_declName_1372_, v___x_1440_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1481_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1481_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1481_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
if (lean_obj_tag(v_a_1448_) == 1)
{
lean_object* v_val_1452_; lean_object* v_config_1453_; lean_object* v_identity_1454_; lean_object* v_extensions_1455_; lean_object* v_extra_1456_; lean_object* v_extraInj_1457_; lean_object* v_extraFacts_1458_; lean_object* v_symPrios_1459_; lean_object* v_norm_1460_; lean_object* v_normProcs_1461_; lean_object* v_anchorRefs_x3f_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_declName_1372_);
v_val_1452_ = lean_ctor_get(v_a_1448_, 0);
lean_inc(v_val_1452_);
lean_dec_ref_known(v_a_1448_, 1);
v_config_1453_ = lean_ctor_get(v_params_1370_, 0);
v_identity_1454_ = lean_ctor_get(v_params_1370_, 1);
v_extensions_1455_ = lean_ctor_get(v_params_1370_, 2);
v_extra_1456_ = lean_ctor_get(v_params_1370_, 3);
v_extraInj_1457_ = lean_ctor_get(v_params_1370_, 4);
v_extraFacts_1458_ = lean_ctor_get(v_params_1370_, 5);
v_symPrios_1459_ = lean_ctor_get(v_params_1370_, 6);
v_norm_1460_ = lean_ctor_get(v_params_1370_, 7);
v_normProcs_1461_ = lean_ctor_get(v_params_1370_, 8);
v_anchorRefs_x3f_1462_ = lean_ctor_get(v_params_1370_, 9);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_params_1370_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1464_ = v_params_1370_;
v_isShared_1465_ = v_isSharedCheck_1474_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_anchorRefs_x3f_1462_);
lean_inc(v_normProcs_1461_);
lean_inc(v_norm_1460_);
lean_inc(v_symPrios_1459_);
lean_inc(v_extraFacts_1458_);
lean_inc(v_extraInj_1457_);
lean_inc(v_extra_1456_);
lean_inc(v_extensions_1455_);
lean_inc(v_identity_1454_);
lean_inc(v_config_1453_);
lean_dec(v_params_1370_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1474_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1469_; 
v___x_1466_ = l_Lean_Array_toPArray_x27___redArg(v_val_1452_);
lean_dec(v_val_1452_);
v___x_1467_ = l_Lean_PersistentArray_append___redArg(v_extra_1456_, v___x_1466_);
lean_dec_ref(v___x_1466_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 3, v___x_1467_);
v___x_1469_ = v___x_1464_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_config_1453_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_identity_1454_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v_extensions_1455_);
lean_ctor_set(v_reuseFailAlloc_1473_, 3, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1473_, 4, v_extraInj_1457_);
lean_ctor_set(v_reuseFailAlloc_1473_, 5, v_extraFacts_1458_);
lean_ctor_set(v_reuseFailAlloc_1473_, 6, v_symPrios_1459_);
lean_ctor_set(v_reuseFailAlloc_1473_, 7, v_norm_1460_);
lean_ctor_set(v_reuseFailAlloc_1473_, 8, v_normProcs_1461_);
lean_ctor_set(v_reuseFailAlloc_1473_, 9, v_anchorRefs_x3f_1462_);
v___x_1469_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1471_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1469_);
v___x_1471_ = v___x_1450_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_del_object(v___x_1450_);
lean_dec(v_a_1448_);
lean_dec_ref(v_params_1370_);
v___x_1475_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__1, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
v___x_1476_ = l_Lean_MessageData_ofConstName(v_declName_1372_, v___x_1440_);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1479_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
return v___x_1480_;
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_declName_1372_);
lean_dec_ref(v_params_1370_);
v_a_1482_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1447_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1447_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_declName_1372_);
lean_dec_ref(v_params_1370_);
v_a_1490_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1446_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1446_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
v___jp_1498_:
{
uint8_t v___x_1503_; 
v___x_1503_ = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(v_kind_1373_);
if (v___x_1503_ == 0)
{
uint8_t v___x_1504_; 
v___x_1504_ = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(v_kind_1373_);
lean_dec(v_kind_1373_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v_params_1370_);
v___x_1505_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1506_ = l_Lean_MessageData_ofConstName(v_declName_1372_, v___x_1440_);
v___x_1507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__5, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1509_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
else
{
v___y_1442_ = v___y_1499_;
v___y_1443_ = v___y_1500_;
v___y_1444_ = v___y_1501_;
v___y_1445_ = v___y_1502_;
goto v___jp_1441_;
}
}
else
{
lean_dec(v_kind_1373_);
v___y_1442_ = v___y_1499_;
v___y_1443_ = v___y_1500_;
v___y_1444_ = v___y_1501_;
v___y_1445_ = v___y_1502_;
goto v___jp_1441_;
}
}
v___jp_1519_:
{
lean_object* v_symPrios_1524_; lean_object* v___x_1525_; 
v_symPrios_1524_ = lean_ctor_get(v_params_1370_, 6);
lean_inc_ref(v_symPrios_1524_);
lean_inc(v_declName_1372_);
v___x_1525_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1372_, v_kind_1373_, v_symPrios_1524_, v___x_1440_, v_minIndexable_1374_, v___y_1523_, v___y_1520_, v___y_1522_, v___y_1521_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref_known(v___x_1525_, 1);
v_thm_1404_ = v_a_1526_;
v___y_1405_ = v___y_1523_;
v___y_1406_ = v___y_1520_;
v___y_1407_ = v___y_1522_;
v___y_1408_ = v___y_1521_;
goto v___jp_1403_;
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_declName_1372_);
lean_dec_ref(v_params_1370_);
v_a_1527_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1525_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1525_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
v___jp_1535_:
{
if (v_suggest_1375_ == 0)
{
lean_dec(v_id_1371_);
v___y_1520_ = v___y_1537_;
v___y_1521_ = v___y_1539_;
v___y_1522_ = v___y_1538_;
v___y_1523_ = v___y_1536_;
goto v___jp_1519_;
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1540_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1538_);
v___x_1541_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1542_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_1540_, v___x_1541_);
lean_dec_ref(v___x_1540_);
if (v___x_1542_ == 0)
{
lean_object* v_symPrios_1543_; lean_object* v___x_1544_; 
lean_dec(v_kind_1373_);
v_symPrios_1543_ = lean_ctor_get(v_params_1370_, 6);
lean_inc_ref(v_symPrios_1543_);
lean_inc(v_declName_1372_);
v___x_1544_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1371_, v_declName_1372_, v_symPrios_1543_, v_minIndexable_1374_, v_suggest_1375_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v_thm_1404_ = v_a_1545_;
v___y_1405_ = v___y_1536_;
v___y_1406_ = v___y_1537_;
v___y_1407_ = v___y_1538_;
v___y_1408_ = v___y_1539_;
goto v___jp_1403_;
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_declName_1372_);
lean_dec_ref(v_params_1370_);
v_a_1546_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1544_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1544_);
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
else
{
lean_dec(v_id_1371_);
v___y_1520_ = v___y_1537_;
v___y_1521_ = v___y_1539_;
v___y_1522_ = v___y_1538_;
v___y_1523_ = v___y_1536_;
goto v___jp_1519_;
}
}
}
v___jp_1554_:
{
lean_object* v___x_1559_; 
v___x_1559_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1374_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1555_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_dec_ref_known(v___x_1559_, 1);
v___y_1536_ = v___y_1556_;
v___y_1537_ = v___y_1557_;
v___y_1538_ = v___y_1558_;
v___y_1539_ = v___y_1555_;
goto v___jp_1535_;
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_kind_1373_);
lean_dec(v_declName_1372_);
lean_dec(v_id_1371_);
lean_dec_ref(v_params_1370_);
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
v___jp_1568_:
{
if (lean_obj_tag(v_kind_1373_) == 2)
{
uint8_t v_gen_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_id_1371_);
v_gen_1573_ = lean_ctor_get_uint8(v_kind_1373_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_kind_1373_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1575_ = v_kind_1373_;
v_isShared_1576_ = v_isSharedCheck_1638_;
goto v_resetjp_1574_;
}
else
{
lean_dec(v_kind_1373_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1638_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; 
v___x_1577_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1374_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_config_1578_; lean_object* v_identity_1579_; lean_object* v_extensions_1580_; lean_object* v_extra_1581_; lean_object* v_extraInj_1582_; lean_object* v_extraFacts_1583_; lean_object* v_symPrios_1584_; lean_object* v_norm_1585_; lean_object* v_normProcs_1586_; lean_object* v_anchorRefs_x3f_1587_; lean_object* v___x_1589_; 
lean_dec_ref_known(v___x_1577_, 1);
v_config_1578_ = lean_ctor_get(v_params_1370_, 0);
lean_inc_ref(v_config_1578_);
v_identity_1579_ = lean_ctor_get(v_params_1370_, 1);
lean_inc(v_identity_1579_);
v_extensions_1580_ = lean_ctor_get(v_params_1370_, 2);
lean_inc_ref(v_extensions_1580_);
v_extra_1581_ = lean_ctor_get(v_params_1370_, 3);
lean_inc_ref(v_extra_1581_);
v_extraInj_1582_ = lean_ctor_get(v_params_1370_, 4);
lean_inc_ref(v_extraInj_1582_);
v_extraFacts_1583_ = lean_ctor_get(v_params_1370_, 5);
lean_inc_ref(v_extraFacts_1583_);
v_symPrios_1584_ = lean_ctor_get(v_params_1370_, 6);
lean_inc_ref(v_symPrios_1584_);
v_norm_1585_ = lean_ctor_get(v_params_1370_, 7);
lean_inc_ref(v_norm_1585_);
v_normProcs_1586_ = lean_ctor_get(v_params_1370_, 8);
lean_inc_ref(v_normProcs_1586_);
v_anchorRefs_x3f_1587_ = lean_ctor_get(v_params_1370_, 9);
lean_inc(v_anchorRefs_x3f_1587_);
lean_dec_ref(v_params_1370_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 0);
v___x_1589_ = v___x_1575_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_1629_, 0, v_gen_1573_);
v___x_1589_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; 
lean_inc_ref(v_symPrios_1584_);
lean_inc(v_declName_1372_);
v___x_1590_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1372_, v___x_1589_, v_symPrios_1584_, v___x_1440_, v___x_1440_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v___x_1592_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1592_, 0, v_gen_1573_);
lean_inc_ref(v_symPrios_1584_);
lean_inc(v_declName_1372_);
v___x_1593_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1372_, v___x_1592_, v_symPrios_1584_, v___x_1440_, v___x_1440_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1593_) == 0)
{
if (v_warn_1376_ == 0)
{
lean_object* v_a_1594_; 
lean_dec(v_declName_1372_);
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v___y_1424_ = v_extraFacts_1583_;
v___y_1425_ = v_symPrios_1584_;
v___y_1426_ = v_extensions_1580_;
v___y_1427_ = v_identity_1579_;
v___y_1428_ = v_norm_1585_;
v___y_1429_ = v_extraInj_1582_;
v___y_1430_ = v_a_1594_;
v___y_1431_ = v_normProcs_1586_;
v___y_1432_ = v_config_1578_;
v___y_1433_ = v_anchorRefs_x3f_1587_;
v___y_1434_ = v_a_1591_;
v___y_1435_ = v_extra_1581_;
goto v___jp_1423_;
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
lean_dec(v_declName_1372_);
v___y_1424_ = v_extraFacts_1583_;
v___y_1425_ = v_symPrios_1584_;
v___y_1426_ = v_extensions_1580_;
v___y_1427_ = v_identity_1579_;
v___y_1428_ = v_norm_1585_;
v___y_1429_ = v_extraInj_1582_;
v___y_1430_ = v_a_1595_;
v___y_1431_ = v_normProcs_1586_;
v___y_1432_ = v_config_1578_;
v___y_1433_ = v_anchorRefs_x3f_1587_;
v___y_1434_ = v_a_1591_;
v___y_1435_ = v_extra_1581_;
goto v___jp_1423_;
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
lean_dec(v_declName_1372_);
v___y_1424_ = v_extraFacts_1583_;
v___y_1425_ = v_symPrios_1584_;
v___y_1426_ = v_extensions_1580_;
v___y_1427_ = v_identity_1579_;
v___y_1428_ = v_norm_1585_;
v___y_1429_ = v_extraInj_1582_;
v___y_1430_ = v_a_1595_;
v___y_1431_ = v_normProcs_1586_;
v___y_1432_ = v_config_1578_;
v___y_1433_ = v_anchorRefs_x3f_1587_;
v___y_1434_ = v_a_1591_;
v___y_1435_ = v_extra_1581_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1604_; 
v___x_1604_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1580_, v_declName_1372_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_dec_ref_known(v___x_1604_, 1);
v___y_1424_ = v_extraFacts_1583_;
v___y_1425_ = v_symPrios_1584_;
v___y_1426_ = v_extensions_1580_;
v___y_1427_ = v_identity_1579_;
v___y_1428_ = v_norm_1585_;
v___y_1429_ = v_extraInj_1582_;
v___y_1430_ = v_a_1595_;
v___y_1431_ = v_normProcs_1586_;
v___y_1432_ = v_config_1578_;
v___y_1433_ = v_anchorRefs_x3f_1587_;
v___y_1434_ = v_a_1591_;
v___y_1435_ = v_extra_1581_;
goto v___jp_1423_;
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
lean_dec(v_identity_1579_);
lean_dec_ref(v_config_1578_);
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
lean_dec(v_identity_1579_);
lean_dec_ref(v_config_1578_);
lean_dec(v_declName_1372_);
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
lean_dec(v_identity_1579_);
lean_dec_ref(v_config_1578_);
lean_dec(v_declName_1372_);
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
lean_del_object(v___x_1575_);
lean_dec(v_declName_1372_);
lean_dec_ref(v_params_1370_);
v_a_1630_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1577_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1577_);
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
switch(lean_obj_tag(v_kind_1373_))
{
case 0:
{
v___y_1555_ = v___y_1572_;
v___y_1556_ = v___y_1569_;
v___y_1557_ = v___y_1570_;
v___y_1558_ = v___y_1571_;
goto v___jp_1554_;
}
case 1:
{
v___y_1555_ = v___y_1572_;
v___y_1556_ = v___y_1569_;
v___y_1557_ = v___y_1570_;
v___y_1558_ = v___y_1571_;
goto v___jp_1554_;
}
default: 
{
v___y_1536_ = v___y_1569_;
v___y_1537_ = v___y_1570_;
v___y_1538_ = v___y_1571_;
v___y_1539_ = v___y_1572_;
goto v___jp_1535_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(lean_object* v_declName_1803_, lean_object* v_symPrios_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
uint8_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = 0;
lean_inc(v_declName_1803_);
v___x_1811_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1803_, v___x_1810_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1884_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1884_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1884_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
uint8_t v_kind_1881_; 
v_kind_1881_ = lean_ctor_get_uint8(v_a_1812_, sizeof(void*)*3);
switch(v_kind_1881_)
{
case 1:
{
goto v___jp_1816_;
}
case 2:
{
goto v___jp_1816_;
}
case 6:
{
goto v___jp_1816_;
}
default: 
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_del_object(v___x_1814_);
lean_dec(v_a_1812_);
lean_dec_ref(v_symPrios_1804_);
lean_dec(v_declName_1803_);
v___x_1882_ = lean_box(v___x_1810_);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
}
v___jp_1816_:
{
lean_object* v___x_1817_; lean_object* v_levelParams_1818_; lean_object* v_type_1819_; uint8_t v___x_1820_; 
v___x_1817_ = l_Lean_AsyncConstantInfo_toConstantVal(v_a_1812_);
v_levelParams_1818_ = lean_ctor_get(v___x_1817_, 1);
lean_inc(v_levelParams_1818_);
v_type_1819_ = lean_ctor_get(v___x_1817_, 2);
lean_inc_ref(v_type_1819_);
lean_dec_ref(v___x_1817_);
v___x_1820_ = l_List_isEmpty___redArg(v_levelParams_1818_);
lean_dec(v_levelParams_1818_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
lean_dec_ref(v_type_1819_);
lean_dec_ref(v_symPrios_1804_);
lean_dec(v_declName_1803_);
v___x_1821_ = lean_box(v___x_1810_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1821_);
v___x_1823_ = v___x_1814_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
else
{
lean_object* v___x_1825_; 
lean_del_object(v___x_1814_);
lean_inc_ref(v_type_1819_);
v___x_1825_ = l_Lean_Meta_whnfR(v_type_1819_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1872_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1872_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1872_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
uint8_t v___x_1830_; 
v___x_1830_ = l_Lean_Expr_isForall(v_a_1826_);
lean_dec(v_a_1826_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; 
lean_del_object(v___x_1828_);
v___x_1831_ = l_Lean_Meta_isProp(v_type_1819_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1867_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1867_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1867_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
uint8_t v___x_1836_; 
v___x_1836_ = lean_unbox(v_a_1832_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_symPrios_1804_);
lean_dec(v_declName_1803_);
v___x_1837_ = lean_box(v___x_1810_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1837_);
v___x_1839_ = v___x_1834_;
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
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_del_object(v___x_1834_);
lean_inc(v_declName_1803_);
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_declName_1803_);
v___x_1842_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__0));
v___x_1843_ = lean_box(0);
v___x_1844_ = l_Lean_mkConst(v_declName_1803_, v___x_1843_);
v___x_1845_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v___x_1846_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_1841_, v___x_1842_, v___x_1844_, v___x_1845_, v_symPrios_1804_, v___x_1820_, v___x_1810_, v___x_1810_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1858_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1858_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1858_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
if (lean_obj_tag(v_a_1847_) == 0)
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v_a_1832_);
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1832_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_dec_ref_known(v_a_1847_, 1);
lean_dec(v_a_1832_);
v___x_1854_ = lean_box(v___x_1830_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1854_);
v___x_1856_ = v___x_1849_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1832_);
v_a_1859_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1846_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1846_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
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
}
}
else
{
lean_dec_ref(v_symPrios_1804_);
lean_dec(v_declName_1803_);
return v___x_1831_;
}
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
lean_dec_ref(v_type_1819_);
lean_dec_ref(v_symPrios_1804_);
lean_dec(v_declName_1803_);
v___x_1868_ = lean_box(v___x_1810_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1868_);
v___x_1870_ = v___x_1828_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec_ref(v_type_1819_);
lean_dec_ref(v_symPrios_1804_);
lean_dec(v_declName_1803_);
v_a_1873_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1825_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1825_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec_ref(v_symPrios_1804_);
lean_dec(v_declName_1803_);
v_a_1885_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1811_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1811_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___boxed(lean_object* v_declName_1893_, lean_object* v_symPrios_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(v_declName_1893_, v_symPrios_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(lean_object* v_params_1901_, lean_object* v_declName_1902_, uint8_t v_minIndexable_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1936_; 
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v___x_1909_, 0);
lean_dec(v_unused_1937_);
v___x_1911_ = v___x_1909_;
v_isShared_1912_ = v_isSharedCheck_1936_;
goto v_resetjp_1910_;
}
else
{
lean_dec(v___x_1909_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1936_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v_config_1913_; lean_object* v_identity_1914_; lean_object* v_extensions_1915_; lean_object* v_extra_1916_; lean_object* v_extraInj_1917_; lean_object* v_extraFacts_1918_; lean_object* v_symPrios_1919_; lean_object* v_norm_1920_; lean_object* v_normProcs_1921_; lean_object* v_anchorRefs_x3f_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1935_; 
v_config_1913_ = lean_ctor_get(v_params_1901_, 0);
v_identity_1914_ = lean_ctor_get(v_params_1901_, 1);
v_extensions_1915_ = lean_ctor_get(v_params_1901_, 2);
v_extra_1916_ = lean_ctor_get(v_params_1901_, 3);
v_extraInj_1917_ = lean_ctor_get(v_params_1901_, 4);
v_extraFacts_1918_ = lean_ctor_get(v_params_1901_, 5);
v_symPrios_1919_ = lean_ctor_get(v_params_1901_, 6);
v_norm_1920_ = lean_ctor_get(v_params_1901_, 7);
v_normProcs_1921_ = lean_ctor_get(v_params_1901_, 8);
v_anchorRefs_x3f_1922_ = lean_ctor_get(v_params_1901_, 9);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_params_1901_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1924_ = v_params_1901_;
v_isShared_1925_ = v_isSharedCheck_1935_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_anchorRefs_x3f_1922_);
lean_inc(v_normProcs_1921_);
lean_inc(v_norm_1920_);
lean_inc(v_symPrios_1919_);
lean_inc(v_extraFacts_1918_);
lean_inc(v_extraInj_1917_);
lean_inc(v_extra_1916_);
lean_inc(v_extensions_1915_);
lean_inc(v_identity_1914_);
lean_inc(v_config_1913_);
lean_dec(v_params_1901_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1935_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1926_ = lean_box(0);
v___x_1927_ = l_Lean_mkConst(v_declName_1902_, v___x_1926_);
v___x_1928_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_1918_, v___x_1927_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 5, v___x_1928_);
v___x_1930_ = v___x_1924_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_config_1913_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_identity_1914_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v_extensions_1915_);
lean_ctor_set(v_reuseFailAlloc_1934_, 3, v_extra_1916_);
lean_ctor_set(v_reuseFailAlloc_1934_, 4, v_extraInj_1917_);
lean_ctor_set(v_reuseFailAlloc_1934_, 5, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1934_, 6, v_symPrios_1919_);
lean_ctor_set(v_reuseFailAlloc_1934_, 7, v_norm_1920_);
lean_ctor_set(v_reuseFailAlloc_1934_, 8, v_normProcs_1921_);
lean_ctor_set(v_reuseFailAlloc_1934_, 9, v_anchorRefs_x3f_1922_);
v___x_1930_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1932_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1930_);
v___x_1932_ = v___x_1911_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_declName_1902_);
lean_dec_ref(v_params_1901_);
v_a_1938_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1909_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1909_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact___boxed(lean_object* v_params_1946_, lean_object* v_declName_1947_, lean_object* v_minIndexable_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
uint8_t v_minIndexable_boxed_1954_; lean_object* v_res_1955_; 
v_minIndexable_boxed_1954_ = lean_unbox(v_minIndexable_1948_);
v_res_1955_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(v_params_1946_, v_declName_1947_, v_minIndexable_boxed_1954_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1958_, lean_object* v_val_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v_config_1963_; lean_object* v_identity_1964_; lean_object* v_extensions_1965_; lean_object* v_extra_1966_; lean_object* v_extraInj_1967_; lean_object* v_extraFacts_1968_; lean_object* v_symPrios_1969_; lean_object* v_norm_1970_; lean_object* v_normProcs_1971_; lean_object* v_anchorRefs_x3f_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2002_; 
v_config_1963_ = lean_ctor_get(v_params_1958_, 0);
v_identity_1964_ = lean_ctor_get(v_params_1958_, 1);
v_extensions_1965_ = lean_ctor_get(v_params_1958_, 2);
v_extra_1966_ = lean_ctor_get(v_params_1958_, 3);
v_extraInj_1967_ = lean_ctor_get(v_params_1958_, 4);
v_extraFacts_1968_ = lean_ctor_get(v_params_1958_, 5);
v_symPrios_1969_ = lean_ctor_get(v_params_1958_, 6);
v_norm_1970_ = lean_ctor_get(v_params_1958_, 7);
v_normProcs_1971_ = lean_ctor_get(v_params_1958_, 8);
v_anchorRefs_x3f_1972_ = lean_ctor_get(v_params_1958_, 9);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_params_1958_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1974_ = v_params_1958_;
v_isShared_1975_ = v_isSharedCheck_2002_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_anchorRefs_x3f_1972_);
lean_inc(v_normProcs_1971_);
lean_inc(v_norm_1970_);
lean_inc(v_symPrios_1969_);
lean_inc(v_extraFacts_1968_);
lean_inc(v_extraInj_1967_);
lean_inc(v_extra_1966_);
lean_inc(v_extensions_1965_);
lean_inc(v_identity_1964_);
lean_inc(v_config_1963_);
lean_dec(v_params_1958_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2002_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___y_1977_; 
if (lean_obj_tag(v_anchorRefs_x3f_1972_) == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_1977_ = v___x_2000_;
goto v___jp_1976_;
}
else
{
lean_object* v_val_2001_; 
v_val_2001_ = lean_ctor_get(v_anchorRefs_x3f_1972_, 0);
lean_inc(v_val_2001_);
lean_dec_ref_known(v_anchorRefs_x3f_1972_, 1);
v___y_1977_ = v_val_2001_;
goto v___jp_1976_;
}
v___jp_1976_:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1959_, v_a_1960_, v_a_1961_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1991_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_1991_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1991_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1983_ = lean_array_push(v___y_1977_, v_a_1979_);
v___x_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 9, v___x_1984_);
v___x_1986_ = v___x_1974_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_config_1963_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_identity_1964_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_extensions_1965_);
lean_ctor_set(v_reuseFailAlloc_1990_, 3, v_extra_1966_);
lean_ctor_set(v_reuseFailAlloc_1990_, 4, v_extraInj_1967_);
lean_ctor_set(v_reuseFailAlloc_1990_, 5, v_extraFacts_1968_);
lean_ctor_set(v_reuseFailAlloc_1990_, 6, v_symPrios_1969_);
lean_ctor_set(v_reuseFailAlloc_1990_, 7, v_norm_1970_);
lean_ctor_set(v_reuseFailAlloc_1990_, 8, v_normProcs_1971_);
lean_ctor_set(v_reuseFailAlloc_1990_, 9, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1988_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1986_);
v___x_1988_ = v___x_1981_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec_ref(v___y_1977_);
lean_del_object(v___x_1974_);
lean_dec_ref(v_normProcs_1971_);
lean_dec_ref(v_norm_1970_);
lean_dec_ref(v_symPrios_1969_);
lean_dec_ref(v_extraFacts_1968_);
lean_dec_ref(v_extraInj_1967_);
lean_dec_ref(v_extra_1966_);
lean_dec_ref(v_extensions_1965_);
lean_dec(v_identity_1964_);
lean_dec_ref(v_config_1963_);
v_a_1992_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1978_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1978_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_2003_, lean_object* v_val_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_2003_, v_val_2004_, v_a_2005_, v_a_2006_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_val_2004_);
return v_res_2008_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_2011_ = l_Lean_stringToMessageData(v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_config_2016_; uint8_t v_revert_2017_; 
v_config_2016_ = lean_ctor_get(v_params_2012_, 0);
v_revert_2017_ = lean_ctor_get_uint8(v_config_2016_, sizeof(void*)*17 + 31);
if (v_revert_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_box(0);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_2021_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_2020_, v_a_2013_, v_a_2014_);
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec_ref(v_params_2022_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_2027_, lean_object* v___y_2028_){
_start:
{
uint8_t v___x_2030_; 
v___x_2030_ = l_Lean_Expr_hasMVar(v_e_2027_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; 
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v_e_2027_);
return v___x_2031_;
}
else
{
lean_object* v___x_2032_; lean_object* v_mctx_2033_; lean_object* v___x_2034_; lean_object* v_fst_2035_; lean_object* v_snd_2036_; lean_object* v___x_2037_; lean_object* v_cache_2038_; lean_object* v_zetaDeltaFVarIds_2039_; lean_object* v_postponed_2040_; lean_object* v_diag_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2050_; 
v___x_2032_ = lean_st_ref_get(v___y_2028_);
v_mctx_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc_ref(v_mctx_2033_);
lean_dec(v___x_2032_);
v___x_2034_ = l_Lean_instantiateMVarsCore(v_mctx_2033_, v_e_2027_);
v_fst_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_fst_2035_);
v_snd_2036_ = lean_ctor_get(v___x_2034_, 1);
lean_inc(v_snd_2036_);
lean_dec_ref(v___x_2034_);
v___x_2037_ = lean_st_ref_take(v___y_2028_);
v_cache_2038_ = lean_ctor_get(v___x_2037_, 1);
v_zetaDeltaFVarIds_2039_ = lean_ctor_get(v___x_2037_, 2);
v_postponed_2040_ = lean_ctor_get(v___x_2037_, 3);
v_diag_2041_ = lean_ctor_get(v___x_2037_, 4);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v___x_2037_, 0);
lean_dec(v_unused_2051_);
v___x_2043_ = v___x_2037_;
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_diag_2041_);
lean_inc(v_postponed_2040_);
lean_inc(v_zetaDeltaFVarIds_2039_);
lean_inc(v_cache_2038_);
lean_dec(v___x_2037_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v_snd_2036_);
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_snd_2036_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_cache_2038_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_zetaDeltaFVarIds_2039_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_postponed_2040_);
lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_diag_2041_);
v___x_2046_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_st_ref_put(v___y_2028_, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v_fst_2035_);
return v___x_2048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_2052_, v___y_2053_);
lean_dec(v___y_2053_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_2056_, v___y_2060_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(uint8_t v___x_2074_, uint8_t v___x_2075_, uint8_t v_____do__lift_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
if (v_____do__lift_2076_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_box(v___x_2074_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
return v___x_2085_;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_box(v___x_2075_);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v___x_2088_, lean_object* v___x_2089_, lean_object* v_____do__lift_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
uint8_t v___x_14806__boxed_2098_; uint8_t v___x_14807__boxed_2099_; uint8_t v_____do__lift_14808__boxed_2100_; lean_object* v_res_2101_; 
v___x_14806__boxed_2098_ = lean_unbox(v___x_2088_);
v___x_14807__boxed_2099_ = lean_unbox(v___x_2089_);
v_____do__lift_14808__boxed_2100_ = lean_unbox(v_____do__lift_2090_);
v_res_2101_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_14806__boxed_2098_, v___x_14807__boxed_2099_, v_____do__lift_14808__boxed_2100_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(uint8_t v___x_2102_, uint8_t v___x_2103_, lean_object* v_as_2104_, size_t v_i_2105_, size_t v_stop_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
uint8_t v___x_2112_; 
v___x_2112_ = lean_usize_dec_eq(v_i_2105_, v_stop_2106_);
if (v___x_2112_ == 0)
{
uint8_t v___x_2113_; uint8_t v_a_2115_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2113_ = 1;
v___x_2121_ = lean_array_uget_borrowed(v_as_2104_, v_i_2105_);
lean_inc(v___x_2121_);
v___x_2122_ = l_Lean_Meta_isProof(v___x_2121_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; uint8_t v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = lean_unbox(v_a_2123_);
lean_dec(v_a_2123_);
if (v___x_2124_ == 0)
{
v_a_2115_ = v___x_2102_;
goto v___jp_2114_;
}
else
{
v_a_2115_ = v___x_2103_;
goto v___jp_2114_;
}
}
else
{
return v___x_2122_;
}
v___jp_2114_:
{
if (v_a_2115_ == 0)
{
size_t v___x_2116_; size_t v___x_2117_; 
v___x_2116_ = ((size_t)1ULL);
v___x_2117_ = lean_usize_add(v_i_2105_, v___x_2116_);
v_i_2105_ = v___x_2117_;
goto _start;
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_box(v___x_2113_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
}
}
else
{
uint8_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = 0;
v___x_2126_ = lean_box(v___x_2125_);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v___x_2128_, lean_object* v___x_2129_, lean_object* v_as_2130_, lean_object* v_i_2131_, lean_object* v_stop_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
uint8_t v___x_14844__boxed_2138_; uint8_t v___x_14845__boxed_2139_; size_t v_i_boxed_2140_; size_t v_stop_boxed_2141_; lean_object* v_res_2142_; 
v___x_14844__boxed_2138_ = lean_unbox(v___x_2128_);
v___x_14845__boxed_2139_ = lean_unbox(v___x_2129_);
v_i_boxed_2140_ = lean_unbox_usize(v_i_2131_);
lean_dec(v_i_2131_);
v_stop_boxed_2141_ = lean_unbox_usize(v_stop_2132_);
lean_dec(v_stop_2132_);
v_res_2142_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_14844__boxed_2138_, v___x_14845__boxed_2139_, v_as_2130_, v_i_boxed_2140_, v_stop_boxed_2141_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v_as_2130_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_p_2143_, lean_object* v_term_2144_, lean_object* v___x_2145_, uint8_t v___x_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_toCold_2154_; lean_object* v_currRecDepth_2155_; lean_object* v_ref_2156_; uint16_t v_optionFlags_2157_; uint8_t v_suppressElabErrors_2158_; uint8_t v_checkDeprecated_2159_; uint8_t v_isRecordingDeps_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2257_; 
v_toCold_2154_ = lean_ctor_get(v___y_2151_, 0);
v_currRecDepth_2155_ = lean_ctor_get(v___y_2151_, 1);
v_ref_2156_ = lean_ctor_get(v___y_2151_, 2);
v_optionFlags_2157_ = lean_ctor_get_uint16(v___y_2151_, sizeof(void*)*3);
v_suppressElabErrors_2158_ = lean_ctor_get_uint8(v___y_2151_, sizeof(void*)*3 + 2);
v_checkDeprecated_2159_ = lean_ctor_get_uint8(v___y_2151_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2160_ = lean_ctor_get_uint8(v___y_2151_, sizeof(void*)*3 + 4);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___y_2151_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2162_ = v___y_2151_;
v_isShared_2163_ = v_isSharedCheck_2257_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_ref_2156_);
lean_inc(v_currRecDepth_2155_);
lean_inc(v_toCold_2154_);
lean_dec(v___y_2151_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2257_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_ref_2164_; lean_object* v___x_2166_; 
v_ref_2164_ = l_Lean_replaceRef(v_p_2143_, v_ref_2156_);
lean_dec(v_ref_2156_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 2, v_ref_2164_);
v___x_2166_ = v___x_2162_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_toCold_2154_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_currRecDepth_2155_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_ref_2164_);
lean_ctor_set_uint16(v_reuseFailAlloc_2256_, sizeof(void*)*3, v_optionFlags_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2256_, sizeof(void*)*3 + 2, v_suppressElabErrors_2158_);
lean_ctor_set_uint8(v_reuseFailAlloc_2256_, sizeof(void*)*3 + 3, v_checkDeprecated_2159_);
lean_ctor_set_uint8(v_reuseFailAlloc_2256_, sizeof(void*)*3 + 4, v_isRecordingDeps_2160_);
v___x_2166_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_Elab_Term_elabTerm(v_term_2144_, v___x_2145_, v___x_2146_, v___x_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___x_2166_, v___y_2152_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = 1;
v___x_2170_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_2169_, v___x_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___x_2166_, v___y_2152_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v___x_2171_; lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref_known(v___x_2170_, 1);
v___x_2171_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_2168_, v___y_2150_);
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2239_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2239_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
uint8_t v___x_2176_; 
v___x_2176_ = l_Lean_Expr_hasSyntheticSorry(v_a_2172_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2177_ = l_Lean_Expr_eta(v_a_2172_);
v___x_2178_ = l_Lean_Expr_hasMVar(v___x_2177_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
lean_dec_ref(v___x_2166_);
v___x_2179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__0));
v___x_2180_ = lean_box(v___x_2178_);
v___x_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2177_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2179_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2183_);
v___x_2185_ = v___x_2174_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
else
{
lean_object* v___x_2187_; 
lean_del_object(v___x_2174_);
v___x_2187_ = l_Lean_Meta_abstractMVars(v___x_2177_, v___x_2146_, v___y_2149_, v___y_2150_, v___x_2166_, v___y_2152_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2226_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2190_ = v___x_2187_;
v_isShared_2191_ = v_isSharedCheck_2226_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2226_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v_paramNames_2192_; lean_object* v_mvars_2193_; lean_object* v_expr_2194_; uint8_t v_a_2196_; lean_object* v___y_2205_; lean_object* v___x_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v_paramNames_2192_ = lean_ctor_get(v_a_2188_, 0);
lean_inc_ref(v_paramNames_2192_);
v_mvars_2193_ = lean_ctor_get(v_a_2188_, 1);
lean_inc_ref(v_mvars_2193_);
v_expr_2194_ = lean_ctor_get(v_a_2188_, 2);
lean_inc_ref(v_expr_2194_);
lean_dec(v_a_2188_);
v___x_2208_ = lean_unsigned_to_nat(0u);
v___x_2209_ = lean_array_get_size(v_mvars_2193_);
v___x_2210_ = lean_nat_dec_lt(v___x_2208_, v___x_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; 
lean_dec_ref(v_mvars_2193_);
v___x_2211_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2178_, v___x_2176_, v___x_2210_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___x_2166_, v___y_2152_);
lean_dec_ref(v___x_2166_);
v___y_2205_ = v___x_2211_;
goto v___jp_2204_;
}
else
{
if (v___x_2210_ == 0)
{
lean_dec_ref(v_mvars_2193_);
lean_dec_ref(v___x_2166_);
v_a_2196_ = v___x_2178_;
goto v___jp_2195_;
}
else
{
size_t v___x_2212_; size_t v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = ((size_t)0ULL);
v___x_2213_ = lean_usize_of_nat(v___x_2209_);
v___x_2214_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2178_, v___x_2176_, v_mvars_2193_, v___x_2212_, v___x_2213_, v___y_2149_, v___y_2150_, v___x_2166_, v___y_2152_);
lean_dec_ref(v_mvars_2193_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = lean_unbox(v_a_2215_);
lean_dec(v_a_2215_);
v___x_2217_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2178_, v___x_2176_, v___x_2216_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___x_2166_, v___y_2152_);
lean_dec_ref(v___x_2166_);
v___y_2205_ = v___x_2217_;
goto v___jp_2204_;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_expr_2194_);
lean_dec_ref(v_paramNames_2192_);
lean_del_object(v___x_2190_);
lean_dec_ref(v___x_2166_);
v_a_2218_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2214_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2214_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
v___jp_2195_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
v___x_2197_ = lean_box(v_a_2196_);
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v_expr_2194_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2199_, 0, v_paramNames_2192_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2200_);
v___x_2202_ = v___x_2190_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
v___jp_2204_:
{
lean_object* v_a_2206_; uint8_t v___x_2207_; 
v_a_2206_ = lean_ctor_get(v___y_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref(v___y_2205_);
v___x_2207_ = lean_unbox(v_a_2206_);
lean_dec(v_a_2206_);
v_a_2196_ = v___x_2207_;
goto v___jp_2195_;
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec_ref(v___x_2166_);
v_a_2227_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2187_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2187_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
lean_dec(v_a_2172_);
lean_dec_ref(v___x_2166_);
v___x_2235_ = lean_box(0);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2235_);
v___x_2237_ = v___x_2174_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_a_2168_);
lean_dec_ref(v___x_2166_);
v_a_2240_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2170_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2170_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec_ref(v___x_2166_);
v_a_2248_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2167_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2167_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_p_2258_, lean_object* v_term_2259_, lean_object* v___x_2260_, lean_object* v___x_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v___x_14901__boxed_2269_; lean_object* v_res_2270_; 
v___x_14901__boxed_2269_ = lean_unbox(v___x_2261_);
v_res_2270_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_p_2258_, v_term_2259_, v___x_2260_, v___x_14901__boxed_2269_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v_p_2258_);
return v_res_2270_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__2));
v___x_2276_ = l_Lean_stringToMessageData(v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(lean_object* v_params_2277_, lean_object* v_p_2278_, lean_object* v_fst_2279_, lean_object* v_fst_2280_, uint8_t v___x_2281_, uint8_t v_minIndexable_2282_, lean_object* v_kind_2283_, lean_object* v_idx_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_symPrios_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; 
v_symPrios_2290_ = lean_ctor_get(v_params_2277_, 6);
lean_inc_ref(v_symPrios_2290_);
lean_dec_ref(v_params_2277_);
v___x_2291_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__1));
v___x_2292_ = lean_name_append_index_after(v___x_2291_, v_idx_2284_);
v___x_2293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
lean_ctor_set(v___x_2293_, 1, v_p_2278_);
v___x_2294_ = 0;
v___x_2295_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2293_, v_fst_2279_, v_fst_2280_, v_kind_2283_, v_symPrios_2290_, v___x_2281_, v___x_2294_, v_minIndexable_2282_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2306_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2298_ = v___x_2295_;
v_isShared_2299_ = v_isSharedCheck_2306_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2306_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
if (lean_obj_tag(v_a_2296_) == 1)
{
lean_object* v_val_2300_; lean_object* v___x_2302_; 
v_val_2300_ = lean_ctor_get(v_a_2296_, 0);
lean_inc(v_val_2300_);
lean_dec_ref_known(v_a_2296_, 1);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v_val_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_val_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
else
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
lean_del_object(v___x_2298_);
lean_dec(v_a_2296_);
v___x_2304_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3);
v___x_2305_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2304_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
return v___x_2305_;
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
v_a_2307_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2295_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2295_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed(lean_object* v_params_2315_, lean_object* v_p_2316_, lean_object* v_fst_2317_, lean_object* v_fst_2318_, lean_object* v___x_2319_, lean_object* v_minIndexable_2320_, lean_object* v_kind_2321_, lean_object* v_idx_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
uint8_t v___x_15131__boxed_2328_; uint8_t v_minIndexable_boxed_2329_; lean_object* v_res_2330_; 
v___x_15131__boxed_2328_ = lean_unbox(v___x_2319_);
v_minIndexable_boxed_2329_ = lean_unbox(v_minIndexable_2320_);
v_res_2330_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(v_params_2315_, v_p_2316_, v_fst_2317_, v_fst_2318_, v___x_15131__boxed_2328_, v_minIndexable_boxed_2329_, v_kind_2321_, v_idx_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
return v_res_2330_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = lean_box(1);
v___x_2332_ = l_Lean_MessageData_ofFormat(v___x_2331_);
return v___x_2332_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__2));
v___x_2337_ = l_Lean_MessageData_ofFormat(v___x_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(lean_object* v_x_2338_, lean_object* v_x_2339_){
_start:
{
if (lean_obj_tag(v_x_2339_) == 0)
{
return v_x_2338_;
}
else
{
lean_object* v_head_2340_; lean_object* v_tail_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2363_; 
v_head_2340_ = lean_ctor_get(v_x_2339_, 0);
v_tail_2341_ = lean_ctor_get(v_x_2339_, 1);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_x_2339_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2343_ = v_x_2339_;
v_isShared_2344_ = v_isSharedCheck_2363_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_tail_2341_);
lean_inc(v_head_2340_);
lean_dec(v_x_2339_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2363_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_before_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2361_; 
v_before_2345_ = lean_ctor_get(v_head_2340_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_head_2340_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; 
v_unused_2362_ = lean_ctor_get(v_head_2340_, 1);
lean_dec(v_unused_2362_);
v___x_2347_ = v_head_2340_;
v_isShared_2348_ = v_isSharedCheck_2361_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_before_2345_);
lean_dec(v_head_2340_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2361_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2349_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2348_ == 0)
{
lean_ctor_set_tag(v___x_2347_, 7);
lean_ctor_set(v___x_2347_, 1, v___x_2349_);
lean_ctor_set(v___x_2347_, 0, v_x_2338_);
v___x_2351_ = v___x_2347_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_x_2338_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2352_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3);
if (v_isShared_2344_ == 0)
{
lean_ctor_set_tag(v___x_2343_, 7);
lean_ctor_set(v___x_2343_, 1, v___x_2352_);
lean_ctor_set(v___x_2343_, 0, v___x_2351_);
v___x_2354_ = v___x_2343_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = l_Lean_MessageData_ofSyntax(v_before_2345_);
v___x_2356_ = l_Lean_indentD(v___x_2355_);
v___x_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2354_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v_x_2338_ = v___x_2357_;
v_x_2339_ = v_tail_2341_;
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
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__1));
v___x_2368_ = l_Lean_MessageData_ofFormat(v___x_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(lean_object* v_msgData_2369_, lean_object* v_macroStack_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2373_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2371_);
v___x_2374_ = l_Lean_Elab_pp_macroStack;
v___x_2375_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_2373_, v___x_2374_);
lean_dec_ref(v___x_2373_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
lean_dec(v_macroStack_2370_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v_msgData_2369_);
return v___x_2376_;
}
else
{
if (lean_obj_tag(v_macroStack_2370_) == 0)
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v_msgData_2369_);
return v___x_2377_;
}
else
{
lean_object* v_head_2378_; lean_object* v_after_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2394_; 
v_head_2378_ = lean_ctor_get(v_macroStack_2370_, 0);
lean_inc(v_head_2378_);
v_after_2379_ = lean_ctor_get(v_head_2378_, 1);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_head_2378_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; 
v_unused_2395_ = lean_ctor_get(v_head_2378_, 0);
lean_dec(v_unused_2395_);
v___x_2381_ = v_head_2378_;
v_isShared_2382_ = v_isSharedCheck_2394_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_after_2379_);
lean_dec(v_head_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2394_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2383_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2382_ == 0)
{
lean_ctor_set_tag(v___x_2381_, 7);
lean_ctor_set(v___x_2381_, 1, v___x_2383_);
lean_ctor_set(v___x_2381_, 0, v_msgData_2369_);
v___x_2385_ = v___x_2381_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_msgData_2369_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v_msgData_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2386_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2);
v___x_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = l_Lean_MessageData_ofSyntax(v_after_2379_);
v___x_2389_ = l_Lean_indentD(v___x_2388_);
v_msgData_2390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2390_, 0, v___x_2387_);
lean_ctor_set(v_msgData_2390_, 1, v___x_2389_);
v___x_2391_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(v_msgData_2390_, v_macroStack_2370_);
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
return v___x_2392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_2396_, lean_object* v_macroStack_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2396_, v_macroStack_2397_, v___y_2398_);
lean_dec_ref(v___y_2398_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(lean_object* v_msg_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_ref_2409_; lean_object* v_macroStack_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v_a_2413_; lean_object* v___x_2414_; lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2423_; 
v_ref_2409_ = lean_ctor_get(v___y_2406_, 2);
v_macroStack_2410_ = lean_ctor_get(v___y_2402_, 1);
v___x_2411_ = l_Lean_Elab_getBetterRef(v_ref_2409_, v_macroStack_2410_);
v___x_2412_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2401_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref(v___x_2412_);
lean_inc(v_macroStack_2410_);
v___x_2414_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_a_2413_, v_macroStack_2410_, v___y_2406_);
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2423_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2423_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2411_);
lean_ctor_set(v___x_2419_, 1, v_a_2415_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set_tag(v___x_2417_, 1);
lean_ctor_set(v___x_2417_, 0, v___x_2419_);
v___x_2421_ = v___x_2417_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg___boxed(lean_object* v_msg_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2432_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2435_ = l_Lean_stringToMessageData(v___x_2434_);
return v___x_2435_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2438_ = l_Lean_stringToMessageData(v___x_2437_);
return v___x_2438_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2441_ = l_Lean_stringToMessageData(v___x_2440_);
return v___x_2441_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_2444_ = l_Lean_stringToMessageData(v___x_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2445_, lean_object* v_p_2446_, lean_object* v_mod_x3f_2447_, lean_object* v_term_2448_, uint8_t v_minIndexable_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v___y_2458_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; uint8_t v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2699_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v_kind_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v_toCold_2820_; lean_object* v_currRecDepth_2821_; lean_object* v_ref_2822_; uint16_t v_optionFlags_2823_; uint8_t v_suppressElabErrors_2824_; uint8_t v_checkDeprecated_2825_; uint8_t v_isRecordingDeps_2826_; lean_object* v_ref_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_toCold_2820_ = lean_ctor_get(v_a_2454_, 0);
v_currRecDepth_2821_ = lean_ctor_get(v_a_2454_, 1);
v_ref_2822_ = lean_ctor_get(v_a_2454_, 2);
v_optionFlags_2823_ = lean_ctor_get_uint16(v_a_2454_, sizeof(void*)*3);
v_suppressElabErrors_2824_ = lean_ctor_get_uint8(v_a_2454_, sizeof(void*)*3 + 2);
v_checkDeprecated_2825_ = lean_ctor_get_uint8(v_a_2454_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2826_ = lean_ctor_get_uint8(v_a_2454_, sizeof(void*)*3 + 4);
v_ref_2827_ = l_Lean_replaceRef(v_p_2446_, v_ref_2822_);
lean_inc(v_currRecDepth_2821_);
lean_inc_ref(v_toCold_2820_);
v___x_2828_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2828_, 0, v_toCold_2820_);
lean_ctor_set(v___x_2828_, 1, v_currRecDepth_2821_);
lean_ctor_set(v___x_2828_, 2, v_ref_2827_);
lean_ctor_set_uint16(v___x_2828_, sizeof(void*)*3, v_optionFlags_2823_);
lean_ctor_set_uint8(v___x_2828_, sizeof(void*)*3 + 2, v_suppressElabErrors_2824_);
lean_ctor_set_uint8(v___x_2828_, sizeof(void*)*3 + 3, v_checkDeprecated_2825_);
lean_ctor_set_uint8(v___x_2828_, sizeof(void*)*3 + 4, v_isRecordingDeps_2826_);
v___x_2829_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2445_, v___x_2828_, v_a_2455_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_dec_ref_known(v___x_2829_, 1);
if (lean_obj_tag(v_mod_x3f_2447_) == 1)
{
lean_object* v_val_2830_; lean_object* v___x_2831_; 
v_val_2830_ = lean_ctor_get(v_mod_x3f_2447_, 0);
lean_inc(v_val_2830_);
v___x_2831_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2830_, v___x_2828_, v_a_2455_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
switch(lean_obj_tag(v_a_2832_))
{
case 0:
{
lean_object* v_k_2833_; 
v_k_2833_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_k_2833_);
lean_dec_ref_known(v_a_2832_, 1);
if (lean_obj_tag(v_k_2833_) == 9)
{
lean_dec_ref_known(v_mod_x3f_2447_, 1);
lean_dec(v_term_2448_);
lean_dec(v_p_2446_);
lean_dec_ref(v_params_2445_);
v___y_2779_ = v_a_2450_;
v___y_2780_ = v_a_2451_;
v___y_2781_ = v_a_2452_;
v___y_2782_ = v_a_2453_;
v___y_2783_ = v___x_2828_;
v___y_2784_ = v_a_2455_;
goto v___jp_2778_;
}
else
{
v_kind_2710_ = v_k_2833_;
v___y_2711_ = v_a_2450_;
v___y_2712_ = v_a_2451_;
v___y_2713_ = v_a_2452_;
v___y_2714_ = v_a_2453_;
v___y_2715_ = v___x_2828_;
v___y_2716_ = v_a_2455_;
goto v___jp_2709_;
}
}
case 1:
{
lean_dec_ref_known(v_a_2832_, 0);
lean_dec_ref_known(v_mod_x3f_2447_, 1);
lean_dec(v_term_2448_);
lean_dec(v_p_2446_);
lean_dec_ref(v_params_2445_);
v___y_2796_ = v_a_2450_;
v___y_2797_ = v_a_2451_;
v___y_2798_ = v_a_2452_;
v___y_2799_ = v_a_2453_;
v___y_2800_ = v___x_2828_;
v___y_2801_ = v_a_2455_;
goto v___jp_2795_;
}
case 3:
{
v___y_2813_ = v_a_2450_;
v___y_2814_ = v_a_2451_;
v___y_2815_ = v_a_2452_;
v___y_2816_ = v_a_2453_;
v___y_2817_ = v___x_2828_;
v___y_2818_ = v_a_2455_;
goto v___jp_2812_;
}
case 5:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec_ref_known(v_a_2832_, 1);
lean_dec_ref_known(v_mod_x3f_2447_, 1);
lean_dec(v_term_2448_);
lean_dec(v_p_2446_);
lean_dec_ref(v_params_2445_);
v___x_2834_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2835_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2834_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v___x_2828_, v_a_2455_);
lean_dec_ref_known(v___x_2828_, 3);
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2835_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2835_);
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
case 8:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec_ref_known(v_a_2832_, 0);
lean_dec_ref_known(v_mod_x3f_2447_, 1);
lean_dec(v_term_2448_);
lean_dec(v_p_2446_);
lean_dec_ref(v_params_2445_);
v___x_2844_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2845_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2844_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v___x_2828_, v_a_2455_);
lean_dec_ref_known(v___x_2828_, 3);
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
case 10:
{
lean_dec_ref_known(v_a_2832_, 0);
lean_dec_ref_known(v_mod_x3f_2447_, 1);
lean_dec(v_term_2448_);
lean_dec(v_p_2446_);
lean_dec_ref(v_params_2445_);
v___y_2796_ = v_a_2450_;
v___y_2797_ = v_a_2451_;
v___y_2798_ = v_a_2452_;
v___y_2799_ = v_a_2453_;
v___y_2800_ = v___x_2828_;
v___y_2801_ = v_a_2455_;
goto v___jp_2795_;
}
default: 
{
lean_dec(v_a_2832_);
lean_dec_ref_known(v_mod_x3f_2447_, 1);
lean_dec(v_term_2448_);
lean_dec(v_p_2446_);
lean_dec_ref(v_params_2445_);
v___y_2779_ = v_a_2450_;
v___y_2780_ = v_a_2451_;
v___y_2781_ = v_a_2452_;
v___y_2782_ = v_a_2453_;
v___y_2783_ = v___x_2828_;
v___y_2784_ = v_a_2455_;
goto v___jp_2778_;
}
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec_ref_known(v_mod_x3f_2447_, 1);
lean_dec_ref_known(v___x_2828_, 3);
lean_dec(v_term_2448_);
lean_dec(v_p_2446_);
lean_dec_ref(v_params_2445_);
v_a_2854_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2831_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2831_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
else
{
v___y_2813_ = v_a_2450_;
v___y_2814_ = v_a_2451_;
v___y_2815_ = v_a_2452_;
v___y_2816_ = v_a_2453_;
v___y_2817_ = v___x_2828_;
v___y_2818_ = v_a_2455_;
goto v___jp_2812_;
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec_ref_known(v___x_2828_, 3);
lean_dec(v_term_2448_);
lean_dec(v_mod_x3f_2447_);
lean_dec(v_p_2446_);
lean_dec_ref(v_params_2445_);
v_a_2862_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2829_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2829_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
v___jp_2457_:
{
lean_object* v_config_2459_; lean_object* v_identity_2460_; lean_object* v_extensions_2461_; lean_object* v_extra_2462_; lean_object* v_extraInj_2463_; lean_object* v_extraFacts_2464_; lean_object* v_symPrios_2465_; lean_object* v_norm_2466_; lean_object* v_normProcs_2467_; lean_object* v_anchorRefs_x3f_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2477_; 
v_config_2459_ = lean_ctor_get(v_params_2445_, 0);
v_identity_2460_ = lean_ctor_get(v_params_2445_, 1);
v_extensions_2461_ = lean_ctor_get(v_params_2445_, 2);
v_extra_2462_ = lean_ctor_get(v_params_2445_, 3);
v_extraInj_2463_ = lean_ctor_get(v_params_2445_, 4);
v_extraFacts_2464_ = lean_ctor_get(v_params_2445_, 5);
v_symPrios_2465_ = lean_ctor_get(v_params_2445_, 6);
v_norm_2466_ = lean_ctor_get(v_params_2445_, 7);
v_normProcs_2467_ = lean_ctor_get(v_params_2445_, 8);
v_anchorRefs_x3f_2468_ = lean_ctor_get(v_params_2445_, 9);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_params_2445_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2470_ = v_params_2445_;
v_isShared_2471_ = v_isSharedCheck_2477_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_anchorRefs_x3f_2468_);
lean_inc(v_normProcs_2467_);
lean_inc(v_norm_2466_);
lean_inc(v_symPrios_2465_);
lean_inc(v_extraFacts_2464_);
lean_inc(v_extraInj_2463_);
lean_inc(v_extra_2462_);
lean_inc(v_extensions_2461_);
lean_inc(v_identity_2460_);
lean_inc(v_config_2459_);
lean_dec(v_params_2445_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2477_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2472_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2464_, v___y_2458_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 5, v___x_2472_);
v___x_2474_ = v___x_2470_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_config_2459_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_identity_2460_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_extensions_2461_);
lean_ctor_set(v_reuseFailAlloc_2476_, 3, v_extra_2462_);
lean_ctor_set(v_reuseFailAlloc_2476_, 4, v_extraInj_2463_);
lean_ctor_set(v_reuseFailAlloc_2476_, 5, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2476_, 6, v_symPrios_2465_);
lean_ctor_set(v_reuseFailAlloc_2476_, 7, v_norm_2466_);
lean_ctor_set(v_reuseFailAlloc_2476_, 8, v_normProcs_2467_);
lean_ctor_set(v_reuseFailAlloc_2476_, 9, v_anchorRefs_x3f_2468_);
v___x_2474_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
return v___x_2475_;
}
}
}
v___jp_2478_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v___x_2488_ = lean_array_get_size(v___y_2479_);
lean_dec_ref(v___y_2479_);
v___x_2489_ = lean_unsigned_to_nat(0u);
v___x_2490_ = lean_nat_dec_eq(v___x_2488_, v___x_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v___y_2480_);
lean_dec_ref(v_params_2445_);
v___x_2491_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2492_ = l_Lean_indentExpr(v___y_2481_);
v___x_2493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2493_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec_ref(v___y_2486_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
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
else
{
lean_dec_ref(v___y_2486_);
lean_dec_ref(v___y_2481_);
v___y_2458_ = v___y_2480_;
goto v___jp_2457_;
}
}
v___jp_2503_:
{
lean_object* v___x_2521_; 
lean_inc(v___y_2520_);
lean_inc(v___y_2518_);
lean_inc_ref(v___y_2517_);
v___x_2521_ = lean_apply_7(v___y_2514_, v___y_2506_, v___y_2504_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, lean_box(0));
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2531_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2531_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2531_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2526_ = l_Lean_PersistentArray_push___redArg(v___y_2507_, v_a_2522_);
v___x_2527_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2527_, 0, v___y_2511_);
lean_ctor_set(v___x_2527_, 1, v___y_2512_);
lean_ctor_set(v___x_2527_, 2, v___y_2510_);
lean_ctor_set(v___x_2527_, 3, v___x_2526_);
lean_ctor_set(v___x_2527_, 4, v___y_2505_);
lean_ctor_set(v___x_2527_, 5, v___y_2513_);
lean_ctor_set(v___x_2527_, 6, v___y_2509_);
lean_ctor_set(v___x_2527_, 7, v___y_2515_);
lean_ctor_set(v___x_2527_, 8, v___y_2516_);
lean_ctor_set(v___x_2527_, 9, v___y_2508_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2527_);
v___x_2529_ = v___x_2524_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec_ref(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec_ref(v___y_2505_);
v_a_2532_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2521_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2521_);
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
v___jp_2540_:
{
lean_object* v___x_2558_; 
v___x_2558_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2449_, v___y_2544_, v___y_2548_, v___y_2542_, v___y_2549_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_dec_ref_known(v___x_2558_, 1);
v___y_2504_ = v___y_2541_;
v___y_2505_ = v___y_2543_;
v___y_2506_ = v___y_2545_;
v___y_2507_ = v___y_2546_;
v___y_2508_ = v___y_2547_;
v___y_2509_ = v___y_2550_;
v___y_2510_ = v___y_2551_;
v___y_2511_ = v___y_2553_;
v___y_2512_ = v___y_2552_;
v___y_2513_ = v___y_2554_;
v___y_2514_ = v___y_2555_;
v___y_2515_ = v___y_2556_;
v___y_2516_ = v___y_2557_;
v___y_2517_ = v___y_2544_;
v___y_2518_ = v___y_2548_;
v___y_2519_ = v___y_2542_;
v___y_2520_ = v___y_2549_;
goto v___jp_2503_;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
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
v___jp_2567_:
{
lean_object* v_extra_2574_; 
v_extra_2574_ = lean_ctor_get(v_params_2445_, 3);
lean_inc_ref(v_extra_2574_);
if (lean_obj_tag(v___y_2570_) == 2)
{
lean_object* v_config_2575_; lean_object* v_identity_2576_; lean_object* v_extensions_2577_; lean_object* v_extraInj_2578_; lean_object* v_extraFacts_2579_; lean_object* v_symPrios_2580_; lean_object* v_norm_2581_; lean_object* v_normProcs_2582_; lean_object* v_anchorRefs_x3f_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2638_; 
v_config_2575_ = lean_ctor_get(v_params_2445_, 0);
v_identity_2576_ = lean_ctor_get(v_params_2445_, 1);
v_extensions_2577_ = lean_ctor_get(v_params_2445_, 2);
v_extraInj_2578_ = lean_ctor_get(v_params_2445_, 4);
v_extraFacts_2579_ = lean_ctor_get(v_params_2445_, 5);
v_symPrios_2580_ = lean_ctor_get(v_params_2445_, 6);
v_norm_2581_ = lean_ctor_get(v_params_2445_, 7);
v_normProcs_2582_ = lean_ctor_get(v_params_2445_, 8);
v_anchorRefs_x3f_2583_ = lean_ctor_get(v_params_2445_, 9);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_params_2445_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; 
v_unused_2639_ = lean_ctor_get(v_params_2445_, 3);
lean_dec(v_unused_2639_);
v___x_2585_ = v_params_2445_;
v_isShared_2586_ = v_isSharedCheck_2638_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_anchorRefs_x3f_2583_);
lean_inc(v_normProcs_2582_);
lean_inc(v_norm_2581_);
lean_inc(v_symPrios_2580_);
lean_inc(v_extraFacts_2579_);
lean_inc(v_extraInj_2578_);
lean_inc(v_extensions_2577_);
lean_inc(v_identity_2576_);
lean_inc(v_config_2575_);
lean_dec(v_params_2445_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2638_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v_size_2587_; uint8_t v_gen_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2637_; 
v_size_2587_ = lean_ctor_get(v_extra_2574_, 2);
v_gen_2588_ = lean_ctor_get_uint8(v___y_2570_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___y_2570_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2590_ = v___y_2570_;
v_isShared_2591_ = v_isSharedCheck_2637_;
goto v_resetjp_2589_;
}
else
{
lean_dec(v___y_2570_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2637_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; 
v___x_2592_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2449_, v___y_2569_, v___y_2571_, v___y_2568_, v___y_2573_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v___x_2594_; 
lean_dec_ref_known(v___x_2592_, 1);
if (v_isShared_2591_ == 0)
{
lean_ctor_set_tag(v___x_2590_, 0);
v___x_2594_ = v___x_2590_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2628_, 0, v_gen_2588_);
v___x_2594_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; 
lean_inc_ref(v___y_2572_);
lean_inc(v___y_2573_);
lean_inc_ref(v___y_2568_);
lean_inc(v___y_2571_);
lean_inc_ref(v___y_2569_);
lean_inc(v_size_2587_);
v___x_2595_ = lean_apply_7(v___y_2572_, v___x_2594_, v_size_2587_, v___y_2569_, v___y_2571_, v___y_2568_, v___y_2573_, lean_box(0));
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2597_, 0, v_gen_2588_);
lean_inc(v___y_2573_);
lean_inc(v___y_2571_);
lean_inc_ref(v___y_2569_);
lean_inc(v_size_2587_);
v___x_2598_ = lean_apply_7(v___y_2572_, v___x_2597_, v_size_2587_, v___y_2569_, v___y_2571_, v___y_2568_, v___y_2573_, lean_box(0));
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2611_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2611_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2611_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2603_ = l_Lean_PersistentArray_push___redArg(v_extra_2574_, v_a_2596_);
v___x_2604_ = l_Lean_PersistentArray_push___redArg(v___x_2603_, v_a_2599_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 3, v___x_2604_);
v___x_2606_ = v___x_2585_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_config_2575_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_identity_2576_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_extensions_2577_);
lean_ctor_set(v_reuseFailAlloc_2610_, 3, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_extraInj_2578_);
lean_ctor_set(v_reuseFailAlloc_2610_, 5, v_extraFacts_2579_);
lean_ctor_set(v_reuseFailAlloc_2610_, 6, v_symPrios_2580_);
lean_ctor_set(v_reuseFailAlloc_2610_, 7, v_norm_2581_);
lean_ctor_set(v_reuseFailAlloc_2610_, 8, v_normProcs_2582_);
lean_ctor_set(v_reuseFailAlloc_2610_, 9, v_anchorRefs_x3f_2583_);
v___x_2606_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2608_; 
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v___x_2606_);
v___x_2608_ = v___x_2601_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v_a_2596_);
lean_del_object(v___x_2585_);
lean_dec(v_anchorRefs_x3f_2583_);
lean_dec_ref(v_normProcs_2582_);
lean_dec_ref(v_norm_2581_);
lean_dec_ref(v_symPrios_2580_);
lean_dec_ref(v_extraFacts_2579_);
lean_dec_ref(v_extraInj_2578_);
lean_dec_ref(v_extensions_2577_);
lean_dec(v_identity_2576_);
lean_dec_ref(v_config_2575_);
lean_dec_ref(v_extra_2574_);
v_a_2612_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2598_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2598_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_del_object(v___x_2585_);
lean_dec(v_anchorRefs_x3f_2583_);
lean_dec_ref(v_normProcs_2582_);
lean_dec_ref(v_norm_2581_);
lean_dec_ref(v_symPrios_2580_);
lean_dec_ref(v_extraFacts_2579_);
lean_dec_ref(v_extraInj_2578_);
lean_dec_ref(v_extensions_2577_);
lean_dec(v_identity_2576_);
lean_dec_ref(v_config_2575_);
lean_dec_ref(v_extra_2574_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2568_);
v_a_2620_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2595_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2595_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_del_object(v___x_2590_);
lean_del_object(v___x_2585_);
lean_dec(v_anchorRefs_x3f_2583_);
lean_dec_ref(v_normProcs_2582_);
lean_dec_ref(v_norm_2581_);
lean_dec_ref(v_symPrios_2580_);
lean_dec_ref(v_extraFacts_2579_);
lean_dec_ref(v_extraInj_2578_);
lean_dec_ref(v_extensions_2577_);
lean_dec(v_identity_2576_);
lean_dec_ref(v_config_2575_);
lean_dec_ref(v_extra_2574_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2568_);
v_a_2629_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2592_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2592_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
}
else
{
switch(lean_obj_tag(v___y_2570_))
{
case 0:
{
lean_object* v_config_2640_; lean_object* v_identity_2641_; lean_object* v_extensions_2642_; lean_object* v_extraInj_2643_; lean_object* v_extraFacts_2644_; lean_object* v_symPrios_2645_; lean_object* v_norm_2646_; lean_object* v_normProcs_2647_; lean_object* v_anchorRefs_x3f_2648_; lean_object* v_size_2649_; 
v_config_2640_ = lean_ctor_get(v_params_2445_, 0);
lean_inc_ref(v_config_2640_);
v_identity_2641_ = lean_ctor_get(v_params_2445_, 1);
lean_inc(v_identity_2641_);
v_extensions_2642_ = lean_ctor_get(v_params_2445_, 2);
lean_inc_ref(v_extensions_2642_);
v_extraInj_2643_ = lean_ctor_get(v_params_2445_, 4);
lean_inc_ref(v_extraInj_2643_);
v_extraFacts_2644_ = lean_ctor_get(v_params_2445_, 5);
lean_inc_ref(v_extraFacts_2644_);
v_symPrios_2645_ = lean_ctor_get(v_params_2445_, 6);
lean_inc_ref(v_symPrios_2645_);
v_norm_2646_ = lean_ctor_get(v_params_2445_, 7);
lean_inc_ref(v_norm_2646_);
v_normProcs_2647_ = lean_ctor_get(v_params_2445_, 8);
lean_inc_ref(v_normProcs_2647_);
v_anchorRefs_x3f_2648_ = lean_ctor_get(v_params_2445_, 9);
lean_inc(v_anchorRefs_x3f_2648_);
lean_dec_ref(v_params_2445_);
v_size_2649_ = lean_ctor_get(v_extra_2574_, 2);
lean_inc(v_size_2649_);
v___y_2541_ = v_size_2649_;
v___y_2542_ = v___y_2568_;
v___y_2543_ = v_extraInj_2643_;
v___y_2544_ = v___y_2569_;
v___y_2545_ = v___y_2570_;
v___y_2546_ = v_extra_2574_;
v___y_2547_ = v_anchorRefs_x3f_2648_;
v___y_2548_ = v___y_2571_;
v___y_2549_ = v___y_2573_;
v___y_2550_ = v_symPrios_2645_;
v___y_2551_ = v_extensions_2642_;
v___y_2552_ = v_identity_2641_;
v___y_2553_ = v_config_2640_;
v___y_2554_ = v_extraFacts_2644_;
v___y_2555_ = v___y_2572_;
v___y_2556_ = v_norm_2646_;
v___y_2557_ = v_normProcs_2647_;
goto v___jp_2540_;
}
case 1:
{
lean_object* v_config_2650_; lean_object* v_identity_2651_; lean_object* v_extensions_2652_; lean_object* v_extraInj_2653_; lean_object* v_extraFacts_2654_; lean_object* v_symPrios_2655_; lean_object* v_norm_2656_; lean_object* v_normProcs_2657_; lean_object* v_anchorRefs_x3f_2658_; lean_object* v_size_2659_; 
v_config_2650_ = lean_ctor_get(v_params_2445_, 0);
lean_inc_ref(v_config_2650_);
v_identity_2651_ = lean_ctor_get(v_params_2445_, 1);
lean_inc(v_identity_2651_);
v_extensions_2652_ = lean_ctor_get(v_params_2445_, 2);
lean_inc_ref(v_extensions_2652_);
v_extraInj_2653_ = lean_ctor_get(v_params_2445_, 4);
lean_inc_ref(v_extraInj_2653_);
v_extraFacts_2654_ = lean_ctor_get(v_params_2445_, 5);
lean_inc_ref(v_extraFacts_2654_);
v_symPrios_2655_ = lean_ctor_get(v_params_2445_, 6);
lean_inc_ref(v_symPrios_2655_);
v_norm_2656_ = lean_ctor_get(v_params_2445_, 7);
lean_inc_ref(v_norm_2656_);
v_normProcs_2657_ = lean_ctor_get(v_params_2445_, 8);
lean_inc_ref(v_normProcs_2657_);
v_anchorRefs_x3f_2658_ = lean_ctor_get(v_params_2445_, 9);
lean_inc(v_anchorRefs_x3f_2658_);
lean_dec_ref(v_params_2445_);
v_size_2659_ = lean_ctor_get(v_extra_2574_, 2);
lean_inc(v_size_2659_);
v___y_2541_ = v_size_2659_;
v___y_2542_ = v___y_2568_;
v___y_2543_ = v_extraInj_2653_;
v___y_2544_ = v___y_2569_;
v___y_2545_ = v___y_2570_;
v___y_2546_ = v_extra_2574_;
v___y_2547_ = v_anchorRefs_x3f_2658_;
v___y_2548_ = v___y_2571_;
v___y_2549_ = v___y_2573_;
v___y_2550_ = v_symPrios_2655_;
v___y_2551_ = v_extensions_2652_;
v___y_2552_ = v_identity_2651_;
v___y_2553_ = v_config_2650_;
v___y_2554_ = v_extraFacts_2654_;
v___y_2555_ = v___y_2572_;
v___y_2556_ = v_norm_2656_;
v___y_2557_ = v_normProcs_2657_;
goto v___jp_2540_;
}
default: 
{
lean_object* v_config_2660_; lean_object* v_identity_2661_; lean_object* v_extensions_2662_; lean_object* v_extraInj_2663_; lean_object* v_extraFacts_2664_; lean_object* v_symPrios_2665_; lean_object* v_norm_2666_; lean_object* v_normProcs_2667_; lean_object* v_anchorRefs_x3f_2668_; lean_object* v_size_2669_; 
v_config_2660_ = lean_ctor_get(v_params_2445_, 0);
lean_inc_ref(v_config_2660_);
v_identity_2661_ = lean_ctor_get(v_params_2445_, 1);
lean_inc(v_identity_2661_);
v_extensions_2662_ = lean_ctor_get(v_params_2445_, 2);
lean_inc_ref(v_extensions_2662_);
v_extraInj_2663_ = lean_ctor_get(v_params_2445_, 4);
lean_inc_ref(v_extraInj_2663_);
v_extraFacts_2664_ = lean_ctor_get(v_params_2445_, 5);
lean_inc_ref(v_extraFacts_2664_);
v_symPrios_2665_ = lean_ctor_get(v_params_2445_, 6);
lean_inc_ref(v_symPrios_2665_);
v_norm_2666_ = lean_ctor_get(v_params_2445_, 7);
lean_inc_ref(v_norm_2666_);
v_normProcs_2667_ = lean_ctor_get(v_params_2445_, 8);
lean_inc_ref(v_normProcs_2667_);
v_anchorRefs_x3f_2668_ = lean_ctor_get(v_params_2445_, 9);
lean_inc(v_anchorRefs_x3f_2668_);
lean_dec_ref(v_params_2445_);
v_size_2669_ = lean_ctor_get(v_extra_2574_, 2);
lean_inc(v_size_2669_);
v___y_2504_ = v_size_2669_;
v___y_2505_ = v_extraInj_2663_;
v___y_2506_ = v___y_2570_;
v___y_2507_ = v_extra_2574_;
v___y_2508_ = v_anchorRefs_x3f_2668_;
v___y_2509_ = v_symPrios_2665_;
v___y_2510_ = v_extensions_2662_;
v___y_2511_ = v_config_2660_;
v___y_2512_ = v_identity_2661_;
v___y_2513_ = v_extraFacts_2664_;
v___y_2514_ = v___y_2572_;
v___y_2515_ = v_norm_2666_;
v___y_2516_ = v_normProcs_2667_;
v___y_2517_ = v___y_2569_;
v___y_2518_ = v___y_2571_;
v___y_2519_ = v___y_2568_;
v___y_2520_ = v___y_2573_;
goto v___jp_2503_;
}
}
}
}
v___jp_2670_:
{
if (lean_obj_tag(v_mod_x3f_2447_) == 0)
{
v___y_2479_ = v___y_2673_;
v___y_2480_ = v___y_2674_;
v___y_2481_ = v___y_2675_;
v___y_2482_ = v___y_2677_;
v___y_2483_ = v___y_2679_;
v___y_2484_ = v___y_2672_;
v___y_2485_ = v___y_2676_;
v___y_2486_ = v___y_2671_;
v___y_2487_ = v___y_2678_;
goto v___jp_2478_;
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec_ref_known(v_mod_x3f_2447_, 1);
lean_dec_ref(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v_params_2445_);
v___x_2680_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2681_ = l_Lean_indentExpr(v___y_2675_);
v___x_2682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2680_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2682_, v___y_2677_, v___y_2679_, v___y_2672_, v___y_2676_, v___y_2671_, v___y_2678_);
lean_dec_ref(v___y_2671_);
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
}
v___jp_2692_:
{
uint8_t v___x_2705_; 
v___x_2705_ = l_Lean_Expr_isForall(v___y_2697_);
if (v___x_2705_ == 0)
{
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2694_);
v___y_2671_ = v___y_2703_;
v___y_2672_ = v___y_2701_;
v___y_2673_ = v___y_2695_;
v___y_2674_ = v___y_2696_;
v___y_2675_ = v___y_2697_;
v___y_2676_ = v___y_2702_;
v___y_2677_ = v___y_2699_;
v___y_2678_ = v___y_2704_;
v___y_2679_ = v___y_2700_;
goto v___jp_2670_;
}
else
{
if (v___y_2693_ == 0)
{
lean_dec_ref(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v_mod_x3f_2447_);
v___y_2568_ = v___y_2703_;
v___y_2569_ = v___y_2701_;
v___y_2570_ = v___y_2694_;
v___y_2571_ = v___y_2702_;
v___y_2572_ = v___y_2698_;
v___y_2573_ = v___y_2704_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2706_ = lean_array_get_size(v___y_2695_);
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = lean_nat_dec_eq(v___x_2706_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_dec_ref(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v_mod_x3f_2447_);
v___y_2568_ = v___y_2703_;
v___y_2569_ = v___y_2701_;
v___y_2570_ = v___y_2694_;
v___y_2571_ = v___y_2702_;
v___y_2572_ = v___y_2698_;
v___y_2573_ = v___y_2704_;
goto v___jp_2567_;
}
else
{
if (lean_obj_tag(v_mod_x3f_2447_) == 0)
{
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2694_);
v___y_2671_ = v___y_2703_;
v___y_2672_ = v___y_2701_;
v___y_2673_ = v___y_2695_;
v___y_2674_ = v___y_2696_;
v___y_2675_ = v___y_2697_;
v___y_2676_ = v___y_2702_;
v___y_2677_ = v___y_2699_;
v___y_2678_ = v___y_2704_;
v___y_2679_ = v___y_2700_;
goto v___jp_2670_;
}
else
{
lean_dec_ref_known(v_mod_x3f_2447_, 1);
lean_dec_ref(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec_ref(v___y_2695_);
v___y_2568_ = v___y_2703_;
v___y_2569_ = v___y_2701_;
v___y_2570_ = v___y_2694_;
v___y_2571_ = v___y_2702_;
v___y_2572_ = v___y_2698_;
v___y_2573_ = v___y_2704_;
goto v___jp_2567_;
}
}
}
}
}
v___jp_2709_:
{
lean_object* v___x_2717_; uint8_t v___x_2718_; lean_object* v___x_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; 
v___x_2717_ = lean_box(0);
v___x_2718_ = 1;
v___x_2719_ = lean_box(v___x_2718_);
lean_inc(v_p_2446_);
v___f_2720_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2720_, 0, v_p_2446_);
lean_closure_set(v___f_2720_, 1, v_term_2448_);
lean_closure_set(v___f_2720_, 2, v___x_2717_);
lean_closure_set(v___f_2720_, 3, v___x_2719_);
v___x_2721_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2720_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2769_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2769_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2769_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
if (lean_obj_tag(v_a_2722_) == 1)
{
lean_object* v_val_2726_; lean_object* v_snd_2727_; lean_object* v_fst_2728_; lean_object* v_fst_2729_; lean_object* v_snd_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___f_2733_; lean_object* v___x_2734_; 
lean_del_object(v___x_2724_);
v_val_2726_ = lean_ctor_get(v_a_2722_, 0);
lean_inc(v_val_2726_);
lean_dec_ref_known(v_a_2722_, 1);
v_snd_2727_ = lean_ctor_get(v_val_2726_, 1);
lean_inc(v_snd_2727_);
v_fst_2728_ = lean_ctor_get(v_val_2726_, 0);
lean_inc_n(v_fst_2728_, 2);
lean_dec(v_val_2726_);
v_fst_2729_ = lean_ctor_get(v_snd_2727_, 0);
lean_inc_n(v_fst_2729_, 3);
v_snd_2730_ = lean_ctor_get(v_snd_2727_, 1);
lean_inc(v_snd_2730_);
lean_dec(v_snd_2727_);
v___x_2731_ = lean_box(v___x_2718_);
v___x_2732_ = lean_box(v_minIndexable_2449_);
lean_inc_ref(v_params_2445_);
v___f_2733_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed), 13, 6);
lean_closure_set(v___f_2733_, 0, v_params_2445_);
lean_closure_set(v___f_2733_, 1, v_p_2446_);
lean_closure_set(v___f_2733_, 2, v_fst_2728_);
lean_closure_set(v___f_2733_, 3, v_fst_2729_);
lean_closure_set(v___f_2733_, 4, v___x_2731_);
lean_closure_set(v___f_2733_, 5, v___x_2732_);
lean_inc(v___y_2716_);
lean_inc_ref(v___y_2715_);
lean_inc(v___y_2714_);
lean_inc_ref(v___y_2713_);
v___x_2734_ = lean_infer_type(v_fst_2729_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2736_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc_n(v_a_2735_, 2);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2736_ = l_Lean_Meta_isProp(v_a_2735_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; uint8_t v___x_2738_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = lean_unbox(v_a_2737_);
lean_dec(v_a_2737_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_a_2735_);
lean_dec_ref(v___f_2733_);
lean_dec(v_snd_2730_);
lean_dec(v_fst_2729_);
lean_dec(v_fst_2728_);
lean_dec(v_kind_2710_);
lean_dec(v_mod_x3f_2447_);
lean_dec_ref(v_params_2445_);
v___x_2739_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2740_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2739_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec_ref(v___y_2715_);
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2740_);
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
else
{
uint8_t v___x_2749_; 
v___x_2749_ = lean_unbox(v_snd_2730_);
lean_dec(v_snd_2730_);
v___y_2693_ = v___x_2749_;
v___y_2694_ = v_kind_2710_;
v___y_2695_ = v_fst_2728_;
v___y_2696_ = v_fst_2729_;
v___y_2697_ = v_a_2735_;
v___y_2698_ = v___f_2733_;
v___y_2699_ = v___y_2711_;
v___y_2700_ = v___y_2712_;
v___y_2701_ = v___y_2713_;
v___y_2702_ = v___y_2714_;
v___y_2703_ = v___y_2715_;
v___y_2704_ = v___y_2716_;
goto v___jp_2692_;
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_a_2735_);
lean_dec_ref(v___f_2733_);
lean_dec(v_snd_2730_);
lean_dec(v_fst_2729_);
lean_dec(v_fst_2728_);
lean_dec_ref(v___y_2715_);
lean_dec(v_kind_2710_);
lean_dec(v_mod_x3f_2447_);
lean_dec_ref(v_params_2445_);
v_a_2750_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2736_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2736_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec_ref(v___f_2733_);
lean_dec(v_snd_2730_);
lean_dec(v_fst_2729_);
lean_dec(v_fst_2728_);
lean_dec_ref(v___y_2715_);
lean_dec(v_kind_2710_);
lean_dec(v_mod_x3f_2447_);
lean_dec_ref(v_params_2445_);
v_a_2758_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2734_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2734_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
else
{
lean_object* v___x_2767_; 
lean_dec(v_a_2722_);
lean_dec_ref(v___y_2715_);
lean_dec(v_kind_2710_);
lean_dec(v_mod_x3f_2447_);
lean_dec(v_p_2446_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v_params_2445_);
v___x_2767_ = v___x_2724_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_params_2445_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec_ref(v___y_2715_);
lean_dec(v_kind_2710_);
lean_dec(v_mod_x3f_2447_);
lean_dec(v_p_2446_);
lean_dec_ref(v_params_2445_);
v_a_2770_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2721_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2721_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
v___jp_2778_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
v___x_2785_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2786_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2785_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec_ref(v___y_2783_);
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2786_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
v___jp_2795_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
v___x_2802_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2803_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2802_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec_ref(v___y_2800_);
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2803_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
v___jp_2812_:
{
lean_object* v___x_2819_; 
v___x_2819_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_kind_2710_ = v___x_2819_;
v___y_2711_ = v___y_2813_;
v___y_2712_ = v___y_2814_;
v___y_2713_ = v___y_2815_;
v___y_2714_ = v___y_2816_;
v___y_2715_ = v___y_2817_;
v___y_2716_ = v___y_2818_;
goto v___jp_2709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2870_, lean_object* v_p_2871_, lean_object* v_mod_x3f_2872_, lean_object* v_term_2873_, lean_object* v_minIndexable_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
uint8_t v_minIndexable_boxed_2882_; lean_object* v_res_2883_; 
v_minIndexable_boxed_2882_ = lean_unbox(v_minIndexable_2874_);
v_res_2883_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2870_, v_p_2871_, v_mod_x3f_2872_, v_term_2873_, v_minIndexable_boxed_2882_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(uint8_t v___x_2884_, uint8_t v___x_2885_, lean_object* v_as_2886_, size_t v_i_2887_, size_t v_stop_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2884_, v___x_2885_, v_as_2886_, v_i_2887_, v_stop_2888_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v___x_2897_, lean_object* v___x_2898_, lean_object* v_as_2899_, lean_object* v_i_2900_, lean_object* v_stop_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
uint8_t v___x_16166__boxed_2909_; uint8_t v___x_16167__boxed_2910_; size_t v_i_boxed_2911_; size_t v_stop_boxed_2912_; lean_object* v_res_2913_; 
v___x_16166__boxed_2909_ = lean_unbox(v___x_2897_);
v___x_16167__boxed_2910_ = lean_unbox(v___x_2898_);
v_i_boxed_2911_ = lean_unbox_usize(v_i_2900_);
lean_dec(v_i_2900_);
v_stop_boxed_2912_ = lean_unbox_usize(v_stop_2901_);
lean_dec(v_stop_2901_);
v_res_2913_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v___x_16166__boxed_2909_, v___x_16167__boxed_2910_, v_as_2899_, v_i_boxed_2911_, v_stop_boxed_2912_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec_ref(v_as_2899_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(lean_object* v_00_u03b1_2914_, lean_object* v_msg_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___boxed(lean_object* v_00_u03b1_2924_, lean_object* v_msg_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(v_00_u03b1_2924_, v_msg_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(lean_object* v_msgData_2934_, lean_object* v_macroStack_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2934_, v_macroStack_2935_, v___y_2940_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___boxed(lean_object* v_msgData_2944_, lean_object* v_macroStack_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(v_msgData_2944_, v_macroStack_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2954_, lean_object* v_val_2955_, lean_object* v___x_2956_, uint8_t v___x_2957_, lean_object* v_____r_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; lean_object* v_ext_2967_; lean_object* v_toEnvExtension_2968_; lean_object* v_env_2969_; lean_object* v_config_2970_; lean_object* v_identity_2971_; lean_object* v_extensions_2972_; lean_object* v_extra_2973_; lean_object* v_extraInj_2974_; lean_object* v_extraFacts_2975_; lean_object* v_symPrios_2976_; lean_object* v_norm_2977_; lean_object* v_normProcs_2978_; lean_object* v_anchorRefs_x3f_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2991_; 
v___x_2966_ = lean_st_ref_get(v___y_2964_);
v_ext_2967_ = lean_ctor_get(v_val_2955_, 1);
v_toEnvExtension_2968_ = lean_ctor_get(v_ext_2967_, 0);
v_env_2969_ = lean_ctor_get(v___x_2966_, 0);
lean_inc_ref(v_env_2969_);
lean_dec(v___x_2966_);
v_config_2970_ = lean_ctor_get(v_params_2954_, 0);
v_identity_2971_ = lean_ctor_get(v_params_2954_, 1);
v_extensions_2972_ = lean_ctor_get(v_params_2954_, 2);
v_extra_2973_ = lean_ctor_get(v_params_2954_, 3);
v_extraInj_2974_ = lean_ctor_get(v_params_2954_, 4);
v_extraFacts_2975_ = lean_ctor_get(v_params_2954_, 5);
v_symPrios_2976_ = lean_ctor_get(v_params_2954_, 6);
v_norm_2977_ = lean_ctor_get(v_params_2954_, 7);
v_normProcs_2978_ = lean_ctor_get(v_params_2954_, 8);
v_anchorRefs_x3f_2979_ = lean_ctor_get(v_params_2954_, 9);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_params_2954_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2981_ = v_params_2954_;
v_isShared_2982_ = v_isSharedCheck_2991_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_anchorRefs_x3f_2979_);
lean_inc(v_normProcs_2978_);
lean_inc(v_norm_2977_);
lean_inc(v_symPrios_2976_);
lean_inc(v_extraFacts_2975_);
lean_inc(v_extraInj_2974_);
lean_inc(v_extra_2973_);
lean_inc(v_extensions_2972_);
lean_inc(v_identity_2971_);
lean_inc(v_config_2970_);
lean_dec(v_params_2954_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2991_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v_asyncMode_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
v_asyncMode_2983_ = lean_ctor_get(v_toEnvExtension_2968_, 2);
v___x_2984_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2956_, v_val_2955_, v_env_2969_, v_asyncMode_2983_, v___x_2957_);
v___x_2985_ = lean_array_push(v_extensions_2972_, v___x_2984_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 2, v___x_2985_);
v___x_2987_ = v___x_2981_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_config_2970_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_identity_2971_);
lean_ctor_set(v_reuseFailAlloc_2990_, 2, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2990_, 3, v_extra_2973_);
lean_ctor_set(v_reuseFailAlloc_2990_, 4, v_extraInj_2974_);
lean_ctor_set(v_reuseFailAlloc_2990_, 5, v_extraFacts_2975_);
lean_ctor_set(v_reuseFailAlloc_2990_, 6, v_symPrios_2976_);
lean_ctor_set(v_reuseFailAlloc_2990_, 7, v_norm_2977_);
lean_ctor_set(v_reuseFailAlloc_2990_, 8, v_normProcs_2978_);
lean_ctor_set(v_reuseFailAlloc_2990_, 9, v_anchorRefs_x3f_2979_);
v___x_2987_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
return v___x_2989_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2992_, lean_object* v_val_2993_, lean_object* v___x_2994_, lean_object* v___x_2995_, lean_object* v_____r_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
uint8_t v___x_33375__boxed_3004_; lean_object* v_res_3005_; 
v___x_33375__boxed_3004_ = lean_unbox(v___x_2995_);
v_res_3005_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2992_, v_val_2993_, v___x_2994_, v___x_33375__boxed_3004_, v_____r_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec_ref(v___x_2994_);
lean_dec_ref(v_val_2993_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_3006_, lean_object* v_id_3007_, uint8_t v_minIndexable_3008_, lean_object* v_as_x27_3009_, lean_object* v_b_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
if (lean_obj_tag(v_as_x27_3009_) == 0)
{
lean_object* v___x_3016_; 
lean_dec(v_id_3007_);
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v_b_3010_);
return v___x_3016_;
}
else
{
lean_object* v_head_3017_; lean_object* v_tail_3018_; lean_object* v_toCold_3019_; lean_object* v_currRecDepth_3020_; lean_object* v_ref_3021_; uint16_t v_optionFlags_3022_; uint8_t v_suppressElabErrors_3023_; uint8_t v_checkDeprecated_3024_; uint8_t v_isRecordingDeps_3025_; uint8_t v___x_3026_; lean_object* v___x_3027_; lean_object* v_ref_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_head_3017_ = lean_ctor_get(v_as_x27_3009_, 0);
v_tail_3018_ = lean_ctor_get(v_as_x27_3009_, 1);
v_toCold_3019_ = lean_ctor_get(v___y_3013_, 0);
v_currRecDepth_3020_ = lean_ctor_get(v___y_3013_, 1);
v_ref_3021_ = lean_ctor_get(v___y_3013_, 2);
v_optionFlags_3022_ = lean_ctor_get_uint16(v___y_3013_, sizeof(void*)*3);
v_suppressElabErrors_3023_ = lean_ctor_get_uint8(v___y_3013_, sizeof(void*)*3 + 2);
v_checkDeprecated_3024_ = lean_ctor_get_uint8(v___y_3013_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3025_ = lean_ctor_get_uint8(v___y_3013_, sizeof(void*)*3 + 4);
v___x_3026_ = 0;
v___x_3027_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_ref_3028_ = l_Lean_replaceRef(v_p_3006_, v_ref_3021_);
lean_inc(v_currRecDepth_3020_);
lean_inc_ref(v_toCold_3019_);
v___x_3029_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3029_, 0, v_toCold_3019_);
lean_ctor_set(v___x_3029_, 1, v_currRecDepth_3020_);
lean_ctor_set(v___x_3029_, 2, v_ref_3028_);
lean_ctor_set_uint16(v___x_3029_, sizeof(void*)*3, v_optionFlags_3022_);
lean_ctor_set_uint8(v___x_3029_, sizeof(void*)*3 + 2, v_suppressElabErrors_3023_);
lean_ctor_set_uint8(v___x_3029_, sizeof(void*)*3 + 3, v_checkDeprecated_3024_);
lean_ctor_set_uint8(v___x_3029_, sizeof(void*)*3 + 4, v_isRecordingDeps_3025_);
lean_inc(v_head_3017_);
lean_inc(v_id_3007_);
v___x_3030_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_3010_, v_id_3007_, v_head_3017_, v___x_3027_, v_minIndexable_3008_, v___x_3026_, v___x_3026_, v___y_3011_, v___y_3012_, v___x_3029_, v___y_3014_);
lean_dec_ref_known(v___x_3029_, 3);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v_as_x27_3009_ = v_tail_3018_;
v_b_3010_ = v_a_3031_;
goto _start;
}
else
{
lean_dec(v_id_3007_);
return v___x_3030_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_3033_, lean_object* v_id_3034_, lean_object* v_minIndexable_3035_, lean_object* v_as_x27_3036_, lean_object* v_b_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
uint8_t v_minIndexable_boxed_3043_; lean_object* v_res_3044_; 
v_minIndexable_boxed_3043_ = lean_unbox(v_minIndexable_3035_);
v_res_3044_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3033_, v_id_3034_, v_minIndexable_boxed_3043_, v_as_x27_3036_, v_b_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v_as_x27_3036_);
lean_dec(v_p_3033_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
if (lean_obj_tag(v_a_3046_) == 0)
{
lean_object* v___x_3048_; 
v___x_3048_ = l_List_reverse___redArg(v_a_3047_);
return v___x_3048_;
}
else
{
lean_object* v_head_3049_; lean_object* v_tail_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3061_; 
v_head_3049_ = lean_ctor_get(v_a_3046_, 0);
v_tail_3050_ = lean_ctor_get(v_a_3046_, 1);
v_isSharedCheck_3061_ = !lean_is_exclusive(v_a_3046_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3052_ = v_a_3046_;
v_isShared_3053_ = v_isSharedCheck_3061_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_tail_3050_);
lean_inc(v_head_3049_);
lean_dec(v_a_3046_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3061_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v_kind_3054_; uint8_t v___x_3055_; 
v_kind_3054_ = lean_ctor_get(v_head_3049_, 6);
v___x_3055_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_3054_, v_k_3045_);
if (v___x_3055_ == 0)
{
lean_del_object(v___x_3052_);
lean_dec(v_head_3049_);
v_a_3046_ = v_tail_3050_;
goto _start;
}
else
{
lean_object* v___x_3058_; 
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 1, v_a_3047_);
v___x_3058_ = v___x_3052_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_head_3049_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v_a_3047_);
v___x_3058_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
v_a_3046_ = v_tail_3050_;
v_a_3047_ = v___x_3058_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_3062_, v_a_3063_, v_a_3064_);
lean_dec(v_k_3062_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_3066_, lean_object* v_msg_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_toCold_3075_; lean_object* v_currRecDepth_3076_; lean_object* v_ref_3077_; uint16_t v_optionFlags_3078_; uint8_t v_suppressElabErrors_3079_; uint8_t v_checkDeprecated_3080_; uint8_t v_isRecordingDeps_3081_; lean_object* v_ref_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_toCold_3075_ = lean_ctor_get(v___y_3072_, 0);
v_currRecDepth_3076_ = lean_ctor_get(v___y_3072_, 1);
v_ref_3077_ = lean_ctor_get(v___y_3072_, 2);
v_optionFlags_3078_ = lean_ctor_get_uint16(v___y_3072_, sizeof(void*)*3);
v_suppressElabErrors_3079_ = lean_ctor_get_uint8(v___y_3072_, sizeof(void*)*3 + 2);
v_checkDeprecated_3080_ = lean_ctor_get_uint8(v___y_3072_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3081_ = lean_ctor_get_uint8(v___y_3072_, sizeof(void*)*3 + 4);
v_ref_3082_ = l_Lean_replaceRef(v_ref_3066_, v_ref_3077_);
lean_inc(v_currRecDepth_3076_);
lean_inc_ref(v_toCold_3075_);
v___x_3083_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3083_, 0, v_toCold_3075_);
lean_ctor_set(v___x_3083_, 1, v_currRecDepth_3076_);
lean_ctor_set(v___x_3083_, 2, v_ref_3082_);
lean_ctor_set_uint16(v___x_3083_, sizeof(void*)*3, v_optionFlags_3078_);
lean_ctor_set_uint8(v___x_3083_, sizeof(void*)*3 + 2, v_suppressElabErrors_3079_);
lean_ctor_set_uint8(v___x_3083_, sizeof(void*)*3 + 3, v_checkDeprecated_3080_);
lean_ctor_set_uint8(v___x_3083_, sizeof(void*)*3 + 4, v_isRecordingDeps_3081_);
v___x_3084_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___x_3083_, v___y_3073_);
lean_dec_ref_known(v___x_3083_, 3);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_3085_, lean_object* v_msg_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_3085_, v_msg_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v_ref_3085_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_3095_, lean_object* v_id_3096_, uint8_t v_minIndexable_3097_, lean_object* v_as_x27_3098_, lean_object* v_b_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
if (lean_obj_tag(v_as_x27_3098_) == 0)
{
lean_object* v___x_3105_; 
lean_dec(v_id_3096_);
v___x_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3105_, 0, v_b_3099_);
return v___x_3105_;
}
else
{
lean_object* v_head_3106_; lean_object* v_tail_3107_; lean_object* v_toCold_3108_; lean_object* v_currRecDepth_3109_; lean_object* v_ref_3110_; uint16_t v_optionFlags_3111_; uint8_t v_suppressElabErrors_3112_; uint8_t v_checkDeprecated_3113_; uint8_t v_isRecordingDeps_3114_; uint8_t v___x_3115_; uint8_t v___x_3116_; lean_object* v___x_3117_; lean_object* v_ref_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v_head_3106_ = lean_ctor_get(v_as_x27_3098_, 0);
v_tail_3107_ = lean_ctor_get(v_as_x27_3098_, 1);
v_toCold_3108_ = lean_ctor_get(v___y_3102_, 0);
v_currRecDepth_3109_ = lean_ctor_get(v___y_3102_, 1);
v_ref_3110_ = lean_ctor_get(v___y_3102_, 2);
v_optionFlags_3111_ = lean_ctor_get_uint16(v___y_3102_, sizeof(void*)*3);
v_suppressElabErrors_3112_ = lean_ctor_get_uint8(v___y_3102_, sizeof(void*)*3 + 2);
v_checkDeprecated_3113_ = lean_ctor_get_uint8(v___y_3102_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3114_ = lean_ctor_get_uint8(v___y_3102_, sizeof(void*)*3 + 4);
v___x_3115_ = 0;
v___x_3116_ = 1;
v___x_3117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_ref_3118_ = l_Lean_replaceRef(v_p_3095_, v_ref_3110_);
lean_inc(v_currRecDepth_3109_);
lean_inc_ref(v_toCold_3108_);
v___x_3119_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3119_, 0, v_toCold_3108_);
lean_ctor_set(v___x_3119_, 1, v_currRecDepth_3109_);
lean_ctor_set(v___x_3119_, 2, v_ref_3118_);
lean_ctor_set_uint16(v___x_3119_, sizeof(void*)*3, v_optionFlags_3111_);
lean_ctor_set_uint8(v___x_3119_, sizeof(void*)*3 + 2, v_suppressElabErrors_3112_);
lean_ctor_set_uint8(v___x_3119_, sizeof(void*)*3 + 3, v_checkDeprecated_3113_);
lean_ctor_set_uint8(v___x_3119_, sizeof(void*)*3 + 4, v_isRecordingDeps_3114_);
lean_inc(v_head_3106_);
lean_inc(v_id_3096_);
v___x_3120_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_3099_, v_id_3096_, v_head_3106_, v___x_3117_, v_minIndexable_3097_, v___x_3115_, v___x_3116_, v___y_3100_, v___y_3101_, v___x_3119_, v___y_3103_);
lean_dec_ref_known(v___x_3119_, 3);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v_as_x27_3098_ = v_tail_3107_;
v_b_3099_ = v_a_3121_;
goto _start;
}
else
{
lean_dec(v_id_3096_);
return v___x_3120_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_3123_, lean_object* v_id_3124_, lean_object* v_minIndexable_3125_, lean_object* v_as_x27_3126_, lean_object* v_b_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
uint8_t v_minIndexable_boxed_3133_; lean_object* v_res_3134_; 
v_minIndexable_boxed_3133_ = lean_unbox(v_minIndexable_3125_);
v_res_3134_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3123_, v_id_3124_, v_minIndexable_boxed_3133_, v_as_x27_3126_, v_b_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v_as_x27_3126_);
lean_dec(v_p_3123_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_3135_){
_start:
{
if (lean_obj_tag(v_x_3135_) == 0)
{
lean_object* v___x_3136_; 
v___x_3136_ = lean_box(0);
return v___x_3136_;
}
else
{
lean_object* v_head_3137_; lean_object* v_tail_3138_; lean_object* v_fst_3139_; uint8_t v___x_3140_; 
v_head_3137_ = lean_ctor_get(v_x_3135_, 0);
v_tail_3138_ = lean_ctor_get(v_x_3135_, 1);
v_fst_3139_ = lean_ctor_get(v_head_3137_, 0);
v___x_3140_ = l_Lean_isPrivateName(v_fst_3139_);
if (v___x_3140_ == 0)
{
v_x_3135_ = v_tail_3138_;
goto _start;
}
else
{
lean_object* v___x_3142_; 
lean_inc(v_head_3137_);
v___x_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3142_, 0, v_head_3137_);
return v___x_3142_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_3143_);
lean_dec(v_x_3143_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_3145_, lean_object* v_msgData_3146_, uint8_t v_severity_3147_, uint8_t v_isSilent_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
uint8_t v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; uint8_t v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v_toCold_3162_; lean_object* v___y_3163_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; uint8_t v___y_3195_; uint8_t v___y_3196_; uint8_t v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3219_; lean_object* v___y_3220_; uint8_t v___y_3221_; lean_object* v___y_3222_; uint8_t v___y_3223_; uint8_t v___y_3224_; lean_object* v___y_3225_; uint8_t v___y_3229_; uint8_t v___y_3230_; uint8_t v___x_3240_; uint8_t v___y_3242_; uint8_t v___x_3248_; 
v___x_3240_ = 2;
v___x_3248_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3147_, v___x_3240_);
if (v___x_3248_ == 0)
{
v___y_3242_ = v___x_3248_;
goto v___jp_3241_;
}
else
{
uint8_t v___x_3249_; 
lean_inc_ref(v_msgData_3146_);
v___x_3249_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3146_);
if (v___x_3249_ == 0)
{
v___y_3242_ = v___x_3249_;
goto v___jp_3241_;
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_dec_ref(v_msgData_3146_);
v___x_3250_ = lean_box(0);
v___x_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
return v___x_3251_;
}
}
v___jp_3154_:
{
lean_object* v_currNamespace_3164_; lean_object* v_openDecls_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v_env_3170_; lean_object* v_nextMacroScope_3171_; lean_object* v_ngen_3172_; lean_object* v_auxDeclNGen_3173_; lean_object* v_traceState_3174_; lean_object* v_cache_3175_; lean_object* v_recordedDeps_3176_; lean_object* v_messages_3177_; lean_object* v_infoState_3178_; lean_object* v_snapshotTasks_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3190_; 
v_currNamespace_3164_ = lean_ctor_get(v_toCold_3162_, 4);
v_openDecls_3165_ = lean_ctor_get(v_toCold_3162_, 5);
lean_inc(v_openDecls_3165_);
lean_inc(v_currNamespace_3164_);
v___x_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3166_, 0, v_currNamespace_3164_);
lean_ctor_set(v___x_3166_, 1, v_openDecls_3165_);
v___x_3167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
lean_ctor_set(v___x_3167_, 1, v___y_3159_);
lean_inc_ref(v___y_3157_);
lean_inc_ref(v___y_3156_);
v___x_3168_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3168_, 0, v___y_3156_);
lean_ctor_set(v___x_3168_, 1, v___y_3161_);
lean_ctor_set(v___x_3168_, 2, v___y_3160_);
lean_ctor_set(v___x_3168_, 3, v___y_3157_);
lean_ctor_set(v___x_3168_, 4, v___x_3167_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*5, v___y_3158_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*5 + 1, v___y_3155_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*5 + 2, v_isSilent_3148_);
v___x_3169_ = lean_st_ref_take(v___y_3163_);
v_env_3170_ = lean_ctor_get(v___x_3169_, 0);
v_nextMacroScope_3171_ = lean_ctor_get(v___x_3169_, 1);
v_ngen_3172_ = lean_ctor_get(v___x_3169_, 2);
v_auxDeclNGen_3173_ = lean_ctor_get(v___x_3169_, 3);
v_traceState_3174_ = lean_ctor_get(v___x_3169_, 4);
v_cache_3175_ = lean_ctor_get(v___x_3169_, 5);
v_recordedDeps_3176_ = lean_ctor_get(v___x_3169_, 6);
v_messages_3177_ = lean_ctor_get(v___x_3169_, 7);
v_infoState_3178_ = lean_ctor_get(v___x_3169_, 8);
v_snapshotTasks_3179_ = lean_ctor_get(v___x_3169_, 9);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3181_ = v___x_3169_;
v_isShared_3182_ = v_isSharedCheck_3190_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_snapshotTasks_3179_);
lean_inc(v_infoState_3178_);
lean_inc(v_messages_3177_);
lean_inc(v_recordedDeps_3176_);
lean_inc(v_cache_3175_);
lean_inc(v_traceState_3174_);
lean_inc(v_auxDeclNGen_3173_);
lean_inc(v_ngen_3172_);
lean_inc(v_nextMacroScope_3171_);
lean_inc(v_env_3170_);
lean_dec(v___x_3169_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3190_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3186_; 
v___x_3183_ = lean_box(0);
v___x_3184_ = l_Lean_MessageLog_add(v___x_3168_, v_messages_3177_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 7, v___x_3184_);
v___x_3186_ = v___x_3181_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_env_3170_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_nextMacroScope_3171_);
lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_ngen_3172_);
lean_ctor_set(v_reuseFailAlloc_3189_, 3, v_auxDeclNGen_3173_);
lean_ctor_set(v_reuseFailAlloc_3189_, 4, v_traceState_3174_);
lean_ctor_set(v_reuseFailAlloc_3189_, 5, v_cache_3175_);
lean_ctor_set(v_reuseFailAlloc_3189_, 6, v_recordedDeps_3176_);
lean_ctor_set(v_reuseFailAlloc_3189_, 7, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3189_, 8, v_infoState_3178_);
lean_ctor_set(v_reuseFailAlloc_3189_, 9, v_snapshotTasks_3179_);
v___x_3186_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_st_ref_put(v___y_3163_, v___x_3186_);
v___x_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3183_);
return v___x_3188_;
}
}
}
v___jp_3191_:
{
lean_object* v_fileName_3200_; lean_object* v_fileMap_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3217_; 
v_fileName_3200_ = lean_ctor_get(v___y_3194_, 0);
v_fileMap_3201_ = lean_ctor_get(v___y_3194_, 1);
v___x_3202_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3146_);
v___x_3203_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_3202_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3217_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3217_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_inc_ref_n(v_fileMap_3201_, 2);
v___x_3208_ = l_Lean_FileMap_toPosition(v_fileMap_3201_, v___y_3198_);
lean_dec(v___y_3198_);
v___x_3209_ = l_Lean_FileMap_toPosition(v_fileMap_3201_, v___y_3199_);
lean_dec(v___y_3199_);
v___x_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
v___x_3211_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_3197_ == 0)
{
lean_del_object(v___x_3206_);
lean_dec_ref(v___y_3193_);
v___y_3155_ = v___y_3195_;
v___y_3156_ = v_fileName_3200_;
v___y_3157_ = v___x_3211_;
v___y_3158_ = v___y_3196_;
v___y_3159_ = v_a_3204_;
v___y_3160_ = v___x_3210_;
v___y_3161_ = v___x_3208_;
v_toCold_3162_ = v___y_3192_;
v___y_3163_ = v___y_3152_;
goto v___jp_3154_;
}
else
{
uint8_t v___x_3212_; 
lean_inc(v_a_3204_);
v___x_3212_ = l_Lean_MessageData_hasTag(v___y_3193_, v_a_3204_);
if (v___x_3212_ == 0)
{
lean_object* v___x_3213_; lean_object* v___x_3215_; 
lean_dec_ref_known(v___x_3210_, 1);
lean_dec_ref(v___x_3208_);
lean_dec(v_a_3204_);
v___x_3213_ = lean_box(0);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3213_);
v___x_3215_ = v___x_3206_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
else
{
lean_del_object(v___x_3206_);
v___y_3155_ = v___y_3195_;
v___y_3156_ = v_fileName_3200_;
v___y_3157_ = v___x_3211_;
v___y_3158_ = v___y_3196_;
v___y_3159_ = v_a_3204_;
v___y_3160_ = v___x_3210_;
v___y_3161_ = v___x_3208_;
v_toCold_3162_ = v___y_3192_;
v___y_3163_ = v___y_3152_;
goto v___jp_3154_;
}
}
}
}
v___jp_3218_:
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Lean_Syntax_getTailPos_x3f(v___y_3222_, v___y_3224_);
lean_dec(v___y_3222_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_inc(v___y_3225_);
v___y_3192_ = v___y_3219_;
v___y_3193_ = v___y_3220_;
v___y_3194_ = v___y_3219_;
v___y_3195_ = v___y_3223_;
v___y_3196_ = v___y_3224_;
v___y_3197_ = v___y_3221_;
v___y_3198_ = v___y_3225_;
v___y_3199_ = v___y_3225_;
goto v___jp_3191_;
}
else
{
lean_object* v_val_3227_; 
v_val_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_val_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v___y_3192_ = v___y_3219_;
v___y_3193_ = v___y_3220_;
v___y_3194_ = v___y_3219_;
v___y_3195_ = v___y_3223_;
v___y_3196_ = v___y_3224_;
v___y_3197_ = v___y_3221_;
v___y_3198_ = v___y_3225_;
v___y_3199_ = v_val_3227_;
goto v___jp_3191_;
}
}
v___jp_3228_:
{
lean_object* v_toCold_3231_; lean_object* v_ref_3232_; uint8_t v_suppressElabErrors_3233_; lean_object* v___x_3234_; lean_object* v___f_3235_; lean_object* v_ref_3236_; lean_object* v___x_3237_; 
v_toCold_3231_ = lean_ctor_get(v___y_3151_, 0);
v_ref_3232_ = lean_ctor_get(v___y_3151_, 2);
v_suppressElabErrors_3233_ = lean_ctor_get_uint8(v___y_3151_, sizeof(void*)*3 + 2);
v___x_3234_ = lean_box(v_suppressElabErrors_3233_);
v___f_3235_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3235_, 0, v___x_3234_);
v_ref_3236_ = l_Lean_replaceRef(v_ref_3145_, v_ref_3232_);
v___x_3237_ = l_Lean_Syntax_getPos_x3f(v_ref_3236_, v___y_3229_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_unsigned_to_nat(0u);
v___y_3219_ = v_toCold_3231_;
v___y_3220_ = v___f_3235_;
v___y_3221_ = v_suppressElabErrors_3233_;
v___y_3222_ = v_ref_3236_;
v___y_3223_ = v___y_3230_;
v___y_3224_ = v___y_3229_;
v___y_3225_ = v___x_3238_;
goto v___jp_3218_;
}
else
{
lean_object* v_val_3239_; 
v_val_3239_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_val_3239_);
lean_dec_ref_known(v___x_3237_, 1);
v___y_3219_ = v_toCold_3231_;
v___y_3220_ = v___f_3235_;
v___y_3221_ = v_suppressElabErrors_3233_;
v___y_3222_ = v_ref_3236_;
v___y_3223_ = v___y_3230_;
v___y_3224_ = v___y_3229_;
v___y_3225_ = v_val_3239_;
goto v___jp_3218_;
}
}
v___jp_3241_:
{
uint8_t v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = 1;
v___x_3244_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3147_, v___x_3243_);
if (v___x_3244_ == 0)
{
v___y_3229_ = v___y_3242_;
v___y_3230_ = v_severity_3147_;
goto v___jp_3228_;
}
else
{
lean_object* v___x_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
v___x_3245_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3151_);
v___x_3246_ = l_Lean_warningAsError;
v___x_3247_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3245_, v___x_3246_);
lean_dec_ref(v___x_3245_);
if (v___x_3247_ == 0)
{
v___y_3229_ = v___y_3242_;
v___y_3230_ = v_severity_3147_;
goto v___jp_3228_;
}
else
{
v___y_3229_ = v___y_3242_;
v___y_3230_ = v___x_3240_;
goto v___jp_3228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_3252_, lean_object* v_msgData_3253_, lean_object* v_severity_3254_, lean_object* v_isSilent_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
uint8_t v_severity_boxed_3261_; uint8_t v_isSilent_boxed_3262_; lean_object* v_res_3263_; 
v_severity_boxed_3261_ = lean_unbox(v_severity_3254_);
v_isSilent_boxed_3262_ = lean_unbox(v_isSilent_3255_);
v_res_3263_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3252_, v_msgData_3253_, v_severity_boxed_3261_, v_isSilent_boxed_3262_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v_ref_3252_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_3264_, uint8_t v_severity_3265_, uint8_t v_isSilent_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_ref_3274_; lean_object* v___x_3275_; 
v_ref_3274_ = lean_ctor_get(v___y_3271_, 2);
v___x_3275_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3274_, v_msgData_3264_, v_severity_3265_, v_isSilent_3266_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_3276_, lean_object* v_severity_3277_, lean_object* v_isSilent_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
uint8_t v_severity_boxed_3286_; uint8_t v_isSilent_boxed_3287_; lean_object* v_res_3288_; 
v_severity_boxed_3286_ = lean_unbox(v_severity_3277_);
v_isSilent_boxed_3287_ = lean_unbox(v_isSilent_3278_);
v_res_3288_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3276_, v_severity_boxed_3286_, v_isSilent_boxed_3287_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
uint8_t v___x_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = 1;
v___x_3298_ = 0;
v___x_3299_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3289_, v___x_3297_, v___x_3298_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v___x_3312_; uint8_t v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3312_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3310_);
v___x_3313_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3312_, v_opt_3309_);
lean_dec_ref(v___x_3312_);
v___x_3314_ = lean_box(v___x_3313_);
v___x_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3316_, v___y_3317_);
lean_dec_ref(v___y_3317_);
lean_dec_ref(v_opt_3316_);
return v_res_3319_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3322_ = l_Lean_stringToMessageData(v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3325_ = l_Lean_stringToMessageData(v___x_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v___x_3334_; lean_object* v_env_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3357_; 
v___x_3334_ = lean_st_ref_get(v___y_3332_);
v_env_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc_ref(v_env_3335_);
lean_dec(v___x_3334_);
v___x_3336_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3337_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3336_, v___y_3331_);
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3357_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3357_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
uint8_t v_isExporting_3347_; 
v_isExporting_3347_ = lean_ctor_get_uint8(v_env_3335_, sizeof(void*)*13);
lean_dec_ref(v_env_3335_);
if (v_isExporting_3347_ == 0)
{
lean_dec(v_a_3338_);
lean_dec(v_id_3326_);
goto v___jp_3342_;
}
else
{
uint8_t v___x_3348_; 
v___x_3348_ = l_Lean_isPrivateName(v_id_3326_);
if (v___x_3348_ == 0)
{
lean_dec(v_a_3338_);
lean_dec(v_id_3326_);
goto v___jp_3342_;
}
else
{
uint8_t v___x_3349_; 
v___x_3349_ = lean_unbox(v_a_3338_);
lean_dec(v_a_3338_);
if (v___x_3349_ == 0)
{
lean_dec(v_id_3326_);
goto v___jp_3342_;
}
else
{
lean_object* v___x_3350_; uint8_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
lean_del_object(v___x_3340_);
v___x_3350_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3351_ = 0;
v___x_3352_ = l_Lean_MessageData_ofConstName(v_id_3326_, v___x_3351_);
v___x_3353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3350_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3353_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3355_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
return v___x_3356_;
}
}
}
v___jp_3342_:
{
lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3343_ = lean_box(0);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3343_);
v___x_3345_ = v___x_3340_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3367_, uint8_t v_enableLog_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v___x_3376_; lean_object* v_toCold_3377_; lean_object* v_env_3378_; lean_object* v_currNamespace_3379_; lean_object* v_openDecls_3380_; lean_object* v___x_3381_; lean_object* v_res_3382_; lean_object* v___x_3383_; 
v___x_3376_ = lean_st_ref_get(v___y_3374_);
v_toCold_3377_ = lean_ctor_get(v___y_3373_, 0);
v_env_3378_ = lean_ctor_get(v___x_3376_, 0);
lean_inc_ref(v_env_3378_);
lean_dec(v___x_3376_);
v_currNamespace_3379_ = lean_ctor_get(v_toCold_3377_, 4);
v_openDecls_3380_ = lean_ctor_get(v_toCold_3377_, 5);
v___x_3381_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3373_);
lean_inc(v_openDecls_3380_);
lean_inc(v_currNamespace_3379_);
v_res_3382_ = l_Lean_ResolveName_resolveGlobalName(v_env_3378_, v___x_3381_, v_currNamespace_3379_, v_openDecls_3380_, v_id_3367_);
lean_dec_ref(v___x_3381_);
v___x_3383_ = lean_st_ref_get(v___y_3374_);
if (v_enableLog_3368_ == 0)
{
lean_object* v___x_3384_; 
lean_dec(v___x_3383_);
v___x_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_res_3382_);
return v___x_3384_;
}
else
{
lean_object* v_env_3385_; uint8_t v_isExporting_3386_; 
v_env_3385_ = lean_ctor_get(v___x_3383_, 0);
lean_inc_ref(v_env_3385_);
lean_dec(v___x_3383_);
v_isExporting_3386_ = lean_ctor_get_uint8(v_env_3385_, sizeof(void*)*13);
lean_dec_ref(v_env_3385_);
if (v_isExporting_3386_ == 0)
{
lean_object* v___x_3387_; 
v___x_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3387_, 0, v_res_3382_);
return v___x_3387_;
}
else
{
lean_object* v___x_3388_; 
v___x_3388_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3382_);
if (lean_obj_tag(v___x_3388_) == 1)
{
lean_object* v_val_3389_; lean_object* v_fst_3390_; lean_object* v___x_3391_; 
v_val_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_val_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v_fst_3390_ = lean_ctor_get(v_val_3389_, 0);
lean_inc(v_fst_3390_);
lean_dec(v_val_3389_);
v___x_3391_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3390_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; 
v_unused_3399_ = lean_ctor_get(v___x_3391_, 0);
lean_dec(v_unused_3399_);
v___x_3393_ = v___x_3391_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_dec(v___x_3391_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 0, v_res_3382_);
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_res_3382_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v_res_3382_);
v_a_3400_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3391_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3391_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v___x_3408_; 
lean_dec(v___x_3388_);
v___x_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3408_, 0, v_res_3382_);
return v___x_3408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3409_, lean_object* v_enableLog_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
uint8_t v_enableLog_boxed_3418_; lean_object* v_res_3419_; 
v_enableLog_boxed_3418_ = lean_unbox(v_enableLog_3410_);
v_res_3419_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3409_, v_enableLog_boxed_3418_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
return v_res_3419_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_snd_3420_, lean_object* v_x_3421_){
_start:
{
if (lean_obj_tag(v_x_3421_) == 0)
{
uint8_t v___x_3422_; 
v___x_3422_ = 0;
return v___x_3422_;
}
else
{
lean_object* v_head_3423_; lean_object* v_tail_3424_; lean_object* v_snd_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v_head_3423_ = lean_ctor_get(v_x_3421_, 0);
v_tail_3424_ = lean_ctor_get(v_x_3421_, 1);
v_snd_3425_ = lean_ctor_get(v_head_3423_, 1);
v___x_3426_ = l_List_lengthTR___redArg(v_snd_3425_);
v___x_3427_ = l_List_lengthTR___redArg(v_snd_3420_);
v___x_3428_ = lean_nat_dec_lt(v___x_3426_, v___x_3427_);
lean_dec(v___x_3427_);
lean_dec(v___x_3426_);
if (v___x_3428_ == 0)
{
v_x_3421_ = v_tail_3424_;
goto _start;
}
else
{
return v___x_3428_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14___boxed(lean_object* v_snd_3430_, lean_object* v_x_3431_){
_start:
{
uint8_t v_res_3432_; lean_object* v_r_3433_; 
v_res_3432_ = l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_snd_3430_, v_x_3431_);
lean_dec(v_x_3431_);
lean_dec(v_snd_3430_);
v_r_3433_ = lean_box(v_res_3432_);
return v_r_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3434_, lean_object* v_findLocalDecl_x3f_3435_, lean_object* v_n_3436_, lean_object* v_projs_3437_, lean_object* v_auxDecl_x3f_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v_auxDecl_x3f_3454_; lean_object* v_imported_3485_; lean_object* v_ctx_3486_; lean_object* v_scopes_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_imported_3485_ = lean_ctor_get(v_view_3434_, 1);
v_ctx_3486_ = lean_ctor_get(v_view_3434_, 2);
v_scopes_3487_ = lean_ctor_get(v_view_3434_, 3);
lean_inc(v_scopes_3487_);
lean_inc(v_ctx_3486_);
lean_inc(v_imported_3485_);
lean_inc(v_n_3436_);
v___x_3488_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3488_, 0, v_n_3436_);
lean_ctor_set(v___x_3488_, 1, v_imported_3485_);
lean_ctor_set(v___x_3488_, 2, v_ctx_3486_);
lean_ctor_set(v___x_3488_, 3, v_scopes_3487_);
lean_inc_ref(v_findLocalDecl_x3f_3435_);
v___x_3489_ = lean_apply_1(v_findLocalDecl_x3f_3435_, v___x_3488_);
if (lean_obj_tag(v___x_3489_) == 1)
{
lean_object* v_val_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3505_; 
v_val_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3505_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_val_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3505_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
uint8_t v___x_3494_; 
v___x_3494_ = l_Lean_LocalDecl_isAuxDecl(v_val_3490_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3498_; 
lean_dec(v_auxDecl_x3f_3438_);
lean_dec(v_n_3436_);
lean_dec_ref(v_findLocalDecl_x3f_3435_);
lean_dec_ref(v_view_3434_);
v___x_3495_ = l_Lean_LocalDecl_toExpr(v_val_3490_);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set(v___x_3496_, 1, v_projs_3437_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3496_);
v___x_3498_ = v___x_3492_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
}
else
{
if (lean_obj_tag(v_auxDecl_x3f_3438_) == 0)
{
lean_object* v___x_3501_; lean_object* v___x_3503_; 
lean_inc(v_projs_3437_);
v___x_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3501_, 0, v_val_3490_);
lean_ctor_set(v___x_3501_, 1, v_projs_3437_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3501_);
v___x_3503_ = v___x_3492_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
v_auxDecl_x3f_3454_ = v___x_3503_;
goto v___jp_3453_;
}
}
else
{
lean_del_object(v___x_3492_);
lean_dec(v_val_3490_);
v_auxDecl_x3f_3454_ = v_auxDecl_x3f_3438_;
goto v___jp_3453_;
}
}
}
}
else
{
lean_dec(v___x_3489_);
v_auxDecl_x3f_3454_ = v_auxDecl_x3f_3438_;
goto v___jp_3453_;
}
v___jp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3449_ = l_Lean_LocalDecl_toExpr(v___y_3447_);
v___x_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
lean_ctor_set(v___x_3450_, 1, v___y_3448_);
v___x_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
return v___x_3452_;
}
v___jp_3453_:
{
if (lean_obj_tag(v_n_3436_) == 1)
{
lean_object* v_pre_3455_; lean_object* v_str_3456_; lean_object* v___x_3457_; 
v_pre_3455_ = lean_ctor_get(v_n_3436_, 0);
lean_inc(v_pre_3455_);
v_str_3456_ = lean_ctor_get(v_n_3436_, 1);
lean_inc_ref(v_str_3456_);
lean_dec_ref_known(v_n_3436_, 2);
v___x_3457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3457_, 0, v_str_3456_);
lean_ctor_set(v___x_3457_, 1, v_projs_3437_);
v_n_3436_ = v_pre_3455_;
v_projs_3437_ = v___x_3457_;
v_auxDecl_x3f_3438_ = v_auxDecl_x3f_3454_;
goto _start;
}
else
{
lean_dec(v_projs_3437_);
lean_dec(v_n_3436_);
lean_dec_ref(v_findLocalDecl_x3f_3435_);
if (lean_obj_tag(v_auxDecl_x3f_3454_) == 1)
{
lean_object* v_val_3459_; lean_object* v_fst_3460_; lean_object* v_snd_3461_; uint8_t v___x_3462_; 
v_val_3459_ = lean_ctor_get(v_auxDecl_x3f_3454_, 0);
lean_inc(v_val_3459_);
lean_dec_ref_known(v_auxDecl_x3f_3454_, 1);
v_fst_3460_ = lean_ctor_get(v_val_3459_, 0);
lean_inc(v_fst_3460_);
v_snd_3461_ = lean_ctor_get(v_val_3459_, 1);
lean_inc(v_snd_3461_);
lean_dec(v_val_3459_);
v___x_3462_ = l_List_isEmpty___redArg(v_snd_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = l_Lean_MacroScopesView_review(v_view_3434_);
v___x_3464_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3463_, v___x_3462_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3474_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3474_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3474_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
uint8_t v___x_3469_; 
v___x_3469_ = l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_snd_3461_, v_a_3465_);
lean_dec(v_a_3465_);
if (v___x_3469_ == 0)
{
lean_del_object(v___x_3467_);
v___y_3447_ = v_fst_3460_;
v___y_3448_ = v_snd_3461_;
goto v___jp_3446_;
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
lean_dec(v_snd_3461_);
lean_dec(v_fst_3460_);
v___x_3470_ = lean_box(0);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3470_);
v___x_3472_ = v___x_3467_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec(v_snd_3461_);
lean_dec(v_fst_3460_);
v_a_3475_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3464_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3464_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
lean_dec_ref(v_view_3434_);
v___y_3447_ = v_fst_3460_;
v___y_3448_ = v_snd_3461_;
goto v___jp_3446_;
}
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
lean_dec(v_auxDecl_x3f_3454_);
lean_dec_ref(v_view_3434_);
v___x_3483_ = lean_box(0);
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
return v___x_3484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3506_, lean_object* v_findLocalDecl_x3f_3507_, lean_object* v_n_3508_, lean_object* v_projs_3509_, lean_object* v_auxDecl_x3f_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3506_, v_findLocalDecl_x3f_3507_, v_n_3508_, v_projs_3509_, v_auxDecl_x3f_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3519_, lean_object* v_givenName_3520_, lean_object* v_as_3521_, lean_object* v_i_3522_){
_start:
{
lean_object* v_zero_3523_; uint8_t v_isZero_3524_; 
v_zero_3523_ = lean_unsigned_to_nat(0u);
v_isZero_3524_ = lean_nat_dec_eq(v_i_3522_, v_zero_3523_);
if (v_isZero_3524_ == 1)
{
lean_object* v___x_3525_; 
lean_dec(v_i_3522_);
v___x_3525_ = lean_box(0);
return v___x_3525_;
}
else
{
lean_object* v_one_3526_; lean_object* v_n_3527_; lean_object* v___x_3528_; 
v_one_3526_ = lean_unsigned_to_nat(1u);
v_n_3527_ = lean_nat_sub(v_i_3522_, v_one_3526_);
lean_dec(v_i_3522_);
v___x_3528_ = lean_array_fget_borrowed(v_as_3521_, v_n_3527_);
if (lean_obj_tag(v___x_3528_) == 0)
{
v_i_3522_ = v_n_3527_;
goto _start;
}
else
{
lean_object* v_val_3530_; uint8_t v___x_3531_; 
v_val_3530_ = lean_ctor_get(v___x_3528_, 0);
v___x_3531_ = l_Lean_LocalDecl_isAuxDecl(v_val_3530_);
if (v___x_3531_ == 0)
{
if (lean_obj_tag(v_localDecl_x3f_3519_) == 0)
{
v_i_3522_ = v_n_3527_;
goto _start;
}
else
{
lean_dec(v_n_3527_);
lean_inc_ref(v_localDecl_x3f_3519_);
return v_localDecl_x3f_3519_;
}
}
else
{
lean_object* v___x_3533_; uint8_t v___x_3534_; 
v___x_3533_ = l_Lean_LocalDecl_userName(v_val_3530_);
v___x_3534_ = lean_name_eq(v___x_3533_, v_givenName_3520_);
lean_dec(v___x_3533_);
if (v___x_3534_ == 0)
{
v_i_3522_ = v_n_3527_;
goto _start;
}
else
{
lean_dec(v_n_3527_);
lean_inc_ref(v___x_3528_);
return v___x_3528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3536_, lean_object* v_givenName_3537_, lean_object* v_as_3538_, lean_object* v_i_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3536_, v_givenName_3537_, v_as_3538_, v_i_3539_);
lean_dec_ref(v_as_3538_);
lean_dec(v_givenName_3537_);
lean_dec(v_localDecl_x3f_3536_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3541_, lean_object* v_givenName_3542_, lean_object* v_as_3543_, lean_object* v_i_3544_){
_start:
{
lean_object* v_zero_3545_; uint8_t v_isZero_3546_; 
v_zero_3545_ = lean_unsigned_to_nat(0u);
v_isZero_3546_ = lean_nat_dec_eq(v_i_3544_, v_zero_3545_);
if (v_isZero_3546_ == 1)
{
lean_object* v___x_3547_; 
lean_dec(v_i_3544_);
v___x_3547_ = lean_box(0);
return v___x_3547_;
}
else
{
lean_object* v_one_3548_; lean_object* v_n_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v_one_3548_ = lean_unsigned_to_nat(1u);
v_n_3549_ = lean_nat_sub(v_i_3544_, v_one_3548_);
lean_dec(v_i_3544_);
v___x_3550_ = lean_array_fget_borrowed(v_as_3543_, v_n_3549_);
v___x_3551_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3541_, v_givenName_3542_, v___x_3550_);
if (lean_obj_tag(v___x_3551_) == 0)
{
v_i_3544_ = v_n_3549_;
goto _start;
}
else
{
lean_dec(v_n_3549_);
return v___x_3551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3553_, lean_object* v_givenName_3554_, lean_object* v_x_3555_){
_start:
{
if (lean_obj_tag(v_x_3555_) == 0)
{
lean_object* v_cs_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_cs_3556_ = lean_ctor_get(v_x_3555_, 0);
v___x_3557_ = lean_array_get_size(v_cs_3556_);
v___x_3558_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3553_, v_givenName_3554_, v_cs_3556_, v___x_3557_);
return v___x_3558_;
}
else
{
lean_object* v_vs_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v_vs_3559_ = lean_ctor_get(v_x_3555_, 0);
v___x_3560_ = lean_array_get_size(v_vs_3559_);
v___x_3561_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3553_, v_givenName_3554_, v_vs_3559_, v___x_3560_);
return v___x_3561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3562_, lean_object* v_givenName_3563_, lean_object* v_x_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3562_, v_givenName_3563_, v_x_3564_);
lean_dec_ref(v_x_3564_);
lean_dec(v_givenName_3563_);
lean_dec(v_localDecl_x3f_3562_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3566_, lean_object* v_givenName_3567_, lean_object* v_as_3568_, lean_object* v_i_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3566_, v_givenName_3567_, v_as_3568_, v_i_3569_);
lean_dec_ref(v_as_3568_);
lean_dec(v_givenName_3567_);
lean_dec(v_localDecl_x3f_3566_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3571_, lean_object* v_givenName_3572_, lean_object* v_t_3573_){
_start:
{
lean_object* v_root_3574_; lean_object* v_tail_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v_root_3574_ = lean_ctor_get(v_t_3573_, 0);
v_tail_3575_ = lean_ctor_get(v_t_3573_, 1);
v___x_3576_ = lean_array_get_size(v_tail_3575_);
v___x_3577_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3571_, v_givenName_3572_, v_tail_3575_, v___x_3576_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3571_, v_givenName_3572_, v_root_3574_);
return v___x_3578_;
}
else
{
return v___x_3577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3579_, lean_object* v_givenName_3580_, lean_object* v_t_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3579_, v_givenName_3580_, v_t_3581_);
lean_dec_ref(v_t_3581_);
lean_dec(v_givenName_3580_);
lean_dec(v_localDecl_x3f_3579_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3583_, lean_object* v_k_3584_){
_start:
{
if (lean_obj_tag(v_t_3583_) == 0)
{
lean_object* v_k_3585_; lean_object* v_v_3586_; lean_object* v_l_3587_; lean_object* v_r_3588_; uint8_t v___x_3589_; 
v_k_3585_ = lean_ctor_get(v_t_3583_, 1);
v_v_3586_ = lean_ctor_get(v_t_3583_, 2);
v_l_3587_ = lean_ctor_get(v_t_3583_, 3);
v_r_3588_ = lean_ctor_get(v_t_3583_, 4);
v___x_3589_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3584_, v_k_3585_);
switch(v___x_3589_)
{
case 0:
{
v_t_3583_ = v_l_3587_;
goto _start;
}
case 1:
{
lean_object* v___x_3591_; 
lean_inc(v_v_3586_);
v___x_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3591_, 0, v_v_3586_);
return v___x_3591_;
}
default: 
{
v_t_3583_ = v_r_3588_;
goto _start;
}
}
}
else
{
lean_object* v___x_3593_; 
v___x_3593_ = lean_box(0);
return v___x_3593_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3594_, lean_object* v_k_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3594_, v_k_3595_);
lean_dec(v_k_3595_);
lean_dec(v_t_3594_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3597_, lean_object* v_givenName_3598_){
_start:
{
lean_object* v___x_3599_; uint8_t v___x_3600_; 
v___x_3599_ = l_Lean_LocalDecl_userName(v_localDecl_3597_);
v___x_3600_ = lean_name_eq(v___x_3599_, v_givenName_3598_);
lean_dec(v___x_3599_);
if (v___x_3600_ == 0)
{
lean_object* v___x_3601_; 
lean_dec_ref(v_localDecl_3597_);
v___x_3601_ = lean_box(0);
return v___x_3601_;
}
else
{
lean_object* v___x_3602_; 
v___x_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3602_, 0, v_localDecl_3597_);
return v___x_3602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3603_, lean_object* v_givenName_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3603_, v_givenName_3604_);
lean_dec(v_givenName_3604_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3606_, lean_object* v_auxDeclToFullName_3607_, lean_object* v___x_3608_, lean_object* v_givenNameView_3609_, lean_object* v_as_3610_, lean_object* v_i_3611_){
_start:
{
lean_object* v_zero_3612_; uint8_t v_isZero_3613_; 
v_zero_3612_ = lean_unsigned_to_nat(0u);
v_isZero_3613_ = lean_nat_dec_eq(v_i_3611_, v_zero_3612_);
if (v_isZero_3613_ == 1)
{
lean_object* v___x_3614_; 
lean_dec(v_i_3611_);
lean_dec_ref(v_givenNameView_3609_);
lean_dec(v___x_3608_);
v___x_3614_ = lean_box(0);
return v___x_3614_;
}
else
{
lean_object* v_one_3615_; lean_object* v_n_3616_; lean_object* v___y_3618_; lean_object* v___x_3620_; 
v_one_3615_ = lean_unsigned_to_nat(1u);
v_n_3616_ = lean_nat_sub(v_i_3611_, v_one_3615_);
lean_dec(v_i_3611_);
v___x_3620_ = lean_array_fget_borrowed(v_as_3610_, v_n_3616_);
if (lean_obj_tag(v___x_3620_) == 0)
{
v_i_3611_ = v_n_3616_;
goto _start;
}
else
{
lean_object* v_val_3622_; uint8_t v___x_3623_; 
v_val_3622_ = lean_ctor_get(v___x_3620_, 0);
v___x_3623_ = l_Lean_LocalDecl_isAuxDecl(v_val_3622_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; 
lean_inc(v_val_3622_);
v___x_3624_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3622_, v_givenName_3606_);
v___y_3618_ = v___x_3624_;
goto v___jp_3617_;
}
else
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = l_Lean_LocalDecl_fvarId(v_val_3622_);
v___x_3626_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3607_, v___x_3625_);
lean_dec(v___x_3625_);
if (lean_obj_tag(v___x_3626_) == 1)
{
lean_object* v_val_3627_; lean_object* v_fullDeclView_3628_; lean_object* v_name_3629_; lean_object* v_imported_3630_; lean_object* v_ctx_3631_; lean_object* v_scopes_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3652_; 
v_val_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_val_3627_);
lean_dec_ref_known(v___x_3626_, 1);
v_fullDeclView_3628_ = l_Lean_extractMacroScopes(v_val_3627_);
v_name_3629_ = lean_ctor_get(v_fullDeclView_3628_, 0);
v_imported_3630_ = lean_ctor_get(v_fullDeclView_3628_, 1);
v_ctx_3631_ = lean_ctor_get(v_fullDeclView_3628_, 2);
v_scopes_3632_ = lean_ctor_get(v_fullDeclView_3628_, 3);
v_isSharedCheck_3652_ = !lean_is_exclusive(v_fullDeclView_3628_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3634_ = v_fullDeclView_3628_;
v_isShared_3635_ = v_isSharedCheck_3652_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_scopes_3632_);
lean_inc(v_ctx_3631_);
lean_inc(v_imported_3630_);
lean_inc(v_name_3629_);
lean_dec(v_fullDeclView_3628_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3652_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___y_3637_; lean_object* v___x_3650_; 
lean_inc(v_name_3629_);
v___x_3650_ = l_Lean_privateToUserName_x3f(v_name_3629_);
if (lean_obj_tag(v___x_3650_) == 0)
{
v___y_3637_ = v_name_3629_;
goto v___jp_3636_;
}
else
{
lean_object* v_val_3651_; 
lean_dec(v_name_3629_);
v_val_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_val_3651_);
lean_dec_ref_known(v___x_3650_, 1);
v___y_3637_ = v_val_3651_;
goto v___jp_3636_;
}
v___jp_3636_:
{
lean_object* v_fullDeclView_3639_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___y_3637_);
v_fullDeclView_3639_ = v___x_3634_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___y_3637_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_imported_3630_);
lean_ctor_set(v_reuseFailAlloc_3649_, 2, v_ctx_3631_);
lean_ctor_set(v_reuseFailAlloc_3649_, 3, v_scopes_3632_);
v_fullDeclView_3639_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v_fullDeclName_3640_; uint8_t v___x_3641_; 
lean_inc_ref(v_fullDeclView_3639_);
v_fullDeclName_3640_ = l_Lean_MacroScopesView_review(v_fullDeclView_3639_);
v___x_3641_ = l_Lean_Name_isPrefixOf(v___x_3608_, v_fullDeclName_3640_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; 
lean_dec_ref(v_fullDeclView_3639_);
lean_inc(v___x_3608_);
lean_inc_ref(v_givenNameView_3609_);
lean_inc(v_val_3622_);
v___x_3642_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3622_, v_givenNameView_3609_, v_fullDeclName_3640_, v___x_3608_);
lean_dec(v_fullDeclName_3640_);
v___y_3618_ = v___x_3642_;
goto v___jp_3617_;
}
else
{
lean_object* v___x_3643_; lean_object* v_localDeclNameView_3644_; uint8_t v___x_3645_; 
lean_dec(v_fullDeclName_3640_);
v___x_3643_ = l_Lean_LocalDecl_userName(v_val_3622_);
v_localDeclNameView_3644_ = l_Lean_extractMacroScopes(v___x_3643_);
v___x_3645_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3644_, v_givenNameView_3609_);
lean_dec_ref(v_localDeclNameView_3644_);
if (v___x_3645_ == 0)
{
lean_dec_ref(v_fullDeclView_3639_);
v_i_3611_ = v_n_3616_;
goto _start;
}
else
{
uint8_t v___x_3647_; 
v___x_3647_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3609_, v_fullDeclView_3639_);
lean_dec_ref(v_fullDeclView_3639_);
if (v___x_3647_ == 0)
{
v_i_3611_ = v_n_3616_;
goto _start;
}
else
{
lean_dec(v_n_3616_);
lean_dec_ref(v_givenNameView_3609_);
lean_dec(v___x_3608_);
lean_inc_ref(v___x_3620_);
return v___x_3620_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3653_; 
lean_dec(v___x_3626_);
lean_inc(v_val_3622_);
v___x_3653_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3622_, v_givenName_3606_);
v___y_3618_ = v___x_3653_;
goto v___jp_3617_;
}
}
}
v___jp_3617_:
{
if (lean_obj_tag(v___y_3618_) == 0)
{
v_i_3611_ = v_n_3616_;
goto _start;
}
else
{
lean_dec(v_n_3616_);
lean_dec_ref(v_givenNameView_3609_);
lean_dec(v___x_3608_);
return v___y_3618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3654_, lean_object* v_auxDeclToFullName_3655_, lean_object* v___x_3656_, lean_object* v_givenNameView_3657_, lean_object* v_as_3658_, lean_object* v_i_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3654_, v_auxDeclToFullName_3655_, v___x_3656_, v_givenNameView_3657_, v_as_3658_, v_i_3659_);
lean_dec_ref(v_as_3658_);
lean_dec(v_auxDeclToFullName_3655_);
lean_dec(v_givenName_3654_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3661_, lean_object* v_auxDeclToFullName_3662_, lean_object* v___x_3663_, lean_object* v_givenNameView_3664_, lean_object* v_as_3665_, lean_object* v_i_3666_){
_start:
{
lean_object* v_zero_3667_; uint8_t v_isZero_3668_; 
v_zero_3667_ = lean_unsigned_to_nat(0u);
v_isZero_3668_ = lean_nat_dec_eq(v_i_3666_, v_zero_3667_);
if (v_isZero_3668_ == 1)
{
lean_object* v___x_3669_; 
lean_dec(v_i_3666_);
lean_dec_ref(v_givenNameView_3664_);
lean_dec(v___x_3663_);
v___x_3669_ = lean_box(0);
return v___x_3669_;
}
else
{
lean_object* v_one_3670_; lean_object* v_n_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v_one_3670_ = lean_unsigned_to_nat(1u);
v_n_3671_ = lean_nat_sub(v_i_3666_, v_one_3670_);
lean_dec(v_i_3666_);
v___x_3672_ = lean_array_fget_borrowed(v_as_3665_, v_n_3671_);
lean_inc_ref(v_givenNameView_3664_);
lean_inc(v___x_3663_);
v___x_3673_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3661_, v_auxDeclToFullName_3662_, v___x_3663_, v_givenNameView_3664_, v___x_3672_);
if (lean_obj_tag(v___x_3673_) == 0)
{
v_i_3666_ = v_n_3671_;
goto _start;
}
else
{
lean_dec(v_n_3671_);
lean_dec_ref(v_givenNameView_3664_);
lean_dec(v___x_3663_);
return v___x_3673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3675_, lean_object* v_auxDeclToFullName_3676_, lean_object* v___x_3677_, lean_object* v_givenNameView_3678_, lean_object* v_x_3679_){
_start:
{
if (lean_obj_tag(v_x_3679_) == 0)
{
lean_object* v_cs_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v_cs_3680_ = lean_ctor_get(v_x_3679_, 0);
v___x_3681_ = lean_array_get_size(v_cs_3680_);
v___x_3682_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3675_, v_auxDeclToFullName_3676_, v___x_3677_, v_givenNameView_3678_, v_cs_3680_, v___x_3681_);
return v___x_3682_;
}
else
{
lean_object* v_vs_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v_vs_3683_ = lean_ctor_get(v_x_3679_, 0);
v___x_3684_ = lean_array_get_size(v_vs_3683_);
v___x_3685_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3675_, v_auxDeclToFullName_3676_, v___x_3677_, v_givenNameView_3678_, v_vs_3683_, v___x_3684_);
return v___x_3685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3686_, lean_object* v_auxDeclToFullName_3687_, lean_object* v___x_3688_, lean_object* v_givenNameView_3689_, lean_object* v_x_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3686_, v_auxDeclToFullName_3687_, v___x_3688_, v_givenNameView_3689_, v_x_3690_);
lean_dec_ref(v_x_3690_);
lean_dec(v_auxDeclToFullName_3687_);
lean_dec(v_givenName_3686_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3692_, lean_object* v_auxDeclToFullName_3693_, lean_object* v___x_3694_, lean_object* v_givenNameView_3695_, lean_object* v_as_3696_, lean_object* v_i_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3692_, v_auxDeclToFullName_3693_, v___x_3694_, v_givenNameView_3695_, v_as_3696_, v_i_3697_);
lean_dec_ref(v_as_3696_);
lean_dec(v_auxDeclToFullName_3693_);
lean_dec(v_givenName_3692_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3699_, lean_object* v_auxDeclToFullName_3700_, lean_object* v___x_3701_, lean_object* v_givenNameView_3702_, lean_object* v_t_3703_){
_start:
{
lean_object* v_root_3704_; lean_object* v_tail_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_root_3704_ = lean_ctor_get(v_t_3703_, 0);
v_tail_3705_ = lean_ctor_get(v_t_3703_, 1);
v___x_3706_ = lean_array_get_size(v_tail_3705_);
lean_inc_ref(v_givenNameView_3702_);
lean_inc(v___x_3701_);
v___x_3707_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3699_, v_auxDeclToFullName_3700_, v___x_3701_, v_givenNameView_3702_, v_tail_3705_, v___x_3706_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v___x_3708_; 
v___x_3708_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3699_, v_auxDeclToFullName_3700_, v___x_3701_, v_givenNameView_3702_, v_root_3704_);
return v___x_3708_;
}
else
{
lean_dec_ref(v_givenNameView_3702_);
lean_dec(v___x_3701_);
return v___x_3707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3709_, lean_object* v_auxDeclToFullName_3710_, lean_object* v___x_3711_, lean_object* v_givenNameView_3712_, lean_object* v_t_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3709_, v_auxDeclToFullName_3710_, v___x_3711_, v_givenNameView_3712_, v_t_3713_);
lean_dec_ref(v_t_3713_);
lean_dec(v_auxDeclToFullName_3710_);
lean_dec(v_givenName_3709_);
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3715_, lean_object* v_currNamespace_3716_, lean_object* v_decls_3717_, lean_object* v_givenNameView_3718_){
_start:
{
lean_object* v_givenName_3719_; lean_object* v_localDecl_x3f_3720_; 
lean_inc_ref(v_givenNameView_3718_);
v_givenName_3719_ = l_Lean_MacroScopesView_review(v_givenNameView_3718_);
v_localDecl_x3f_3720_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3719_, v_auxDeclToFullName_3715_, v_currNamespace_3716_, v_givenNameView_3718_, v_decls_3717_);
if (lean_obj_tag(v_localDecl_x3f_3720_) == 0)
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3720_, v_givenName_3719_, v_decls_3717_);
lean_dec(v_givenName_3719_);
return v___x_3721_;
}
else
{
lean_dec(v_givenName_3719_);
return v_localDecl_x3f_3720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3722_, lean_object* v_currNamespace_3723_, lean_object* v_decls_3724_, lean_object* v_givenNameView_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3722_, v_currNamespace_3723_, v_decls_3724_, v_givenNameView_3725_);
lean_dec_ref(v_decls_3724_);
lean_dec(v_auxDeclToFullName_3722_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v_lctx_3735_; lean_object* v_toCold_3736_; lean_object* v_decls_3737_; lean_object* v_auxDeclToFullName_3738_; lean_object* v_currNamespace_3739_; lean_object* v_view_3740_; lean_object* v_name_3741_; lean_object* v_findLocalDecl_x3f_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_lctx_3735_ = lean_ctor_get(v___y_3730_, 2);
v_toCold_3736_ = lean_ctor_get(v___y_3732_, 0);
v_decls_3737_ = lean_ctor_get(v_lctx_3735_, 1);
v_auxDeclToFullName_3738_ = lean_ctor_get(v_lctx_3735_, 2);
v_currNamespace_3739_ = lean_ctor_get(v_toCold_3736_, 4);
v_view_3740_ = l_Lean_extractMacroScopes(v_n_3727_);
v_name_3741_ = lean_ctor_get(v_view_3740_, 0);
lean_inc(v_name_3741_);
lean_inc_ref(v_decls_3737_);
lean_inc(v_currNamespace_3739_);
lean_inc(v_auxDeclToFullName_3738_);
v_findLocalDecl_x3f_3742_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 4, 3);
lean_closure_set(v_findLocalDecl_x3f_3742_, 0, v_auxDeclToFullName_3738_);
lean_closure_set(v_findLocalDecl_x3f_3742_, 1, v_currNamespace_3739_);
lean_closure_set(v_findLocalDecl_x3f_3742_, 2, v_decls_3737_);
v___x_3743_ = lean_box(0);
v___x_3744_ = lean_box(0);
v___x_3745_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3740_, v_findLocalDecl_x3f_3742_, v_name_3741_, v___x_3743_, v___x_3744_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3755_, lean_object* v_b_3756_){
_start:
{
if (lean_obj_tag(v_as_x27_3755_) == 0)
{
lean_object* v___x_3758_; 
v___x_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3758_, 0, v_b_3756_);
return v___x_3758_;
}
else
{
lean_object* v_head_3759_; lean_object* v_tail_3760_; lean_object* v_config_3761_; lean_object* v_identity_3762_; lean_object* v_extensions_3763_; lean_object* v_extra_3764_; lean_object* v_extraInj_3765_; lean_object* v_extraFacts_3766_; lean_object* v_symPrios_3767_; lean_object* v_norm_3768_; lean_object* v_normProcs_3769_; lean_object* v_anchorRefs_x3f_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3779_; 
v_head_3759_ = lean_ctor_get(v_as_x27_3755_, 0);
v_tail_3760_ = lean_ctor_get(v_as_x27_3755_, 1);
v_config_3761_ = lean_ctor_get(v_b_3756_, 0);
v_identity_3762_ = lean_ctor_get(v_b_3756_, 1);
v_extensions_3763_ = lean_ctor_get(v_b_3756_, 2);
v_extra_3764_ = lean_ctor_get(v_b_3756_, 3);
v_extraInj_3765_ = lean_ctor_get(v_b_3756_, 4);
v_extraFacts_3766_ = lean_ctor_get(v_b_3756_, 5);
v_symPrios_3767_ = lean_ctor_get(v_b_3756_, 6);
v_norm_3768_ = lean_ctor_get(v_b_3756_, 7);
v_normProcs_3769_ = lean_ctor_get(v_b_3756_, 8);
v_anchorRefs_x3f_3770_ = lean_ctor_get(v_b_3756_, 9);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_b_3756_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3772_ = v_b_3756_;
v_isShared_3773_ = v_isSharedCheck_3779_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_anchorRefs_x3f_3770_);
lean_inc(v_normProcs_3769_);
lean_inc(v_norm_3768_);
lean_inc(v_symPrios_3767_);
lean_inc(v_extraFacts_3766_);
lean_inc(v_extraInj_3765_);
lean_inc(v_extra_3764_);
lean_inc(v_extensions_3763_);
lean_inc(v_identity_3762_);
lean_inc(v_config_3761_);
lean_dec(v_b_3756_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3779_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
lean_inc(v_head_3759_);
v___x_3774_ = l_Lean_PersistentArray_push___redArg(v_extra_3764_, v_head_3759_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 3, v___x_3774_);
v___x_3776_ = v___x_3772_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_config_3761_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_identity_3762_);
lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_extensions_3763_);
lean_ctor_set(v_reuseFailAlloc_3778_, 3, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3778_, 4, v_extraInj_3765_);
lean_ctor_set(v_reuseFailAlloc_3778_, 5, v_extraFacts_3766_);
lean_ctor_set(v_reuseFailAlloc_3778_, 6, v_symPrios_3767_);
lean_ctor_set(v_reuseFailAlloc_3778_, 7, v_norm_3768_);
lean_ctor_set(v_reuseFailAlloc_3778_, 8, v_normProcs_3769_);
lean_ctor_set(v_reuseFailAlloc_3778_, 9, v_anchorRefs_x3f_3770_);
v___x_3776_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
v_as_x27_3755_ = v_tail_3760_;
v_b_3756_ = v___x_3776_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3780_, lean_object* v_b_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3780_, v_b_3781_);
lean_dec(v_as_x27_3780_);
return v_res_3783_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3786_ = l_Lean_stringToMessageData(v___x_3785_);
return v___x_3786_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3789_ = l_Lean_stringToMessageData(v___x_3788_);
return v___x_3789_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3792_ = l_Lean_stringToMessageData(v___x_3791_);
return v___x_3792_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3794_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3795_ = l_Lean_stringToMessageData(v___x_3794_);
return v___x_3795_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3798_ = l_Lean_stringToMessageData(v___x_3797_);
return v___x_3798_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3801_ = l_Lean_stringToMessageData(v___x_3800_);
return v___x_3801_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3804_ = l_Lean_stringToMessageData(v___x_3803_);
return v___x_3804_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3806_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3807_ = l_Lean_stringToMessageData(v___x_3806_);
return v___x_3807_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3809_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3810_ = l_Lean_stringToMessageData(v___x_3809_);
return v___x_3810_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3813_ = l_Lean_stringToMessageData(v___x_3812_);
return v___x_3813_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3815_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3816_ = l_Lean_stringToMessageData(v___x_3815_);
return v___x_3816_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23(void){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3818_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22));
v___x_3819_ = l_Lean_stringToMessageData(v___x_3818_);
return v___x_3819_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25(void){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3821_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24));
v___x_3822_ = l_Lean_stringToMessageData(v___x_3821_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3823_, lean_object* v_p_3824_, lean_object* v_mod_x3f_3825_, lean_object* v_id_3826_, uint8_t v_minIndexable_3827_, uint8_t v_only_3828_, uint8_t v_incremental_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_){
_start:
{
lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3848_; uint8_t v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3941_; uint8_t v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v_a_4016_; lean_object* v___y_4240_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4251_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4252_ = lean_box(0);
lean_inc(v_id_3826_);
v___x_4253_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3826_, v___x_4252_, v_a_3834_, v_a_3835_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
v_a_4016_ = v_a_4254_;
goto v___jp_4015_;
}
else
{
lean_object* v_a_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4330_; 
v_a_4255_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4257_ = v___x_4253_;
v_isShared_4258_ = v_isSharedCheck_4330_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_a_4255_);
lean_dec(v___x_4253_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4330_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
uint8_t v___x_4259_; 
v___x_4259_ = l_Lean_Exception_isInterrupt(v_a_4255_);
if (v___x_4259_ == 0)
{
uint8_t v___x_4260_; 
lean_inc(v_a_4255_);
v___x_4260_ = l_Lean_Exception_isRuntime(v_a_4255_);
if (v___x_4260_ == 0)
{
lean_object* v___x_4261_; lean_object* v___x_4262_; 
lean_del_object(v___x_4257_);
v___x_4261_ = l_Lean_TSyntax_getId(v_id_3826_);
lean_inc(v___x_4261_);
v___x_4262_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4261_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
if (lean_obj_tag(v_a_4263_) == 0)
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_4261_, v_a_3834_, v_a_3835_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4293_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4267_ = v___x_4264_;
v_isShared_4268_ = v_isSharedCheck_4293_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4264_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4293_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
if (lean_obj_tag(v_a_4265_) == 1)
{
lean_del_object(v___x_4267_);
lean_dec(v_a_4255_);
if (lean_obj_tag(v_mod_x3f_3825_) == 1)
{
lean_object* v_val_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
lean_dec_ref_known(v_a_4265_, 1);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_val_4269_ = lean_ctor_get(v_mod_x3f_3825_, 0);
lean_inc(v_val_4269_);
lean_dec_ref_known(v_mod_x3f_3825_, 1);
v___x_4270_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4271_ = l_Lean_MessageData_ofName(v___x_4261_);
v___x_4272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4270_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
v___x_4273_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4272_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v___x_4275_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4269_, v___x_4274_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
lean_dec(v_val_4269_);
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4275_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4275_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
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
lean_object* v_val_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
lean_dec(v___x_4261_);
v_val_4284_ = lean_ctor_get(v_a_4265_, 0);
lean_inc(v_val_4284_);
lean_dec_ref_known(v_a_4265_, 1);
v___x_4285_ = lean_box(0);
lean_inc_ref(v_params_3823_);
v___x_4286_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3823_, v_val_4284_, v___x_4251_, v___x_4260_, v___x_4285_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
lean_dec(v_val_4284_);
v___y_4240_ = v___x_4286_;
goto v___jp_4239_;
}
}
else
{
lean_object* v___x_4287_; uint8_t v___x_4288_; 
lean_dec(v_a_4265_);
v___x_4287_ = l_Lean_Name_getPrefix(v___x_4261_);
lean_dec(v___x_4261_);
v___x_4288_ = l_Lean_Name_isAnonymous(v___x_4287_);
lean_dec(v___x_4287_);
if (v___x_4288_ == 0)
{
lean_object* v___x_4289_; 
lean_del_object(v___x_4267_);
lean_dec(v_a_4255_);
v___x_4289_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3823_, v_p_3824_, v_mod_x3f_3825_, v_id_3826_, v_minIndexable_3827_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
return v___x_4289_;
}
else
{
lean_object* v___x_4291_; 
lean_dec(v_id_3826_);
lean_dec(v_mod_x3f_3825_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
if (v_isShared_4268_ == 0)
{
lean_ctor_set_tag(v___x_4267_, 1);
lean_ctor_set(v___x_4267_, 0, v_a_4255_);
v___x_4291_ = v___x_4267_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4255_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
}
}
else
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
lean_dec(v___x_4261_);
lean_dec(v_a_4255_);
lean_dec(v_id_3826_);
lean_dec(v_mod_x3f_3825_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_a_4294_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4296_ = v___x_4264_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4264_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
}
else
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref_known(v_a_4263_, 1);
lean_dec(v___x_4261_);
lean_dec(v_a_4255_);
lean_dec(v_mod_x3f_3825_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v___x_4302_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23);
lean_inc(v_id_3826_);
v___x_4303_ = l_Lean_MessageData_ofSyntax(v_id_3826_);
v___x_4304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4302_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
v___x_4305_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25);
v___x_4306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4304_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3826_, v___x_4306_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
lean_dec(v_id_3826_);
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4307_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4307_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
lean_dec(v___x_4261_);
lean_dec(v_a_4255_);
lean_dec(v_id_3826_);
lean_dec(v_mod_x3f_3825_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_a_4316_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4262_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4262_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
else
{
lean_object* v___x_4325_; 
lean_dec(v_id_3826_);
lean_dec(v_mod_x3f_3825_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
if (v_isShared_4258_ == 0)
{
v___x_4325_ = v___x_4257_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4255_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
else
{
lean_object* v___x_4328_; 
lean_dec(v_id_3826_);
lean_dec(v_mod_x3f_3825_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
if (v_isShared_4258_ == 0)
{
v___x_4328_ = v___x_4257_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4255_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
v___jp_3837_:
{
lean_object* v_ctors_3845_; lean_object* v___x_3846_; 
v_ctors_3845_ = lean_ctor_get(v___y_3838_, 4);
lean_inc(v_ctors_3845_);
lean_dec_ref(v___y_3838_);
v___x_3846_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3824_, v_id_3826_, v_minIndexable_3827_, v_ctors_3845_, v_params_3823_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
lean_dec(v_ctors_3845_);
lean_dec(v_p_3824_);
return v___x_3846_;
}
v___jp_3847_:
{
lean_object* v___x_3854_; 
v___x_3854_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3827_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_toCold_3855_; lean_object* v_currRecDepth_3856_; lean_object* v_ref_3857_; uint16_t v_optionFlags_3858_; uint8_t v_suppressElabErrors_3859_; uint8_t v_checkDeprecated_3860_; uint8_t v_isRecordingDeps_3861_; lean_object* v_ref_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
lean_dec_ref_known(v___x_3854_, 1);
v_toCold_3855_ = lean_ctor_get(v___y_3852_, 0);
v_currRecDepth_3856_ = lean_ctor_get(v___y_3852_, 1);
v_ref_3857_ = lean_ctor_get(v___y_3852_, 2);
v_optionFlags_3858_ = lean_ctor_get_uint16(v___y_3852_, sizeof(void*)*3);
v_suppressElabErrors_3859_ = lean_ctor_get_uint8(v___y_3852_, sizeof(void*)*3 + 2);
v_checkDeprecated_3860_ = lean_ctor_get_uint8(v___y_3852_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3861_ = lean_ctor_get_uint8(v___y_3852_, sizeof(void*)*3 + 4);
v_ref_3862_ = l_Lean_replaceRef(v_p_3824_, v_ref_3857_);
lean_dec(v_p_3824_);
lean_inc(v_currRecDepth_3856_);
lean_inc_ref(v_toCold_3855_);
v___x_3863_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3863_, 0, v_toCold_3855_);
lean_ctor_set(v___x_3863_, 1, v_currRecDepth_3856_);
lean_ctor_set(v___x_3863_, 2, v_ref_3862_);
lean_ctor_set_uint16(v___x_3863_, sizeof(void*)*3, v_optionFlags_3858_);
lean_ctor_set_uint8(v___x_3863_, sizeof(void*)*3 + 2, v_suppressElabErrors_3859_);
lean_ctor_set_uint8(v___x_3863_, sizeof(void*)*3 + 3, v_checkDeprecated_3860_);
lean_ctor_set_uint8(v___x_3863_, sizeof(void*)*3 + 4, v_isRecordingDeps_3861_);
lean_inc(v___y_3848_);
v___x_3864_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3848_, v___y_3849_, v___x_3863_, v___y_3853_);
lean_dec_ref_known(v___x_3863_, 3);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3872_; 
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3872_ == 0)
{
lean_object* v_unused_3873_; 
v_unused_3873_ = lean_ctor_get(v___x_3864_, 0);
lean_dec(v_unused_3873_);
v___x_3866_ = v___x_3864_;
v_isShared_3867_ = v_isSharedCheck_3872_;
goto v_resetjp_3865_;
}
else
{
lean_dec(v___x_3864_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3872_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3868_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3823_, v___y_3848_, v___y_3849_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 0, v___x_3868_);
v___x_3870_ = v___x_3866_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec(v___y_3848_);
lean_dec_ref(v_params_3823_);
v_a_3874_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3864_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3864_);
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
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
lean_dec(v___y_3848_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_a_3882_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3854_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3854_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
v___jp_3890_:
{
lean_object* v___x_3899_; 
v___x_3899_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3827_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
lean_dec_ref_known(v___x_3899_, 1);
v___x_3900_ = l_Lean_Meta_Grind_grindExt;
v___x_3901_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3900_, v___y_3898_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3902_);
lean_dec_ref_known(v___x_3901_, 1);
lean_inc(v___y_3891_);
v___x_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3903_, 0, v___y_3891_);
v___x_3904_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3902_, v___x_3903_);
lean_dec_ref_known(v___x_3903_, 1);
lean_dec(v_a_3902_);
v___x_3905_ = lean_box(0);
v___x_3906_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3892_, v___x_3904_, v___x_3905_);
lean_dec(v___y_3892_);
v___x_3907_ = l_List_isEmpty___redArg(v___x_3906_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; 
lean_dec(v___y_3891_);
lean_dec(v_p_3824_);
v___x_3908_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3906_, v_params_3823_);
lean_dec(v___x_3906_);
return v___x_3908_;
}
else
{
lean_object* v___x_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec(v___x_3906_);
lean_dec_ref(v_params_3823_);
v___x_3909_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3910_ = 0;
v___x_3911_ = l_Lean_MessageData_ofConstName(v___y_3891_, v___x_3910_);
v___x_3912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3909_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3912_);
lean_ctor_set(v___x_3914_, 1, v___x_3913_);
v___x_3915_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3824_, v___x_3914_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v_p_3824_);
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3915_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3915_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_a_3924_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3901_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3901_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_a_3932_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3899_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3899_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
v___jp_3940_:
{
uint8_t v___x_3949_; lean_object* v___x_3950_; 
v___x_3949_ = 0;
lean_inc(v___y_3941_);
v___x_3950_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3941_, v___x_3949_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref_known(v___x_3950_, 1);
if (lean_obj_tag(v_a_3951_) == 1)
{
lean_object* v_val_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
lean_dec(v___y_3941_);
v_val_3952_ = lean_ctor_get(v_a_3951_, 0);
lean_inc_n(v_val_3952_, 2);
lean_dec_ref_known(v_a_3951_, 1);
v___x_3953_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3823_, v_val_3952_, v___x_3949_);
v___x_3954_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3952_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3965_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3957_ = v___x_3954_;
v_isShared_3958_ = v_isSharedCheck_3965_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3954_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3965_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
if (lean_obj_tag(v_a_3955_) == 1)
{
lean_object* v_val_3959_; lean_object* v_ctors_3960_; lean_object* v___x_3961_; 
lean_del_object(v___x_3957_);
v_val_3959_ = lean_ctor_get(v_a_3955_, 0);
lean_inc(v_val_3959_);
lean_dec_ref_known(v_a_3955_, 1);
v_ctors_3960_ = lean_ctor_get(v_val_3959_, 4);
lean_inc(v_ctors_3960_);
lean_dec(v_val_3959_);
v___x_3961_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3824_, v_id_3826_, v_minIndexable_3827_, v_ctors_3960_, v___x_3953_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
lean_dec(v_ctors_3960_);
lean_dec(v_p_3824_);
return v___x_3961_;
}
else
{
lean_object* v___x_3963_; 
lean_dec(v_a_3955_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 0, v___x_3953_);
v___x_3963_ = v___x_3957_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3953_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec_ref(v___x_3953_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
v_a_3966_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3954_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3954_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
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
else
{
lean_object* v_symPrios_3974_; lean_object* v___x_3975_; 
lean_dec(v_a_3951_);
v_symPrios_3974_ = lean_ctor_get(v_params_3823_, 6);
lean_inc_ref(v_symPrios_3974_);
lean_inc(v___y_3941_);
v___x_3975_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(v___y_3941_, v_symPrios_3974_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; uint8_t v___x_3977_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_a_3976_);
lean_dec_ref_known(v___x_3975_, 1);
v___x_3977_ = lean_unbox(v_a_3976_);
lean_dec(v_a_3976_);
if (v___x_3977_ == 0)
{
lean_object* v_toCold_3978_; lean_object* v_currRecDepth_3979_; lean_object* v_ref_3980_; uint16_t v_optionFlags_3981_; uint8_t v_suppressElabErrors_3982_; uint8_t v_checkDeprecated_3983_; uint8_t v_isRecordingDeps_3984_; lean_object* v___x_3985_; lean_object* v_ref_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_toCold_3978_ = lean_ctor_get(v___y_3947_, 0);
v_currRecDepth_3979_ = lean_ctor_get(v___y_3947_, 1);
v_ref_3980_ = lean_ctor_get(v___y_3947_, 2);
v_optionFlags_3981_ = lean_ctor_get_uint16(v___y_3947_, sizeof(void*)*3);
v_suppressElabErrors_3982_ = lean_ctor_get_uint8(v___y_3947_, sizeof(void*)*3 + 2);
v_checkDeprecated_3983_ = lean_ctor_get_uint8(v___y_3947_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3984_ = lean_ctor_get_uint8(v___y_3947_, sizeof(void*)*3 + 4);
v___x_3985_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_ref_3986_ = l_Lean_replaceRef(v_p_3824_, v_ref_3980_);
lean_dec(v_p_3824_);
lean_inc(v_currRecDepth_3979_);
lean_inc_ref(v_toCold_3978_);
v___x_3987_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3987_, 0, v_toCold_3978_);
lean_ctor_set(v___x_3987_, 1, v_currRecDepth_3979_);
lean_ctor_set(v___x_3987_, 2, v_ref_3986_);
lean_ctor_set_uint16(v___x_3987_, sizeof(void*)*3, v_optionFlags_3981_);
lean_ctor_set_uint8(v___x_3987_, sizeof(void*)*3 + 2, v_suppressElabErrors_3982_);
lean_ctor_set_uint8(v___x_3987_, sizeof(void*)*3 + 3, v_checkDeprecated_3983_);
lean_ctor_set_uint8(v___x_3987_, sizeof(void*)*3 + 4, v_isRecordingDeps_3984_);
v___x_3988_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3823_, v_id_3826_, v___y_3941_, v___x_3985_, v_minIndexable_3827_, v___y_3942_, v___y_3942_, v___y_3945_, v___y_3946_, v___x_3987_, v___y_3948_);
lean_dec_ref_known(v___x_3987_, 3);
return v___x_3988_;
}
else
{
lean_object* v_toCold_3989_; lean_object* v_currRecDepth_3990_; lean_object* v_ref_3991_; uint16_t v_optionFlags_3992_; uint8_t v_suppressElabErrors_3993_; uint8_t v_checkDeprecated_3994_; uint8_t v_isRecordingDeps_3995_; lean_object* v_ref_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
lean_dec(v_id_3826_);
v_toCold_3989_ = lean_ctor_get(v___y_3947_, 0);
v_currRecDepth_3990_ = lean_ctor_get(v___y_3947_, 1);
v_ref_3991_ = lean_ctor_get(v___y_3947_, 2);
v_optionFlags_3992_ = lean_ctor_get_uint16(v___y_3947_, sizeof(void*)*3);
v_suppressElabErrors_3993_ = lean_ctor_get_uint8(v___y_3947_, sizeof(void*)*3 + 2);
v_checkDeprecated_3994_ = lean_ctor_get_uint8(v___y_3947_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3995_ = lean_ctor_get_uint8(v___y_3947_, sizeof(void*)*3 + 4);
v_ref_3996_ = l_Lean_replaceRef(v_p_3824_, v_ref_3991_);
lean_dec(v_p_3824_);
lean_inc(v_currRecDepth_3990_);
lean_inc_ref(v_toCold_3989_);
v___x_3997_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3997_, 0, v_toCold_3989_);
lean_ctor_set(v___x_3997_, 1, v_currRecDepth_3990_);
lean_ctor_set(v___x_3997_, 2, v_ref_3996_);
lean_ctor_set_uint16(v___x_3997_, sizeof(void*)*3, v_optionFlags_3992_);
lean_ctor_set_uint8(v___x_3997_, sizeof(void*)*3 + 2, v_suppressElabErrors_3993_);
lean_ctor_set_uint8(v___x_3997_, sizeof(void*)*3 + 3, v_checkDeprecated_3994_);
lean_ctor_set_uint8(v___x_3997_, sizeof(void*)*3 + 4, v_isRecordingDeps_3995_);
v___x_3998_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(v_params_3823_, v___y_3941_, v_minIndexable_3827_, v___y_3945_, v___y_3946_, v___x_3997_, v___y_3948_);
lean_dec_ref_known(v___x_3997_, 3);
return v___x_3998_;
}
}
else
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
lean_dec(v___y_3941_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_a_3999_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3975_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3975_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec(v___y_3941_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_a_4007_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3950_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3950_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
v___jp_4015_:
{
lean_object* v_toCold_4017_; lean_object* v_currRecDepth_4018_; lean_object* v_ref_4019_; uint16_t v_optionFlags_4020_; uint8_t v_suppressElabErrors_4021_; uint8_t v_checkDeprecated_4022_; uint8_t v_isRecordingDeps_4023_; uint8_t v___x_4024_; lean_object* v_ref_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v_toCold_4017_ = lean_ctor_get(v_a_3834_, 0);
v_currRecDepth_4018_ = lean_ctor_get(v_a_3834_, 1);
v_ref_4019_ = lean_ctor_get(v_a_3834_, 2);
v_optionFlags_4020_ = lean_ctor_get_uint16(v_a_3834_, sizeof(void*)*3);
v_suppressElabErrors_4021_ = lean_ctor_get_uint8(v_a_3834_, sizeof(void*)*3 + 2);
v_checkDeprecated_4022_ = lean_ctor_get_uint8(v_a_3834_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4023_ = lean_ctor_get_uint8(v_a_3834_, sizeof(void*)*3 + 4);
v___x_4024_ = 1;
v_ref_4025_ = l_Lean_replaceRef(v_id_3826_, v_ref_4019_);
lean_inc(v_currRecDepth_4018_);
lean_inc_ref(v_toCold_4017_);
v___x_4026_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4026_, 0, v_toCold_4017_);
lean_ctor_set(v___x_4026_, 1, v_currRecDepth_4018_);
lean_ctor_set(v___x_4026_, 2, v_ref_4025_);
lean_ctor_set_uint16(v___x_4026_, sizeof(void*)*3, v_optionFlags_4020_);
lean_ctor_set_uint8(v___x_4026_, sizeof(void*)*3 + 2, v_suppressElabErrors_4021_);
lean_ctor_set_uint8(v___x_4026_, sizeof(void*)*3 + 3, v_checkDeprecated_4022_);
lean_ctor_set_uint8(v___x_4026_, sizeof(void*)*3 + 4, v_isRecordingDeps_4023_);
lean_inc(v_a_4016_);
v___x_4027_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4016_, v___x_4024_, v_a_3832_, v_a_3833_, v___x_4026_, v_a_3835_);
lean_dec_ref_known(v___x_4026_, 3);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_dec_ref_known(v___x_4027_, 1);
if (lean_obj_tag(v_mod_x3f_3825_) == 1)
{
lean_object* v_val_4028_; lean_object* v___x_4029_; 
v_val_4028_ = lean_ctor_get(v_mod_x3f_3825_, 0);
lean_inc(v_val_4028_);
lean_dec_ref_known(v_mod_x3f_3825_, 1);
v___x_4029_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_4028_, v_a_3834_, v_a_3835_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4222_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4032_ = v___x_4029_;
v_isShared_4033_ = v_isSharedCheck_4222_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4222_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
switch(lean_obj_tag(v_a_4030_))
{
case 0:
{
lean_object* v_k_4034_; 
lean_del_object(v___x_4032_);
v_k_4034_ = lean_ctor_get(v_a_4030_, 0);
lean_inc(v_k_4034_);
lean_dec_ref_known(v_a_4030_, 1);
if (lean_obj_tag(v_k_4034_) == 9)
{
lean_dec(v_id_3826_);
if (v_only_3828_ == 0)
{
lean_object* v_ref_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v_ref_4035_ = l_Lean_replaceRef(v_p_3824_, v_ref_4019_);
lean_inc(v_currRecDepth_4018_);
lean_inc_ref(v_toCold_4017_);
v___x_4036_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4036_, 0, v_toCold_4017_);
lean_ctor_set(v___x_4036_, 1, v_currRecDepth_4018_);
lean_ctor_set(v___x_4036_, 2, v_ref_4035_);
lean_ctor_set_uint16(v___x_4036_, sizeof(void*)*3, v_optionFlags_4020_);
lean_ctor_set_uint8(v___x_4036_, sizeof(void*)*3 + 2, v_suppressElabErrors_4021_);
lean_ctor_set_uint8(v___x_4036_, sizeof(void*)*3 + 3, v_checkDeprecated_4022_);
lean_ctor_set_uint8(v___x_4036_, sizeof(void*)*3 + 4, v_isRecordingDeps_4023_);
v___x_4037_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_4036_, v_a_3835_);
lean_dec_ref_known(v___x_4036_, 3);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_dec_ref_known(v___x_4037_, 1);
v___y_3891_ = v_a_4016_;
v___y_3892_ = v_k_4034_;
v___y_3893_ = v_a_3830_;
v___y_3894_ = v_a_3831_;
v___y_3895_ = v_a_3832_;
v___y_3896_ = v_a_3833_;
v___y_3897_ = v_a_3834_;
v___y_3898_ = v_a_3835_;
goto v___jp_3890_;
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec(v_a_4016_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4037_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4037_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
else
{
v___y_3891_ = v_a_4016_;
v___y_3892_ = v_k_4034_;
v___y_3893_ = v_a_3830_;
v___y_3894_ = v_a_3831_;
v___y_3895_ = v_a_3832_;
v___y_3896_ = v_a_3833_;
v___y_3897_ = v_a_3834_;
v___y_3898_ = v_a_3835_;
goto v___jp_3890_;
}
}
else
{
uint8_t v___x_4046_; lean_object* v_ref_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4046_ = 0;
v_ref_4047_ = l_Lean_replaceRef(v_p_3824_, v_ref_4019_);
lean_dec(v_p_3824_);
lean_inc(v_currRecDepth_4018_);
lean_inc_ref(v_toCold_4017_);
v___x_4048_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4048_, 0, v_toCold_4017_);
lean_ctor_set(v___x_4048_, 1, v_currRecDepth_4018_);
lean_ctor_set(v___x_4048_, 2, v_ref_4047_);
lean_ctor_set_uint16(v___x_4048_, sizeof(void*)*3, v_optionFlags_4020_);
lean_ctor_set_uint8(v___x_4048_, sizeof(void*)*3 + 2, v_suppressElabErrors_4021_);
lean_ctor_set_uint8(v___x_4048_, sizeof(void*)*3 + 3, v_checkDeprecated_4022_);
lean_ctor_set_uint8(v___x_4048_, sizeof(void*)*3 + 4, v_isRecordingDeps_4023_);
v___x_4049_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3823_, v_id_3826_, v_a_4016_, v_k_4034_, v_minIndexable_3827_, v___x_4046_, v___x_4024_, v_a_3832_, v_a_3833_, v___x_4048_, v_a_3835_);
lean_dec_ref_known(v___x_4048_, 3);
return v___x_4049_;
}
}
case 1:
{
lean_del_object(v___x_4032_);
lean_dec(v_id_3826_);
if (v_incremental_3829_ == 0)
{
uint8_t v_eager_4050_; 
v_eager_4050_ = lean_ctor_get_uint8(v_a_4030_, 0);
lean_dec_ref_known(v_a_4030_, 0);
v___y_3848_ = v_a_4016_;
v___y_3849_ = v_eager_4050_;
v___y_3850_ = v_a_3832_;
v___y_3851_ = v_a_3833_;
v___y_3852_ = v_a_3834_;
v___y_3853_ = v_a_3835_;
goto v___jp_3847_;
}
else
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec_ref_known(v_a_4030_, 0);
lean_dec(v_a_4016_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v___x_4051_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_4052_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4051_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
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
case 2:
{
uint8_t v___x_4061_; lean_object* v___x_4062_; 
lean_del_object(v___x_4032_);
v___x_4061_ = 0;
lean_inc(v_a_4016_);
v___x_4062_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_4016_, v___x_4061_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref_known(v___x_4062_, 1);
if (lean_obj_tag(v_a_4063_) == 1)
{
lean_dec(v_a_4016_);
if (v_incremental_3829_ == 0)
{
lean_object* v_val_4064_; 
v_val_4064_ = lean_ctor_get(v_a_4063_, 0);
lean_inc(v_val_4064_);
lean_dec_ref_known(v_a_4063_, 1);
v___y_3838_ = v_val_4064_;
v___y_3839_ = v_a_3830_;
v___y_3840_ = v_a_3831_;
v___y_3841_ = v_a_3832_;
v___y_3842_ = v_a_3833_;
v___y_3843_ = v_a_3834_;
v___y_3844_ = v_a_3835_;
goto v___jp_3837_;
}
else
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
lean_dec_ref_known(v_a_4063_, 1);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v___x_4065_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_4066_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4065_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4066_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4066_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
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
else
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v_a_4063_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v___x_4075_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_4076_ = l_Lean_MessageData_ofConstName(v_a_4016_, v___x_4061_);
v___x_4077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4075_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
v___x_4078_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_4079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4077_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
v___x_4080_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4079_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
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
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec(v_a_4016_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_a_4089_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4062_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4062_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
case 3:
{
lean_del_object(v___x_4032_);
v___y_3941_ = v_a_4016_;
v___y_3942_ = v___x_4024_;
v___y_3943_ = v_a_3830_;
v___y_3944_ = v_a_3831_;
v___y_3945_ = v_a_3832_;
v___y_3946_ = v_a_3833_;
v___y_3947_ = v_a_3834_;
v___y_3948_ = v_a_3835_;
goto v___jp_3940_;
}
case 4:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_del_object(v___x_4032_);
lean_dec(v_a_4016_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v___x_4097_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_4098_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4097_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4098_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4098_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
case 5:
{
lean_object* v_prio_4107_; lean_object* v___x_4108_; 
lean_del_object(v___x_4032_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
v_prio_4107_ = lean_ctor_get(v_a_4030_, 0);
lean_inc(v_prio_4107_);
lean_dec_ref_known(v_a_4030_, 1);
v___x_4108_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3827_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4133_; 
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4133_ == 0)
{
lean_object* v_unused_4134_; 
v_unused_4134_ = lean_ctor_get(v___x_4108_, 0);
lean_dec(v_unused_4134_);
v___x_4110_ = v___x_4108_;
v_isShared_4111_ = v_isSharedCheck_4133_;
goto v_resetjp_4109_;
}
else
{
lean_dec(v___x_4108_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4133_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v_config_4112_; lean_object* v_identity_4113_; lean_object* v_extensions_4114_; lean_object* v_extra_4115_; lean_object* v_extraInj_4116_; lean_object* v_extraFacts_4117_; lean_object* v_symPrios_4118_; lean_object* v_norm_4119_; lean_object* v_normProcs_4120_; lean_object* v_anchorRefs_x3f_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4132_; 
v_config_4112_ = lean_ctor_get(v_params_3823_, 0);
v_identity_4113_ = lean_ctor_get(v_params_3823_, 1);
v_extensions_4114_ = lean_ctor_get(v_params_3823_, 2);
v_extra_4115_ = lean_ctor_get(v_params_3823_, 3);
v_extraInj_4116_ = lean_ctor_get(v_params_3823_, 4);
v_extraFacts_4117_ = lean_ctor_get(v_params_3823_, 5);
v_symPrios_4118_ = lean_ctor_get(v_params_3823_, 6);
v_norm_4119_ = lean_ctor_get(v_params_3823_, 7);
v_normProcs_4120_ = lean_ctor_get(v_params_3823_, 8);
v_anchorRefs_x3f_4121_ = lean_ctor_get(v_params_3823_, 9);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_params_3823_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4123_ = v_params_3823_;
v_isShared_4124_ = v_isSharedCheck_4132_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_anchorRefs_x3f_4121_);
lean_inc(v_normProcs_4120_);
lean_inc(v_norm_4119_);
lean_inc(v_symPrios_4118_);
lean_inc(v_extraFacts_4117_);
lean_inc(v_extraInj_4116_);
lean_inc(v_extra_4115_);
lean_inc(v_extensions_4114_);
lean_inc(v_identity_4113_);
lean_inc(v_config_4112_);
lean_dec(v_params_3823_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4132_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4125_; lean_object* v___x_4127_; 
v___x_4125_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_4118_, v_a_4016_, v_prio_4107_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 6, v___x_4125_);
v___x_4127_ = v___x_4123_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_config_4112_);
lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_identity_4113_);
lean_ctor_set(v_reuseFailAlloc_4131_, 2, v_extensions_4114_);
lean_ctor_set(v_reuseFailAlloc_4131_, 3, v_extra_4115_);
lean_ctor_set(v_reuseFailAlloc_4131_, 4, v_extraInj_4116_);
lean_ctor_set(v_reuseFailAlloc_4131_, 5, v_extraFacts_4117_);
lean_ctor_set(v_reuseFailAlloc_4131_, 6, v___x_4125_);
lean_ctor_set(v_reuseFailAlloc_4131_, 7, v_norm_4119_);
lean_ctor_set(v_reuseFailAlloc_4131_, 8, v_normProcs_4120_);
lean_ctor_set(v_reuseFailAlloc_4131_, 9, v_anchorRefs_x3f_4121_);
v___x_4127_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
lean_object* v___x_4129_; 
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 0, v___x_4127_);
v___x_4129_ = v___x_4110_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v___x_4127_);
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
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec(v_prio_4107_);
lean_dec(v_a_4016_);
lean_dec_ref(v_params_3823_);
v_a_4135_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4108_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4108_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
case 6:
{
lean_object* v___x_4143_; 
lean_del_object(v___x_4032_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
v___x_4143_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_4016_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4169_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4146_ = v___x_4143_;
v_isShared_4147_ = v_isSharedCheck_4169_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4143_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4169_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v_config_4148_; lean_object* v_identity_4149_; lean_object* v_extensions_4150_; lean_object* v_extra_4151_; lean_object* v_extraInj_4152_; lean_object* v_extraFacts_4153_; lean_object* v_symPrios_4154_; lean_object* v_norm_4155_; lean_object* v_normProcs_4156_; lean_object* v_anchorRefs_x3f_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4168_; 
v_config_4148_ = lean_ctor_get(v_params_3823_, 0);
v_identity_4149_ = lean_ctor_get(v_params_3823_, 1);
v_extensions_4150_ = lean_ctor_get(v_params_3823_, 2);
v_extra_4151_ = lean_ctor_get(v_params_3823_, 3);
v_extraInj_4152_ = lean_ctor_get(v_params_3823_, 4);
v_extraFacts_4153_ = lean_ctor_get(v_params_3823_, 5);
v_symPrios_4154_ = lean_ctor_get(v_params_3823_, 6);
v_norm_4155_ = lean_ctor_get(v_params_3823_, 7);
v_normProcs_4156_ = lean_ctor_get(v_params_3823_, 8);
v_anchorRefs_x3f_4157_ = lean_ctor_get(v_params_3823_, 9);
v_isSharedCheck_4168_ = !lean_is_exclusive(v_params_3823_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4159_ = v_params_3823_;
v_isShared_4160_ = v_isSharedCheck_4168_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_anchorRefs_x3f_4157_);
lean_inc(v_normProcs_4156_);
lean_inc(v_norm_4155_);
lean_inc(v_symPrios_4154_);
lean_inc(v_extraFacts_4153_);
lean_inc(v_extraInj_4152_);
lean_inc(v_extra_4151_);
lean_inc(v_extensions_4150_);
lean_inc(v_identity_4149_);
lean_inc(v_config_4148_);
lean_dec(v_params_3823_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4168_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4161_; lean_object* v___x_4163_; 
v___x_4161_ = l_Lean_PersistentArray_push___redArg(v_extraInj_4152_, v_a_4144_);
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 4, v___x_4161_);
v___x_4163_ = v___x_4159_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_config_4148_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v_identity_4149_);
lean_ctor_set(v_reuseFailAlloc_4167_, 2, v_extensions_4150_);
lean_ctor_set(v_reuseFailAlloc_4167_, 3, v_extra_4151_);
lean_ctor_set(v_reuseFailAlloc_4167_, 4, v___x_4161_);
lean_ctor_set(v_reuseFailAlloc_4167_, 5, v_extraFacts_4153_);
lean_ctor_set(v_reuseFailAlloc_4167_, 6, v_symPrios_4154_);
lean_ctor_set(v_reuseFailAlloc_4167_, 7, v_norm_4155_);
lean_ctor_set(v_reuseFailAlloc_4167_, 8, v_normProcs_4156_);
lean_ctor_set(v_reuseFailAlloc_4167_, 9, v_anchorRefs_x3f_4157_);
v___x_4163_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
lean_object* v___x_4165_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v___x_4163_);
v___x_4165_ = v___x_4146_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4163_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_dec_ref(v_params_3823_);
v_a_4170_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_4143_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4143_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
case 7:
{
lean_object* v___x_4178_; lean_object* v___x_4180_; 
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
v___x_4178_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3823_, v_a_4016_);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 0, v___x_4178_);
v___x_4180_ = v___x_4032_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4178_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
case 8:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
lean_dec_ref_known(v_a_4030_, 0);
lean_del_object(v___x_4032_);
lean_dec(v_a_4016_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v___x_4182_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_4183_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4182_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
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
case 9:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_del_object(v___x_4032_);
lean_dec(v_a_4016_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v___x_4192_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_4193_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4192_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
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
case 10:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
lean_dec_ref_known(v_a_4030_, 0);
lean_del_object(v___x_4032_);
lean_dec(v_a_4016_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v___x_4202_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_4203_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4202_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
default: 
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_del_object(v___x_4032_);
lean_dec(v_a_4016_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v___x_4212_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
v___x_4213_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4212_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4213_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4213_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec(v_a_4016_);
lean_dec(v_id_3826_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_a_4223_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4029_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4029_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_3825_);
v___y_3941_ = v_a_4016_;
v___y_3942_ = v___x_4024_;
v___y_3943_ = v_a_3830_;
v___y_3944_ = v_a_3831_;
v___y_3945_ = v_a_3832_;
v___y_3946_ = v_a_3833_;
v___y_3947_ = v_a_3834_;
v___y_3948_ = v_a_3835_;
goto v___jp_3940_;
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_dec(v_a_4016_);
lean_dec(v_id_3826_);
lean_dec(v_mod_x3f_3825_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_a_4231_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___x_4027_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4027_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
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
v___jp_4239_:
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4250_; 
v_a_4241_ = lean_ctor_get(v___y_4240_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___y_4240_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4243_ = v___y_4240_;
v_isShared_4244_ = v_isSharedCheck_4250_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___y_4240_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4250_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
if (lean_obj_tag(v_a_4241_) == 0)
{
lean_object* v_a_4245_; lean_object* v___x_4247_; 
lean_dec(v_id_3826_);
lean_dec(v_mod_x3f_3825_);
lean_dec(v_p_3824_);
lean_dec_ref(v_params_3823_);
v_a_4245_ = lean_ctor_get(v_a_4241_, 0);
lean_inc(v_a_4245_);
lean_dec_ref_known(v_a_4241_, 1);
if (v_isShared_4244_ == 0)
{
lean_ctor_set(v___x_4243_, 0, v_a_4245_);
v___x_4247_ = v___x_4243_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4245_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
else
{
lean_object* v_a_4249_; 
lean_del_object(v___x_4243_);
v_a_4249_ = lean_ctor_get(v_a_4241_, 0);
lean_inc(v_a_4249_);
lean_dec_ref_known(v_a_4241_, 1);
v_a_4016_ = v_a_4249_;
goto v___jp_4015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4331_, lean_object* v_p_4332_, lean_object* v_mod_x3f_4333_, lean_object* v_id_4334_, lean_object* v_minIndexable_4335_, lean_object* v_only_4336_, lean_object* v_incremental_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_){
_start:
{
uint8_t v_minIndexable_boxed_4345_; uint8_t v_only_boxed_4346_; uint8_t v_incremental_boxed_4347_; lean_object* v_res_4348_; 
v_minIndexable_boxed_4345_ = lean_unbox(v_minIndexable_4335_);
v_only_boxed_4346_ = lean_unbox(v_only_4336_);
v_incremental_boxed_4347_ = lean_unbox(v_incremental_4337_);
v_res_4348_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4331_, v_p_4332_, v_mod_x3f_4333_, v_id_4334_, v_minIndexable_boxed_4345_, v_only_boxed_4346_, v_incremental_boxed_4347_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_);
lean_dec(v_a_4343_);
lean_dec_ref(v_a_4342_);
lean_dec(v_a_4341_);
lean_dec_ref(v_a_4340_);
lean_dec(v_a_4339_);
lean_dec_ref(v_a_4338_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4349_, lean_object* v_id_4350_, uint8_t v_minIndexable_4351_, lean_object* v_as_4352_, lean_object* v_as_x27_4353_, lean_object* v_b_4354_, lean_object* v_a_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v___x_4363_; 
v___x_4363_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4349_, v_id_4350_, v_minIndexable_4351_, v_as_x27_4353_, v_b_4354_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4364_, lean_object* v_id_4365_, lean_object* v_minIndexable_4366_, lean_object* v_as_4367_, lean_object* v_as_x27_4368_, lean_object* v_b_4369_, lean_object* v_a_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
uint8_t v_minIndexable_boxed_4378_; lean_object* v_res_4379_; 
v_minIndexable_boxed_4378_ = lean_unbox(v_minIndexable_4366_);
v_res_4379_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4364_, v_id_4365_, v_minIndexable_boxed_4378_, v_as_4367_, v_as_x27_4368_, v_b_4369_, v_a_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v_as_x27_4368_);
lean_dec(v_as_4367_);
lean_dec(v_p_4364_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4380_, lean_object* v_as_x27_4381_, lean_object* v_b_4382_, lean_object* v_a_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4381_, v_b_4382_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4392_, lean_object* v_as_x27_4393_, lean_object* v_b_4394_, lean_object* v_a_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4392_, v_as_x27_4393_, v_b_4394_, v_a_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec(v_as_x27_4393_);
lean_dec(v_as_4392_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4404_, lean_object* v_ref_4405_, lean_object* v_msg_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v___x_4414_; 
v___x_4414_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4405_, v_msg_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4415_, lean_object* v_ref_4416_, lean_object* v_msg_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4415_, v_ref_4416_, v_msg_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec(v_ref_4416_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4426_, lean_object* v_id_4427_, uint8_t v_minIndexable_4428_, lean_object* v_as_4429_, lean_object* v_as_x27_4430_, lean_object* v_b_4431_, lean_object* v_a_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v___x_4440_; 
v___x_4440_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4426_, v_id_4427_, v_minIndexable_4428_, v_as_x27_4430_, v_b_4431_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4441_, lean_object* v_id_4442_, lean_object* v_minIndexable_4443_, lean_object* v_as_4444_, lean_object* v_as_x27_4445_, lean_object* v_b_4446_, lean_object* v_a_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
uint8_t v_minIndexable_boxed_4455_; lean_object* v_res_4456_; 
v_minIndexable_boxed_4455_ = lean_unbox(v_minIndexable_4443_);
v_res_4456_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4441_, v_id_4442_, v_minIndexable_boxed_4455_, v_as_4444_, v_as_x27_4445_, v_b_4446_, v_a_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v_as_x27_4445_);
lean_dec(v_as_4444_);
lean_dec(v_p_4441_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4457_, lean_object* v_t_4458_, lean_object* v_k_4459_){
_start:
{
lean_object* v___x_4460_; 
v___x_4460_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4458_, v_k_4459_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4461_, lean_object* v_t_4462_, lean_object* v_k_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4461_, v_t_4462_, v_k_4463_);
lean_dec(v_k_4463_);
lean_dec(v_t_4462_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4465_, lean_object* v_auxDeclToFullName_4466_, lean_object* v___x_4467_, lean_object* v_givenNameView_4468_, lean_object* v_as_4469_, lean_object* v_i_4470_, lean_object* v_a_4471_){
_start:
{
lean_object* v___x_4472_; 
v___x_4472_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4465_, v_auxDeclToFullName_4466_, v___x_4467_, v_givenNameView_4468_, v_as_4469_, v_i_4470_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4473_, lean_object* v_auxDeclToFullName_4474_, lean_object* v___x_4475_, lean_object* v_givenNameView_4476_, lean_object* v_as_4477_, lean_object* v_i_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4473_, v_auxDeclToFullName_4474_, v___x_4475_, v_givenNameView_4476_, v_as_4477_, v_i_4478_, v_a_4479_);
lean_dec_ref(v_as_4477_);
lean_dec(v_auxDeclToFullName_4474_);
lean_dec(v_givenName_4473_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4481_, lean_object* v_givenName_4482_, lean_object* v_as_4483_, lean_object* v_i_4484_, lean_object* v_a_4485_){
_start:
{
lean_object* v___x_4486_; 
v___x_4486_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4481_, v_givenName_4482_, v_as_4483_, v_i_4484_);
return v___x_4486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4487_, lean_object* v_givenName_4488_, lean_object* v_as_4489_, lean_object* v_i_4490_, lean_object* v_a_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4487_, v_givenName_4488_, v_as_4489_, v_i_4490_, v_a_4491_);
lean_dec_ref(v_as_4489_);
lean_dec(v_givenName_4488_);
lean_dec(v_localDecl_x3f_4487_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4493_, lean_object* v_auxDeclToFullName_4494_, lean_object* v___x_4495_, lean_object* v_givenNameView_4496_, lean_object* v_as_4497_, lean_object* v_i_4498_, lean_object* v_a_4499_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4493_, v_auxDeclToFullName_4494_, v___x_4495_, v_givenNameView_4496_, v_as_4497_, v_i_4498_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4501_, lean_object* v_auxDeclToFullName_4502_, lean_object* v___x_4503_, lean_object* v_givenNameView_4504_, lean_object* v_as_4505_, lean_object* v_i_4506_, lean_object* v_a_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4501_, v_auxDeclToFullName_4502_, v___x_4503_, v_givenNameView_4504_, v_as_4505_, v_i_4506_, v_a_4507_);
lean_dec_ref(v_as_4505_);
lean_dec(v_auxDeclToFullName_4502_);
lean_dec(v_givenName_4501_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4509_, lean_object* v_givenName_4510_, lean_object* v_as_4511_, lean_object* v_i_4512_, lean_object* v_a_4513_){
_start:
{
lean_object* v___x_4514_; 
v___x_4514_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4509_, v_givenName_4510_, v_as_4511_, v_i_4512_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4515_, lean_object* v_givenName_4516_, lean_object* v_as_4517_, lean_object* v_i_4518_, lean_object* v_a_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4515_, v_givenName_4516_, v_as_4517_, v_i_4518_, v_a_4519_);
lean_dec_ref(v_as_4517_);
lean_dec(v_givenName_4516_);
lean_dec(v_localDecl_x3f_4515_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v___x_4529_; 
v___x_4529_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4521_, v___y_4526_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec_ref(v_opt_4530_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4539_, lean_object* v_msgData_4540_, uint8_t v_severity_4541_, uint8_t v_isSilent_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
lean_object* v___x_4550_; 
v___x_4550_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4539_, v_msgData_4540_, v_severity_4541_, v_isSilent_4542_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4551_, lean_object* v_msgData_4552_, lean_object* v_severity_4553_, lean_object* v_isSilent_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
uint8_t v_severity_boxed_4562_; uint8_t v_isSilent_boxed_4563_; lean_object* v_res_4564_; 
v_severity_boxed_4562_ = lean_unbox(v_severity_4553_);
v_isSilent_boxed_4563_ = lean_unbox(v_isSilent_4554_);
v_res_4564_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4551_, v_msgData_4552_, v_severity_boxed_4562_, v_isSilent_boxed_4563_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v_ref_4551_);
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4565_, uint8_t v___x_4566_, lean_object* v_b_4567_, lean_object* v_____r_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4576_ = lean_box(0);
lean_inc(v___x_4565_);
v___x_4577_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4565_, v___x_4576_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4577_) == 0)
{
lean_object* v_a_4578_; lean_object* v_toCold_4579_; lean_object* v_currRecDepth_4580_; lean_object* v_ref_4581_; uint16_t v_optionFlags_4582_; uint8_t v_suppressElabErrors_4583_; uint8_t v_checkDeprecated_4584_; uint8_t v_isRecordingDeps_4585_; lean_object* v_ref_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
v_a_4578_ = lean_ctor_get(v___x_4577_, 0);
lean_inc_n(v_a_4578_, 2);
lean_dec_ref_known(v___x_4577_, 1);
v_toCold_4579_ = lean_ctor_get(v___y_4573_, 0);
v_currRecDepth_4580_ = lean_ctor_get(v___y_4573_, 1);
v_ref_4581_ = lean_ctor_get(v___y_4573_, 2);
v_optionFlags_4582_ = lean_ctor_get_uint16(v___y_4573_, sizeof(void*)*3);
v_suppressElabErrors_4583_ = lean_ctor_get_uint8(v___y_4573_, sizeof(void*)*3 + 2);
v_checkDeprecated_4584_ = lean_ctor_get_uint8(v___y_4573_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4585_ = lean_ctor_get_uint8(v___y_4573_, sizeof(void*)*3 + 4);
v_ref_4586_ = l_Lean_replaceRef(v___x_4565_, v_ref_4581_);
lean_dec(v___x_4565_);
lean_inc(v_currRecDepth_4580_);
lean_inc_ref(v_toCold_4579_);
v___x_4587_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4587_, 0, v_toCold_4579_);
lean_ctor_set(v___x_4587_, 1, v_currRecDepth_4580_);
lean_ctor_set(v___x_4587_, 2, v_ref_4586_);
lean_ctor_set_uint16(v___x_4587_, sizeof(void*)*3, v_optionFlags_4582_);
lean_ctor_set_uint8(v___x_4587_, sizeof(void*)*3 + 2, v_suppressElabErrors_4583_);
lean_ctor_set_uint8(v___x_4587_, sizeof(void*)*3 + 3, v_checkDeprecated_4584_);
lean_ctor_set_uint8(v___x_4587_, sizeof(void*)*3 + 4, v_isRecordingDeps_4585_);
v___x_4588_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4578_, v___x_4566_, v___y_4571_, v___y_4572_, v___x_4587_, v___y_4574_);
lean_dec_ref_known(v___x_4587_, 3);
if (lean_obj_tag(v___x_4588_) == 0)
{
uint8_t v___x_4589_; lean_object* v___x_4590_; 
lean_dec_ref_known(v___x_4588_, 1);
v___x_4589_ = 0;
lean_inc(v_a_4578_);
v___x_4590_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4578_, v___x_4589_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4650_; 
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v___x_4590_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4593_ = v___x_4590_;
v_isShared_4594_ = v_isSharedCheck_4650_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_dec(v___x_4590_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4650_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
if (lean_obj_tag(v_a_4591_) == 1)
{
lean_object* v_val_4595_; lean_object* v___x_4596_; 
lean_del_object(v___x_4593_);
lean_dec(v_a_4578_);
v_val_4595_ = lean_ctor_get(v_a_4591_, 0);
lean_inc_n(v_val_4595_, 2);
lean_dec_ref_known(v_a_4591_, 1);
v___x_4596_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4595_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v___x_4597_; 
lean_dec_ref_known(v___x_4596_, 1);
v___x_4597_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4567_, v_val_4595_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4607_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4600_ = v___x_4597_;
v_isShared_4601_ = v_isSharedCheck_4607_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4597_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4607_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4605_; 
v___x_4602_ = lean_box(0);
v___x_4603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
lean_ctor_set(v___x_4603_, 1, v_a_4598_);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v___x_4603_);
v___x_4605_ = v___x_4600_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4603_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
v_a_4608_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4597_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4597_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
else
{
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4623_; 
lean_dec(v_val_4595_);
lean_dec_ref(v_b_4567_);
v_a_4616_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4618_ = v___x_4596_;
v_isShared_4619_ = v_isSharedCheck_4623_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4596_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4623_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4621_; 
if (v_isShared_4619_ == 0)
{
v___x_4621_ = v___x_4618_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_a_4616_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
}
else
{
uint8_t v___x_4624_; 
lean_dec(v_a_4591_);
lean_inc(v_a_4578_);
v___x_4624_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4567_, v_a_4578_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4625_; 
lean_del_object(v___x_4593_);
v___x_4625_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4567_, v_a_4578_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4625_) == 0)
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4635_; 
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4628_ = v___x_4625_;
v_isShared_4629_ = v_isSharedCheck_4635_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4625_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4635_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4633_; 
v___x_4630_ = lean_box(0);
v___x_4631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4630_);
lean_ctor_set(v___x_4631_, 1, v_a_4626_);
if (v_isShared_4629_ == 0)
{
lean_ctor_set(v___x_4628_, 0, v___x_4631_);
v___x_4633_ = v___x_4628_;
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
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
v_a_4636_ = lean_ctor_get(v___x_4625_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4625_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4625_);
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
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4648_; 
v___x_4644_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4567_, v_a_4578_);
v___x_4645_ = lean_box(0);
v___x_4646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4645_);
lean_ctor_set(v___x_4646_, 1, v___x_4644_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 0, v___x_4646_);
v___x_4648_ = v___x_4593_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v___x_4646_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
}
}
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4658_; 
lean_dec(v_a_4578_);
lean_dec_ref(v_b_4567_);
v_a_4651_ = lean_ctor_get(v___x_4590_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4590_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4653_ = v___x_4590_;
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4590_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4656_; 
if (v_isShared_4654_ == 0)
{
v___x_4656_ = v___x_4653_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4651_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
}
else
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
lean_dec(v_a_4578_);
lean_dec_ref(v_b_4567_);
v_a_4659_ = lean_ctor_get(v___x_4588_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4588_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4661_ = v___x_4588_;
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4588_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4664_; 
if (v_isShared_4662_ == 0)
{
v___x_4664_ = v___x_4661_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_a_4659_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
else
{
lean_object* v_a_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4674_; 
lean_dec_ref(v_b_4567_);
lean_dec(v___x_4565_);
v_a_4667_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4669_ = v___x_4577_;
v_isShared_4670_ = v_isSharedCheck_4674_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_a_4667_);
lean_dec(v___x_4577_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4674_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v___x_4672_; 
if (v_isShared_4670_ == 0)
{
v___x_4672_ = v___x_4669_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_a_4667_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4675_, lean_object* v___x_4676_, lean_object* v_b_4677_, lean_object* v_____r_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
uint8_t v___x_18543__boxed_4686_; lean_object* v_res_4687_; 
v___x_18543__boxed_4686_ = lean_unbox(v___x_4676_);
v_res_4687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4675_, v___x_18543__boxed_4686_, v_b_4677_, v_____r_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4691_, lean_object* v_b_4692_, lean_object* v_a_4693_, uint8_t v___x_4694_, uint8_t v_only_4695_, uint8_t v_incremental_4696_, lean_object* v_x_4697_, lean_object* v_mod_x3f_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___y_4709_; lean_object* v___y_4710_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4713_; lean_object* v___y_4714_; lean_object* v___x_4734_; uint8_t v___x_4735_; 
v___x_4706_ = lean_unsigned_to_nat(1u);
v___x_4707_ = l_Lean_Syntax_getArg(v___x_4691_, v___x_4706_);
v___x_4734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4707_);
v___x_4735_ = l_Lean_Syntax_isOfKind(v___x_4707_, v___x_4734_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; 
v___x_4736_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4692_, v_a_4693_, v_mod_x3f_4698_, v___x_4707_, v___x_4694_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4746_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4739_ = v___x_4736_;
v_isShared_4740_ = v_isSharedCheck_4746_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4736_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4746_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4744_; 
v___x_4741_ = lean_box(0);
v___x_4742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4741_);
lean_ctor_set(v___x_4742_, 1, v_a_4737_);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v___x_4742_);
v___x_4744_ = v___x_4739_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4742_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
}
else
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4754_; 
v_a_4747_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4749_ = v___x_4736_;
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___x_4736_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___x_4752_; 
if (v_isShared_4750_ == 0)
{
v___x_4752_ = v___x_4749_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4747_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
}
else
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4755_ = l_Lean_TSyntax_getId(v___x_4707_);
v___x_4756_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4755_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
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
v___x_4763_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4692_, v_a_4693_, v_mod_x3f_4698_, v___x_4707_, v___x_4694_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
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
v___y_4709_ = v___y_4699_;
v___y_4710_ = v___y_4700_;
v___y_4711_ = v___y_4701_;
v___y_4712_ = v___y_4702_;
v___y_4713_ = v___y_4703_;
v___y_4714_ = v___y_4704_;
goto v___jp_4708_;
}
}
}
else
{
lean_dec(v_a_4757_);
v___y_4709_ = v___y_4699_;
v___y_4710_ = v___y_4700_;
v___y_4711_ = v___y_4701_;
v___y_4712_ = v___y_4702_;
v___y_4713_ = v___y_4703_;
v___y_4714_ = v___y_4704_;
goto v___jp_4708_;
}
}
else
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4793_; 
lean_dec(v___x_4707_);
lean_dec(v_mod_x3f_4698_);
lean_dec(v_a_4693_);
lean_dec_ref(v_b_4692_);
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
v___jp_4708_:
{
lean_object* v___x_4715_; 
v___x_4715_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4692_, v_a_4693_, v_mod_x3f_4698_, v___x_4707_, v___x_4694_, v_only_4695_, v_incremental_4696_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_object* v_a_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4725_; 
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4718_ = v___x_4715_;
v_isShared_4719_ = v_isSharedCheck_4725_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_a_4716_);
lean_dec(v___x_4715_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4725_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4723_; 
v___x_4720_ = lean_box(0);
v___x_4721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
lean_ctor_set(v___x_4721_, 1, v_a_4716_);
if (v_isShared_4719_ == 0)
{
lean_ctor_set(v___x_4718_, 0, v___x_4721_);
v___x_4723_ = v___x_4718_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v___x_4721_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
else
{
lean_object* v_a_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4733_; 
v_a_4726_ = lean_ctor_get(v___x_4715_, 0);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4728_ = v___x_4715_;
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_a_4726_);
lean_dec(v___x_4715_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4731_; 
if (v_isShared_4729_ == 0)
{
v___x_4731_ = v___x_4728_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4726_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4794_, lean_object* v_b_4795_, lean_object* v_a_4796_, lean_object* v___x_4797_, lean_object* v_only_4798_, lean_object* v_incremental_4799_, lean_object* v_x_4800_, lean_object* v_mod_x3f_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_){
_start:
{
uint8_t v___x_18763__boxed_4809_; uint8_t v_only_boxed_4810_; uint8_t v_incremental_boxed_4811_; lean_object* v_res_4812_; 
v___x_18763__boxed_4809_ = lean_unbox(v___x_4797_);
v_only_boxed_4810_ = lean_unbox(v_only_4798_);
v_incremental_boxed_4811_ = lean_unbox(v_incremental_4799_);
v_res_4812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4794_, v_b_4795_, v_a_4796_, v___x_18763__boxed_4809_, v_only_boxed_4810_, v_incremental_boxed_4811_, v_x_4800_, v_mod_x3f_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_);
lean_dec(v___y_4807_);
lean_dec_ref(v___y_4806_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
lean_dec(v___y_4803_);
lean_dec_ref(v___y_4802_);
lean_dec(v___x_4794_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4813_, lean_object* v___x_4814_, lean_object* v_____r_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v___x_4823_; 
v___x_4823_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4813_, v___x_4814_, v___y_4820_, v___y_4821_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4833_; 
v_a_4824_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4826_ = v___x_4823_;
v_isShared_4827_ = v_isSharedCheck_4833_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4823_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4833_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4831_; 
v___x_4828_ = lean_box(0);
v___x_4829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
lean_ctor_set(v___x_4829_, 1, v_a_4824_);
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 0, v___x_4829_);
v___x_4831_ = v___x_4826_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v___x_4829_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
else
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4841_; 
v_a_4834_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4836_ = v___x_4823_;
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4823_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4839_; 
if (v_isShared_4837_ == 0)
{
v___x_4839_ = v___x_4836_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4834_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4842_, lean_object* v___x_4843_, lean_object* v_____r_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4842_, v___x_4843_, v_____r_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
lean_dec(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec(v___y_4848_);
lean_dec_ref(v___y_4847_);
lean_dec(v___y_4846_);
lean_dec_ref(v___y_4845_);
lean_dec(v___x_4843_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4853_, lean_object* v_b_4854_, lean_object* v_a_4855_, uint8_t v___x_4856_, uint8_t v_only_4857_, uint8_t v_incremental_4858_, lean_object* v_x_4859_, lean_object* v_mod_x3f_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_){
_start:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___y_4871_; lean_object* v___y_4872_; lean_object* v___y_4873_; lean_object* v___y_4874_; lean_object* v___y_4875_; lean_object* v___y_4876_; lean_object* v___x_4896_; uint8_t v___x_4897_; 
v___x_4868_ = lean_unsigned_to_nat(2u);
v___x_4869_ = l_Lean_Syntax_getArg(v___x_4853_, v___x_4868_);
v___x_4896_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4869_);
v___x_4897_ = l_Lean_Syntax_isOfKind(v___x_4869_, v___x_4896_);
if (v___x_4897_ == 0)
{
lean_object* v___x_4898_; 
v___x_4898_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4854_, v_a_4855_, v_mod_x3f_4860_, v___x_4869_, v___x_4856_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4908_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4901_ = v___x_4898_;
v_isShared_4902_ = v_isSharedCheck_4908_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4898_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4908_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4906_; 
v___x_4903_ = lean_box(0);
v___x_4904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4903_);
lean_ctor_set(v___x_4904_, 1, v_a_4899_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v___x_4904_);
v___x_4906_ = v___x_4901_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v___x_4904_);
v___x_4906_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
return v___x_4906_;
}
}
}
else
{
lean_object* v_a_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4916_; 
v_a_4909_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4911_ = v___x_4898_;
v_isShared_4912_ = v_isSharedCheck_4916_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_a_4909_);
lean_dec(v___x_4898_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4916_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v___x_4914_; 
if (v_isShared_4912_ == 0)
{
v___x_4914_ = v___x_4911_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4909_);
v___x_4914_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
return v___x_4914_;
}
}
}
}
else
{
lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4917_ = l_Lean_TSyntax_getId(v___x_4869_);
v___x_4918_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4917_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_);
if (lean_obj_tag(v___x_4918_) == 0)
{
lean_object* v_a_4919_; 
v_a_4919_ = lean_ctor_get(v___x_4918_, 0);
lean_inc(v_a_4919_);
lean_dec_ref_known(v___x_4918_, 1);
if (lean_obj_tag(v_a_4919_) == 1)
{
lean_object* v_val_4920_; lean_object* v_snd_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4946_; 
v_val_4920_ = lean_ctor_get(v_a_4919_, 0);
lean_inc(v_val_4920_);
lean_dec_ref_known(v_a_4919_, 1);
v_snd_4921_ = lean_ctor_get(v_val_4920_, 1);
v_isSharedCheck_4946_ = !lean_is_exclusive(v_val_4920_);
if (v_isSharedCheck_4946_ == 0)
{
lean_object* v_unused_4947_; 
v_unused_4947_ = lean_ctor_get(v_val_4920_, 0);
lean_dec(v_unused_4947_);
v___x_4923_ = v_val_4920_;
v_isShared_4924_ = v_isSharedCheck_4946_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_snd_4921_);
lean_dec(v_val_4920_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4946_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
if (lean_obj_tag(v_snd_4921_) == 1)
{
lean_object* v___x_4925_; 
lean_dec_ref_known(v_snd_4921_, 2);
v___x_4925_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4854_, v_a_4855_, v_mod_x3f_4860_, v___x_4869_, v___x_4856_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4937_; 
v_a_4926_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4928_ = v___x_4925_;
v_isShared_4929_ = v_isSharedCheck_4937_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4925_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4937_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4930_; lean_object* v___x_4932_; 
v___x_4930_ = lean_box(0);
if (v_isShared_4924_ == 0)
{
lean_ctor_set(v___x_4923_, 1, v_a_4926_);
lean_ctor_set(v___x_4923_, 0, v___x_4930_);
v___x_4932_ = v___x_4923_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4930_);
lean_ctor_set(v_reuseFailAlloc_4936_, 1, v_a_4926_);
v___x_4932_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
lean_object* v___x_4934_; 
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 0, v___x_4932_);
v___x_4934_ = v___x_4928_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4932_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
lean_del_object(v___x_4923_);
v_a_4938_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4925_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4925_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
else
{
lean_del_object(v___x_4923_);
lean_dec(v_snd_4921_);
v___y_4871_ = v___y_4861_;
v___y_4872_ = v___y_4862_;
v___y_4873_ = v___y_4863_;
v___y_4874_ = v___y_4864_;
v___y_4875_ = v___y_4865_;
v___y_4876_ = v___y_4866_;
goto v___jp_4870_;
}
}
}
else
{
lean_dec(v_a_4919_);
v___y_4871_ = v___y_4861_;
v___y_4872_ = v___y_4862_;
v___y_4873_ = v___y_4863_;
v___y_4874_ = v___y_4864_;
v___y_4875_ = v___y_4865_;
v___y_4876_ = v___y_4866_;
goto v___jp_4870_;
}
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
lean_dec(v___x_4869_);
lean_dec(v_mod_x3f_4860_);
lean_dec(v_a_4855_);
lean_dec_ref(v_b_4854_);
v_a_4948_ = lean_ctor_get(v___x_4918_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4918_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4918_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4918_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
v___jp_4870_:
{
lean_object* v___x_4877_; 
v___x_4877_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4854_, v_a_4855_, v_mod_x3f_4860_, v___x_4869_, v___x_4856_, v_only_4857_, v_incremental_4858_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4887_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4880_ = v___x_4877_;
v_isShared_4881_ = v_isSharedCheck_4887_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4877_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4887_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4885_; 
v___x_4882_ = lean_box(0);
v___x_4883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4882_);
lean_ctor_set(v___x_4883_, 1, v_a_4878_);
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 0, v___x_4883_);
v___x_4885_ = v___x_4880_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4883_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
else
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4895_; 
v_a_4888_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4890_ = v___x_4877_;
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4877_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4893_; 
if (v_isShared_4891_ == 0)
{
v___x_4893_ = v___x_4890_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4956_, lean_object* v_b_4957_, lean_object* v_a_4958_, lean_object* v___x_4959_, lean_object* v_only_4960_, lean_object* v_incremental_4961_, lean_object* v_x_4962_, lean_object* v_mod_x3f_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_){
_start:
{
uint8_t v___x_19042__boxed_4971_; uint8_t v_only_boxed_4972_; uint8_t v_incremental_boxed_4973_; lean_object* v_res_4974_; 
v___x_19042__boxed_4971_ = lean_unbox(v___x_4959_);
v_only_boxed_4972_ = lean_unbox(v_only_4960_);
v_incremental_boxed_4973_ = lean_unbox(v_incremental_4961_);
v_res_4974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4956_, v_b_4957_, v_a_4958_, v___x_19042__boxed_4971_, v_only_boxed_4972_, v_incremental_boxed_4973_, v_x_4962_, v_mod_x3f_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
lean_dec(v___y_4969_);
lean_dec_ref(v___y_4968_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___x_4956_);
return v_res_4974_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4983_ = l_Lean_stringToMessageData(v___x_4982_);
return v___x_4983_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15(void){
_start:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14));
v___x_5013_ = l_Lean_stringToMessageData(v___x_5012_);
return v___x_5013_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_5015_; lean_object* v___x_5016_; 
v___x_5015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_5016_ = l_Lean_stringToMessageData(v___x_5015_);
return v___x_5016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_5017_, uint8_t v_only_5018_, uint8_t v_incremental_5019_, lean_object* v_as_5020_, size_t v_sz_5021_, size_t v_i_5022_, lean_object* v_b_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_){
_start:
{
lean_object* v_snd_5032_; lean_object* v_a_5037_; lean_object* v___y_5044_; uint8_t v___x_5048_; 
v___x_5048_ = lean_usize_dec_lt(v_i_5022_, v_sz_5021_);
if (v___x_5048_ == 0)
{
lean_object* v___x_5049_; 
v___x_5049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5049_, 0, v_b_5023_);
return v___x_5049_;
}
else
{
lean_object* v_a_5050_; lean_object* v___x_5051_; uint8_t v___x_5052_; 
v_a_5050_ = lean_array_uget_borrowed(v_as_5020_, v_i_5022_);
v___x_5051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_5050_);
v___x_5052_ = l_Lean_Syntax_isOfKind(v_a_5050_, v___x_5051_);
if (v___x_5052_ == 0)
{
lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5053_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5050_);
v___x_5054_ = l_Lean_MessageData_ofSyntax(v_a_5050_);
v___x_5055_ = l_Lean_indentD(v___x_5054_);
v___x_5056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5053_);
lean_ctor_set(v___x_5056_, 1, v___x_5055_);
v___x_5057_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5056_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_dec_ref_known(v___x_5057_, 1);
v_snd_5032_ = v_b_5023_;
goto v___jp_5031_;
}
else
{
lean_object* v_a_5058_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_a_5058_);
lean_dec_ref_known(v___x_5057_, 1);
v_a_5037_ = v_a_5058_;
goto v___jp_5036_;
}
}
else
{
lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; uint8_t v___x_5062_; 
v___x_5059_ = lean_unsigned_to_nat(0u);
v___x_5060_ = l_Lean_Syntax_getArg(v_a_5050_, v___x_5059_);
v___x_5061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_5060_);
v___x_5062_ = l_Lean_Syntax_isOfKind(v___x_5060_, v___x_5061_);
if (v___x_5062_ == 0)
{
lean_object* v___x_5063_; uint8_t v___x_5064_; 
v___x_5063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_5060_);
v___x_5064_ = l_Lean_Syntax_isOfKind(v___x_5060_, v___x_5063_);
if (v___x_5064_ == 0)
{
lean_object* v___x_5065_; uint8_t v___x_5066_; 
v___x_5065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_5060_);
v___x_5066_ = l_Lean_Syntax_isOfKind(v___x_5060_, v___x_5065_);
if (v___x_5066_ == 0)
{
lean_object* v___x_5067_; uint8_t v___x_5068_; 
v___x_5067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_5060_);
v___x_5068_ = l_Lean_Syntax_isOfKind(v___x_5060_, v___x_5067_);
if (v___x_5068_ == 0)
{
lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
lean_dec(v___x_5060_);
v___x_5069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5050_);
v___x_5070_ = l_Lean_MessageData_ofSyntax(v_a_5050_);
v___x_5071_ = l_Lean_indentD(v___x_5070_);
v___x_5072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5069_);
lean_ctor_set(v___x_5072_, 1, v___x_5071_);
v___x_5073_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5072_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_dec_ref_known(v___x_5073_, 1);
v_snd_5032_ = v_b_5023_;
goto v___jp_5031_;
}
else
{
lean_object* v_a_5074_; 
v_a_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_a_5074_);
lean_dec_ref_known(v___x_5073_, 1);
v_a_5037_ = v_a_5074_;
goto v___jp_5036_;
}
}
else
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; uint8_t v___x_5078_; 
v___x_5075_ = lean_unsigned_to_nat(1u);
v___x_5076_ = l_Lean_Syntax_getArg(v___x_5060_, v___x_5075_);
lean_dec(v___x_5060_);
v___x_5077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13));
lean_inc(v___x_5076_);
v___x_5078_ = l_Lean_Syntax_isOfKind(v___x_5076_, v___x_5077_);
if (v___x_5078_ == 0)
{
lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
lean_dec(v___x_5076_);
v___x_5079_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5050_);
v___x_5080_ = l_Lean_MessageData_ofSyntax(v_a_5050_);
v___x_5081_ = l_Lean_indentD(v___x_5080_);
v___x_5082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5082_, 0, v___x_5079_);
lean_ctor_set(v___x_5082_, 1, v___x_5081_);
v___x_5083_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5082_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
if (lean_obj_tag(v___x_5083_) == 0)
{
lean_dec_ref_known(v___x_5083_, 1);
v_snd_5032_ = v_b_5023_;
goto v___jp_5031_;
}
else
{
lean_object* v_a_5084_; 
v_a_5084_ = lean_ctor_get(v___x_5083_, 0);
lean_inc(v_a_5084_);
lean_dec_ref_known(v___x_5083_, 1);
v_a_5037_ = v_a_5084_;
goto v___jp_5036_;
}
}
else
{
if (v_only_5018_ == 0)
{
lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5085_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15);
v___x_5086_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_5076_, v___x_5085_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_object* v_a_5087_; lean_object* v___x_5088_; 
v_a_5087_ = lean_ctor_get(v___x_5086_, 0);
lean_inc(v_a_5087_);
lean_dec_ref_known(v___x_5086_, 1);
lean_inc_ref(v_b_5023_);
v___x_5088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_5023_, v___x_5076_, v_a_5087_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
lean_dec(v___x_5076_);
v___y_5044_ = v___x_5088_;
goto v___jp_5043_;
}
else
{
lean_object* v_a_5089_; 
lean_dec(v___x_5076_);
v_a_5089_ = lean_ctor_get(v___x_5086_, 0);
lean_inc(v_a_5089_);
lean_dec_ref_known(v___x_5086_, 1);
v_a_5037_ = v_a_5089_;
goto v___jp_5036_;
}
}
else
{
lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___x_5090_ = lean_box(0);
lean_inc_ref(v_b_5023_);
v___x_5091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_5023_, v___x_5076_, v___x_5090_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
lean_dec(v___x_5076_);
v___y_5044_ = v___x_5091_;
goto v___jp_5043_;
}
}
}
}
else
{
lean_object* v___x_5092_; lean_object* v___x_5093_; uint8_t v___x_5094_; 
v___x_5092_ = lean_unsigned_to_nat(1u);
v___x_5093_ = l_Lean_Syntax_getArg(v___x_5060_, v___x_5092_);
v___x_5094_ = l_Lean_Syntax_isNone(v___x_5093_);
if (v___x_5094_ == 0)
{
uint8_t v___x_5095_; 
lean_inc(v___x_5093_);
v___x_5095_ = l_Lean_Syntax_matchesNull(v___x_5093_, v___x_5092_);
if (v___x_5095_ == 0)
{
lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
lean_dec(v___x_5093_);
lean_dec(v___x_5060_);
v___x_5096_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5050_);
v___x_5097_ = l_Lean_MessageData_ofSyntax(v_a_5050_);
v___x_5098_ = l_Lean_indentD(v___x_5097_);
v___x_5099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5096_);
lean_ctor_set(v___x_5099_, 1, v___x_5098_);
v___x_5100_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5099_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_dec_ref_known(v___x_5100_, 1);
v_snd_5032_ = v_b_5023_;
goto v___jp_5031_;
}
else
{
lean_object* v_a_5101_; 
v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
lean_inc(v_a_5101_);
lean_dec_ref_known(v___x_5100_, 1);
v_a_5037_ = v_a_5101_;
goto v___jp_5036_;
}
}
else
{
lean_object* v___x_5102_; lean_object* v___x_5103_; uint8_t v___x_5104_; 
v___x_5102_ = l_Lean_Syntax_getArg(v___x_5093_, v___x_5059_);
lean_dec(v___x_5093_);
v___x_5103_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_5102_);
v___x_5104_ = l_Lean_Syntax_isOfKind(v___x_5102_, v___x_5103_);
if (v___x_5104_ == 0)
{
lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
lean_dec(v___x_5102_);
lean_dec(v___x_5060_);
v___x_5105_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5050_);
v___x_5106_ = l_Lean_MessageData_ofSyntax(v_a_5050_);
v___x_5107_ = l_Lean_indentD(v___x_5106_);
v___x_5108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5108_, 0, v___x_5105_);
lean_ctor_set(v___x_5108_, 1, v___x_5107_);
v___x_5109_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5108_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
if (lean_obj_tag(v___x_5109_) == 0)
{
lean_dec_ref_known(v___x_5109_, 1);
v_snd_5032_ = v_b_5023_;
goto v___jp_5031_;
}
else
{
lean_object* v_a_5110_; 
v_a_5110_ = lean_ctor_get(v___x_5109_, 0);
lean_inc(v_a_5110_);
lean_dec_ref_known(v___x_5109_, 1);
v_a_5037_ = v_a_5110_;
goto v___jp_5036_;
}
}
else
{
lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
v___x_5111_ = lean_box(0);
v___x_5112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5112_, 0, v___x_5102_);
lean_inc(v_a_5050_);
lean_inc_ref(v_b_5023_);
v___x_5113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_5060_, v_b_5023_, v_a_5050_, v___x_5052_, v_only_5018_, v_incremental_5019_, v___x_5111_, v___x_5112_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
lean_dec(v___x_5060_);
v___y_5044_ = v___x_5113_;
goto v___jp_5043_;
}
}
}
else
{
lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; 
lean_dec(v___x_5093_);
v___x_5114_ = lean_box(0);
v___x_5115_ = lean_box(0);
lean_inc(v_a_5050_);
lean_inc_ref(v_b_5023_);
v___x_5116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_5060_, v_b_5023_, v_a_5050_, v___x_5052_, v_only_5018_, v_incremental_5019_, v___x_5114_, v___x_5115_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
lean_dec(v___x_5060_);
v___y_5044_ = v___x_5116_;
goto v___jp_5043_;
}
}
}
else
{
lean_object* v___x_5117_; uint8_t v___x_5118_; 
v___x_5117_ = l_Lean_Syntax_getArg(v___x_5060_, v___x_5059_);
v___x_5118_ = l_Lean_Syntax_isNone(v___x_5117_);
if (v___x_5118_ == 0)
{
lean_object* v___x_5119_; uint8_t v___x_5120_; 
v___x_5119_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_5117_);
v___x_5120_ = l_Lean_Syntax_matchesNull(v___x_5117_, v___x_5119_);
if (v___x_5120_ == 0)
{
lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; 
lean_dec(v___x_5117_);
lean_dec(v___x_5060_);
v___x_5121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5050_);
v___x_5122_ = l_Lean_MessageData_ofSyntax(v_a_5050_);
v___x_5123_ = l_Lean_indentD(v___x_5122_);
v___x_5124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5124_, 0, v___x_5121_);
lean_ctor_set(v___x_5124_, 1, v___x_5123_);
v___x_5125_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5124_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_dec_ref_known(v___x_5125_, 1);
v_snd_5032_ = v_b_5023_;
goto v___jp_5031_;
}
else
{
lean_object* v_a_5126_; 
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
lean_inc(v_a_5126_);
lean_dec_ref_known(v___x_5125_, 1);
v_a_5037_ = v_a_5126_;
goto v___jp_5036_;
}
}
else
{
lean_object* v___x_5127_; lean_object* v___x_5128_; uint8_t v___x_5129_; 
v___x_5127_ = l_Lean_Syntax_getArg(v___x_5117_, v___x_5059_);
lean_dec(v___x_5117_);
v___x_5128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_5127_);
v___x_5129_ = l_Lean_Syntax_isOfKind(v___x_5127_, v___x_5128_);
if (v___x_5129_ == 0)
{
lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; 
lean_dec(v___x_5127_);
lean_dec(v___x_5060_);
v___x_5130_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5050_);
v___x_5131_ = l_Lean_MessageData_ofSyntax(v_a_5050_);
v___x_5132_ = l_Lean_indentD(v___x_5131_);
v___x_5133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5133_, 0, v___x_5130_);
lean_ctor_set(v___x_5133_, 1, v___x_5132_);
v___x_5134_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5133_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_dec_ref_known(v___x_5134_, 1);
v_snd_5032_ = v_b_5023_;
goto v___jp_5031_;
}
else
{
lean_object* v_a_5135_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5134_, 1);
v_a_5037_ = v_a_5135_;
goto v___jp_5036_;
}
}
else
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; 
v___x_5136_ = lean_box(0);
v___x_5137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5137_, 0, v___x_5127_);
lean_inc(v_a_5050_);
lean_inc_ref(v_b_5023_);
v___x_5138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_5060_, v_b_5023_, v_a_5050_, v___x_5062_, v_only_5018_, v_incremental_5019_, v___x_5136_, v___x_5137_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
lean_dec(v___x_5060_);
v___y_5044_ = v___x_5138_;
goto v___jp_5043_;
}
}
}
else
{
lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; 
lean_dec(v___x_5117_);
v___x_5139_ = lean_box(0);
v___x_5140_ = lean_box(0);
lean_inc(v_a_5050_);
lean_inc_ref(v_b_5023_);
v___x_5141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_5060_, v_b_5023_, v_a_5050_, v___x_5062_, v_only_5018_, v_incremental_5019_, v___x_5139_, v___x_5140_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
lean_dec(v___x_5060_);
v___y_5044_ = v___x_5141_;
goto v___jp_5043_;
}
}
}
else
{
lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; uint8_t v___x_5145_; 
v___x_5142_ = lean_unsigned_to_nat(1u);
v___x_5143_ = l_Lean_Syntax_getArg(v___x_5060_, v___x_5142_);
lean_dec(v___x_5060_);
v___x_5144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_5143_);
v___x_5145_ = l_Lean_Syntax_isOfKind(v___x_5143_, v___x_5144_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; 
lean_dec(v___x_5143_);
v___x_5146_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5050_);
v___x_5147_ = l_Lean_MessageData_ofSyntax(v_a_5050_);
v___x_5148_ = l_Lean_indentD(v___x_5147_);
v___x_5149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5149_, 0, v___x_5146_);
lean_ctor_set(v___x_5149_, 1, v___x_5148_);
v___x_5150_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5149_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
if (lean_obj_tag(v___x_5150_) == 0)
{
lean_dec_ref_known(v___x_5150_, 1);
v_snd_5032_ = v_b_5023_;
goto v___jp_5031_;
}
else
{
lean_object* v_a_5151_; 
v_a_5151_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_a_5151_);
lean_dec_ref_known(v___x_5150_, 1);
v_a_5037_ = v_a_5151_;
goto v___jp_5036_;
}
}
else
{
if (v_incremental_5019_ == 0)
{
lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___x_5152_ = lean_box(0);
lean_inc_ref(v_b_5023_);
v___x_5153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_5143_, v___x_5052_, v_b_5023_, v___x_5152_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
v___y_5044_ = v___x_5153_;
goto v___jp_5043_;
}
else
{
lean_object* v___x_5154_; lean_object* v___x_5155_; 
v___x_5154_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_5155_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_5050_, v___x_5154_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
if (lean_obj_tag(v___x_5155_) == 0)
{
lean_object* v_a_5156_; lean_object* v___x_5157_; 
v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
lean_inc(v_a_5156_);
lean_dec_ref_known(v___x_5155_, 1);
lean_inc_ref(v_b_5023_);
v___x_5157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_5143_, v___x_5052_, v_b_5023_, v_a_5156_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
v___y_5044_ = v___x_5157_;
goto v___jp_5043_;
}
else
{
lean_object* v_a_5158_; 
lean_dec(v___x_5143_);
v_a_5158_ = lean_ctor_get(v___x_5155_, 0);
lean_inc(v_a_5158_);
lean_dec_ref_known(v___x_5155_, 1);
v_a_5037_ = v_a_5158_;
goto v___jp_5036_;
}
}
}
}
}
}
v___jp_5031_:
{
size_t v___x_5033_; size_t v___x_5034_; 
v___x_5033_ = ((size_t)1ULL);
v___x_5034_ = lean_usize_add(v_i_5022_, v___x_5033_);
v_i_5022_ = v___x_5034_;
v_b_5023_ = v_snd_5032_;
goto _start;
}
v___jp_5036_:
{
uint8_t v___x_5038_; 
v___x_5038_ = l_Lean_Exception_isInterrupt(v_a_5037_);
if (v___x_5038_ == 0)
{
uint8_t v___x_5039_; 
lean_inc_ref(v_a_5037_);
v___x_5039_ = l_Lean_Exception_isRuntime(v_a_5037_);
if (v___x_5039_ == 0)
{
if (v_lax_5017_ == 0)
{
lean_object* v___x_5040_; 
lean_dec_ref(v_b_5023_);
v___x_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5040_, 0, v_a_5037_);
return v___x_5040_;
}
else
{
lean_dec_ref(v_a_5037_);
v_snd_5032_ = v_b_5023_;
goto v___jp_5031_;
}
}
else
{
lean_object* v___x_5041_; 
lean_dec_ref(v_b_5023_);
v___x_5041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5041_, 0, v_a_5037_);
return v___x_5041_;
}
}
else
{
lean_object* v___x_5042_; 
lean_dec_ref(v_b_5023_);
v___x_5042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5042_, 0, v_a_5037_);
return v___x_5042_;
}
}
v___jp_5043_:
{
if (lean_obj_tag(v___y_5044_) == 0)
{
lean_object* v_a_5045_; lean_object* v_snd_5046_; 
lean_dec_ref(v_b_5023_);
v_a_5045_ = lean_ctor_get(v___y_5044_, 0);
lean_inc(v_a_5045_);
lean_dec_ref_known(v___y_5044_, 1);
v_snd_5046_ = lean_ctor_get(v_a_5045_, 1);
lean_inc(v_snd_5046_);
lean_dec(v_a_5045_);
v_snd_5032_ = v_snd_5046_;
goto v___jp_5031_;
}
else
{
lean_object* v_a_5047_; 
v_a_5047_ = lean_ctor_get(v___y_5044_, 0);
lean_inc(v_a_5047_);
lean_dec_ref_known(v___y_5044_, 1);
v_a_5037_ = v_a_5047_;
goto v___jp_5036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_5159_, lean_object* v_only_5160_, lean_object* v_incremental_5161_, lean_object* v_as_5162_, lean_object* v_sz_5163_, lean_object* v_i_5164_, lean_object* v_b_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_){
_start:
{
uint8_t v_lax_boxed_5173_; uint8_t v_only_boxed_5174_; uint8_t v_incremental_boxed_5175_; size_t v_sz_boxed_5176_; size_t v_i_boxed_5177_; lean_object* v_res_5178_; 
v_lax_boxed_5173_ = lean_unbox(v_lax_5159_);
v_only_boxed_5174_ = lean_unbox(v_only_5160_);
v_incremental_boxed_5175_ = lean_unbox(v_incremental_5161_);
v_sz_boxed_5176_ = lean_unbox_usize(v_sz_5163_);
lean_dec(v_sz_5163_);
v_i_boxed_5177_ = lean_unbox_usize(v_i_5164_);
lean_dec(v_i_5164_);
v_res_5178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_5173_, v_only_boxed_5174_, v_incremental_boxed_5175_, v_as_5162_, v_sz_boxed_5176_, v_i_boxed_5177_, v_b_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
lean_dec_ref(v_as_5162_);
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_5179_, lean_object* v_ps_5180_, uint8_t v_only_5181_, uint8_t v_lax_5182_, uint8_t v_incremental_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_){
_start:
{
size_t v_sz_5191_; size_t v___x_5192_; lean_object* v___x_5193_; 
v_sz_5191_ = lean_array_size(v_ps_5180_);
v___x_5192_ = ((size_t)0ULL);
v___x_5193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_5182_, v_only_5181_, v_incremental_5183_, v_ps_5180_, v_sz_5191_, v___x_5192_, v_params_5179_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_5194_, lean_object* v_ps_5195_, lean_object* v_only_5196_, lean_object* v_lax_5197_, lean_object* v_incremental_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_){
_start:
{
uint8_t v_only_boxed_5206_; uint8_t v_lax_boxed_5207_; uint8_t v_incremental_boxed_5208_; lean_object* v_res_5209_; 
v_only_boxed_5206_ = lean_unbox(v_only_5196_);
v_lax_boxed_5207_ = lean_unbox(v_lax_5197_);
v_incremental_boxed_5208_ = lean_unbox(v_incremental_5198_);
v_res_5209_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5194_, v_ps_5195_, v_only_boxed_5206_, v_lax_boxed_5207_, v_incremental_boxed_5208_, v_a_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_);
lean_dec(v_a_5204_);
lean_dec_ref(v_a_5203_);
lean_dec(v_a_5202_);
lean_dec_ref(v_a_5201_);
lean_dec(v_a_5200_);
lean_dec_ref(v_a_5199_);
lean_dec_ref(v_ps_5195_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_){
_start:
{
lean_object* v_origin_5221_; 
v_origin_5221_ = lean_ctor_get(v_thm_5210_, 5);
if (lean_obj_tag(v_origin_5221_) == 0)
{
lean_object* v_declName_5222_; lean_object* v___x_5223_; 
lean_inc_ref(v_origin_5221_);
lean_dec_ref(v_thm_5210_);
v_declName_5222_ = lean_ctor_get(v_origin_5221_, 0);
lean_inc(v_declName_5222_);
lean_dec_ref_known(v_origin_5221_, 1);
v___x_5223_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_5222_, v_a_5218_, v_a_5219_);
return v___x_5223_;
}
else
{
lean_object* v_proof_5224_; lean_object* v___x_5225_; 
v_proof_5224_ = lean_ctor_get(v_thm_5210_, 1);
lean_inc_ref(v_proof_5224_);
lean_dec_ref(v_thm_5210_);
v___x_5225_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_5224_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_);
return v___x_5225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_5226_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_, v_a_5235_);
lean_dec(v_a_5235_);
lean_dec_ref(v_a_5234_);
lean_dec(v_a_5233_);
lean_dec_ref(v_a_5232_);
lean_dec(v_a_5231_);
lean_dec_ref(v_a_5230_);
lean_dec(v_a_5229_);
lean_dec_ref(v_a_5228_);
lean_dec(v_a_5227_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_5238_, size_t v_sz_5239_, size_t v_i_5240_, lean_object* v_b_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
uint8_t v___x_5252_; 
v___x_5252_ = lean_usize_dec_lt(v_i_5240_, v_sz_5239_);
if (v___x_5252_ == 0)
{
lean_object* v___x_5253_; 
v___x_5253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5253_, 0, v_b_5241_);
return v___x_5253_;
}
else
{
lean_object* v_snd_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5280_; 
v_snd_5254_ = lean_ctor_get(v_b_5241_, 1);
v_isSharedCheck_5280_ = !lean_is_exclusive(v_b_5241_);
if (v_isSharedCheck_5280_ == 0)
{
lean_object* v_unused_5281_; 
v_unused_5281_ = lean_ctor_get(v_b_5241_, 0);
lean_dec(v_unused_5281_);
v___x_5256_ = v_b_5241_;
v_isShared_5257_ = v_isSharedCheck_5280_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_snd_5254_);
lean_dec(v_b_5241_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5280_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5258_; lean_object* v_a_5260_; lean_object* v_a_5267_; lean_object* v___x_5268_; 
v___x_5258_ = lean_box(0);
v_a_5267_ = lean_array_uget_borrowed(v_as_5238_, v_i_5240_);
lean_inc(v_a_5267_);
v___x_5268_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5267_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
if (lean_obj_tag(v___x_5268_) == 0)
{
lean_object* v_a_5269_; uint8_t v___x_5270_; 
v_a_5269_ = lean_ctor_get(v___x_5268_, 0);
lean_inc(v_a_5269_);
lean_dec_ref_known(v___x_5268_, 1);
v___x_5270_ = lean_unbox(v_a_5269_);
lean_dec(v_a_5269_);
if (v___x_5270_ == 0)
{
v_a_5260_ = v_snd_5254_;
goto v___jp_5259_;
}
else
{
lean_object* v___x_5271_; 
lean_inc(v_a_5267_);
v___x_5271_ = l_Lean_PersistentArray_push___redArg(v_snd_5254_, v_a_5267_);
v_a_5260_ = v___x_5271_;
goto v___jp_5259_;
}
}
else
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5279_; 
lean_del_object(v___x_5256_);
lean_dec(v_snd_5254_);
v_a_5272_ = lean_ctor_get(v___x_5268_, 0);
v_isSharedCheck_5279_ = !lean_is_exclusive(v___x_5268_);
if (v_isSharedCheck_5279_ == 0)
{
v___x_5274_ = v___x_5268_;
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5268_);
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
v___jp_5259_:
{
lean_object* v___x_5262_; 
if (v_isShared_5257_ == 0)
{
lean_ctor_set(v___x_5256_, 1, v_a_5260_);
lean_ctor_set(v___x_5256_, 0, v___x_5258_);
v___x_5262_ = v___x_5256_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5258_);
lean_ctor_set(v_reuseFailAlloc_5266_, 1, v_a_5260_);
v___x_5262_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
size_t v___x_5263_; size_t v___x_5264_; 
v___x_5263_ = ((size_t)1ULL);
v___x_5264_ = lean_usize_add(v_i_5240_, v___x_5263_);
v_i_5240_ = v___x_5264_;
v_b_5241_ = v___x_5262_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5282_, lean_object* v_sz_5283_, lean_object* v_i_5284_, lean_object* v_b_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_){
_start:
{
size_t v_sz_boxed_5296_; size_t v_i_boxed_5297_; lean_object* v_res_5298_; 
v_sz_boxed_5296_ = lean_unbox_usize(v_sz_5283_);
lean_dec(v_sz_5283_);
v_i_boxed_5297_ = lean_unbox_usize(v_i_5284_);
lean_dec(v_i_5284_);
v_res_5298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5282_, v_sz_boxed_5296_, v_i_boxed_5297_, v_b_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_);
lean_dec(v___y_5294_);
lean_dec_ref(v___y_5293_);
lean_dec(v___y_5292_);
lean_dec_ref(v___y_5291_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v_as_5282_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5299_, size_t v_sz_5300_, size_t v_i_5301_, lean_object* v_b_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_){
_start:
{
uint8_t v___x_5313_; 
v___x_5313_ = lean_usize_dec_lt(v_i_5301_, v_sz_5300_);
if (v___x_5313_ == 0)
{
lean_object* v___x_5314_; 
v___x_5314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5314_, 0, v_b_5302_);
return v___x_5314_;
}
else
{
lean_object* v_snd_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5341_; 
v_snd_5315_ = lean_ctor_get(v_b_5302_, 1);
v_isSharedCheck_5341_ = !lean_is_exclusive(v_b_5302_);
if (v_isSharedCheck_5341_ == 0)
{
lean_object* v_unused_5342_; 
v_unused_5342_ = lean_ctor_get(v_b_5302_, 0);
lean_dec(v_unused_5342_);
v___x_5317_ = v_b_5302_;
v_isShared_5318_ = v_isSharedCheck_5341_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_snd_5315_);
lean_dec(v_b_5302_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5341_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v___x_5319_; lean_object* v_a_5321_; lean_object* v_a_5328_; lean_object* v___x_5329_; 
v___x_5319_ = lean_box(0);
v_a_5328_ = lean_array_uget_borrowed(v_as_5299_, v_i_5301_);
lean_inc(v_a_5328_);
v___x_5329_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5328_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_);
if (lean_obj_tag(v___x_5329_) == 0)
{
lean_object* v_a_5330_; uint8_t v___x_5331_; 
v_a_5330_ = lean_ctor_get(v___x_5329_, 0);
lean_inc(v_a_5330_);
lean_dec_ref_known(v___x_5329_, 1);
v___x_5331_ = lean_unbox(v_a_5330_);
lean_dec(v_a_5330_);
if (v___x_5331_ == 0)
{
v_a_5321_ = v_snd_5315_;
goto v___jp_5320_;
}
else
{
lean_object* v___x_5332_; 
lean_inc(v_a_5328_);
v___x_5332_ = l_Lean_PersistentArray_push___redArg(v_snd_5315_, v_a_5328_);
v_a_5321_ = v___x_5332_;
goto v___jp_5320_;
}
}
else
{
lean_object* v_a_5333_; lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5340_; 
lean_del_object(v___x_5317_);
lean_dec(v_snd_5315_);
v_a_5333_ = lean_ctor_get(v___x_5329_, 0);
v_isSharedCheck_5340_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5340_ == 0)
{
v___x_5335_ = v___x_5329_;
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
else
{
lean_inc(v_a_5333_);
lean_dec(v___x_5329_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v___x_5338_; 
if (v_isShared_5336_ == 0)
{
v___x_5338_ = v___x_5335_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_a_5333_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
}
v___jp_5320_:
{
lean_object* v___x_5323_; 
if (v_isShared_5318_ == 0)
{
lean_ctor_set(v___x_5317_, 1, v_a_5321_);
lean_ctor_set(v___x_5317_, 0, v___x_5319_);
v___x_5323_ = v___x_5317_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5319_);
lean_ctor_set(v_reuseFailAlloc_5327_, 1, v_a_5321_);
v___x_5323_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
size_t v___x_5324_; size_t v___x_5325_; lean_object* v___x_5326_; 
v___x_5324_ = ((size_t)1ULL);
v___x_5325_ = lean_usize_add(v_i_5301_, v___x_5324_);
v___x_5326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5299_, v_sz_5300_, v___x_5325_, v___x_5323_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_);
return v___x_5326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5343_, lean_object* v_sz_5344_, lean_object* v_i_5345_, lean_object* v_b_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_){
_start:
{
size_t v_sz_boxed_5357_; size_t v_i_boxed_5358_; lean_object* v_res_5359_; 
v_sz_boxed_5357_ = lean_unbox_usize(v_sz_5344_);
lean_dec(v_sz_5344_);
v_i_boxed_5358_ = lean_unbox_usize(v_i_5345_);
lean_dec(v_i_5345_);
v_res_5359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5343_, v_sz_boxed_5357_, v_i_boxed_5358_, v_b_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
lean_dec(v___y_5353_);
lean_dec_ref(v___y_5352_);
lean_dec(v___y_5351_);
lean_dec_ref(v___y_5350_);
lean_dec(v___y_5349_);
lean_dec_ref(v___y_5348_);
lean_dec(v___y_5347_);
lean_dec_ref(v_as_5343_);
return v_res_5359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5360_, size_t v_sz_5361_, size_t v_i_5362_, lean_object* v_b_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_){
_start:
{
uint8_t v___x_5374_; 
v___x_5374_ = lean_usize_dec_lt(v_i_5362_, v_sz_5361_);
if (v___x_5374_ == 0)
{
lean_object* v___x_5375_; 
v___x_5375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5375_, 0, v_b_5363_);
return v___x_5375_;
}
else
{
lean_object* v_snd_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5402_; 
v_snd_5376_ = lean_ctor_get(v_b_5363_, 1);
v_isSharedCheck_5402_ = !lean_is_exclusive(v_b_5363_);
if (v_isSharedCheck_5402_ == 0)
{
lean_object* v_unused_5403_; 
v_unused_5403_ = lean_ctor_get(v_b_5363_, 0);
lean_dec(v_unused_5403_);
v___x_5378_ = v_b_5363_;
v_isShared_5379_ = v_isSharedCheck_5402_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_snd_5376_);
lean_dec(v_b_5363_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5402_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5380_; lean_object* v_a_5382_; lean_object* v_a_5389_; lean_object* v___x_5390_; 
v___x_5380_ = lean_box(0);
v_a_5389_ = lean_array_uget_borrowed(v_as_5360_, v_i_5362_);
lean_inc(v_a_5389_);
v___x_5390_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5389_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_);
if (lean_obj_tag(v___x_5390_) == 0)
{
lean_object* v_a_5391_; uint8_t v___x_5392_; 
v_a_5391_ = lean_ctor_get(v___x_5390_, 0);
lean_inc(v_a_5391_);
lean_dec_ref_known(v___x_5390_, 1);
v___x_5392_ = lean_unbox(v_a_5391_);
lean_dec(v_a_5391_);
if (v___x_5392_ == 0)
{
v_a_5382_ = v_snd_5376_;
goto v___jp_5381_;
}
else
{
lean_object* v___x_5393_; 
lean_inc(v_a_5389_);
v___x_5393_ = l_Lean_PersistentArray_push___redArg(v_snd_5376_, v_a_5389_);
v_a_5382_ = v___x_5393_;
goto v___jp_5381_;
}
}
else
{
lean_object* v_a_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5401_; 
lean_del_object(v___x_5378_);
lean_dec(v_snd_5376_);
v_a_5394_ = lean_ctor_get(v___x_5390_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___x_5390_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5396_ = v___x_5390_;
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___x_5390_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___x_5399_; 
if (v_isShared_5397_ == 0)
{
v___x_5399_ = v___x_5396_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_a_5394_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
v___jp_5381_:
{
lean_object* v___x_5384_; 
if (v_isShared_5379_ == 0)
{
lean_ctor_set(v___x_5378_, 1, v_a_5382_);
lean_ctor_set(v___x_5378_, 0, v___x_5380_);
v___x_5384_ = v___x_5378_;
goto v_reusejp_5383_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v___x_5380_);
lean_ctor_set(v_reuseFailAlloc_5388_, 1, v_a_5382_);
v___x_5384_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5383_;
}
v_reusejp_5383_:
{
size_t v___x_5385_; size_t v___x_5386_; 
v___x_5385_ = ((size_t)1ULL);
v___x_5386_ = lean_usize_add(v_i_5362_, v___x_5385_);
v_i_5362_ = v___x_5386_;
v_b_5363_ = v___x_5384_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5404_, lean_object* v_sz_5405_, lean_object* v_i_5406_, lean_object* v_b_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_){
_start:
{
size_t v_sz_boxed_5418_; size_t v_i_boxed_5419_; lean_object* v_res_5420_; 
v_sz_boxed_5418_ = lean_unbox_usize(v_sz_5405_);
lean_dec(v_sz_5405_);
v_i_boxed_5419_ = lean_unbox_usize(v_i_5406_);
lean_dec(v_i_5406_);
v_res_5420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5404_, v_sz_boxed_5418_, v_i_boxed_5419_, v_b_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
lean_dec(v___y_5416_);
lean_dec_ref(v___y_5415_);
lean_dec(v___y_5414_);
lean_dec_ref(v___y_5413_);
lean_dec(v___y_5412_);
lean_dec_ref(v___y_5411_);
lean_dec(v___y_5410_);
lean_dec_ref(v___y_5409_);
lean_dec(v___y_5408_);
lean_dec_ref(v_as_5404_);
return v_res_5420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5421_, size_t v_sz_5422_, size_t v_i_5423_, lean_object* v_b_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_){
_start:
{
uint8_t v___x_5435_; 
v___x_5435_ = lean_usize_dec_lt(v_i_5423_, v_sz_5422_);
if (v___x_5435_ == 0)
{
lean_object* v___x_5436_; 
v___x_5436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5436_, 0, v_b_5424_);
return v___x_5436_;
}
else
{
lean_object* v_snd_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5463_; 
v_snd_5437_ = lean_ctor_get(v_b_5424_, 1);
v_isSharedCheck_5463_ = !lean_is_exclusive(v_b_5424_);
if (v_isSharedCheck_5463_ == 0)
{
lean_object* v_unused_5464_; 
v_unused_5464_ = lean_ctor_get(v_b_5424_, 0);
lean_dec(v_unused_5464_);
v___x_5439_ = v_b_5424_;
v_isShared_5440_ = v_isSharedCheck_5463_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_snd_5437_);
lean_dec(v_b_5424_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5463_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5441_; lean_object* v_a_5443_; lean_object* v_a_5450_; lean_object* v___x_5451_; 
v___x_5441_ = lean_box(0);
v_a_5450_ = lean_array_uget_borrowed(v_as_5421_, v_i_5423_);
lean_inc(v_a_5450_);
v___x_5451_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5450_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_);
if (lean_obj_tag(v___x_5451_) == 0)
{
lean_object* v_a_5452_; uint8_t v___x_5453_; 
v_a_5452_ = lean_ctor_get(v___x_5451_, 0);
lean_inc(v_a_5452_);
lean_dec_ref_known(v___x_5451_, 1);
v___x_5453_ = lean_unbox(v_a_5452_);
lean_dec(v_a_5452_);
if (v___x_5453_ == 0)
{
v_a_5443_ = v_snd_5437_;
goto v___jp_5442_;
}
else
{
lean_object* v___x_5454_; 
lean_inc(v_a_5450_);
v___x_5454_ = l_Lean_PersistentArray_push___redArg(v_snd_5437_, v_a_5450_);
v_a_5443_ = v___x_5454_;
goto v___jp_5442_;
}
}
else
{
lean_object* v_a_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5462_; 
lean_del_object(v___x_5439_);
lean_dec(v_snd_5437_);
v_a_5455_ = lean_ctor_get(v___x_5451_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5451_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5457_ = v___x_5451_;
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_a_5455_);
lean_dec(v___x_5451_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v___x_5460_; 
if (v_isShared_5458_ == 0)
{
v___x_5460_ = v___x_5457_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5455_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
v___jp_5442_:
{
lean_object* v___x_5445_; 
if (v_isShared_5440_ == 0)
{
lean_ctor_set(v___x_5439_, 1, v_a_5443_);
lean_ctor_set(v___x_5439_, 0, v___x_5441_);
v___x_5445_ = v___x_5439_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v___x_5441_);
lean_ctor_set(v_reuseFailAlloc_5449_, 1, v_a_5443_);
v___x_5445_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
size_t v___x_5446_; size_t v___x_5447_; lean_object* v___x_5448_; 
v___x_5446_ = ((size_t)1ULL);
v___x_5447_ = lean_usize_add(v_i_5423_, v___x_5446_);
v___x_5448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5421_, v_sz_5422_, v___x_5447_, v___x_5445_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_);
return v___x_5448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5465_, lean_object* v_sz_5466_, lean_object* v_i_5467_, lean_object* v_b_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_){
_start:
{
size_t v_sz_boxed_5479_; size_t v_i_boxed_5480_; lean_object* v_res_5481_; 
v_sz_boxed_5479_ = lean_unbox_usize(v_sz_5466_);
lean_dec(v_sz_5466_);
v_i_boxed_5480_ = lean_unbox_usize(v_i_5467_);
lean_dec(v_i_5467_);
v_res_5481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5465_, v_sz_boxed_5479_, v_i_boxed_5480_, v_b_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec(v___y_5475_);
lean_dec_ref(v___y_5474_);
lean_dec(v___y_5473_);
lean_dec_ref(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
lean_dec(v___y_5469_);
lean_dec_ref(v_as_5465_);
return v_res_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5482_, lean_object* v_n_5483_, lean_object* v_b_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_){
_start:
{
if (lean_obj_tag(v_n_5483_) == 0)
{
lean_object* v_cs_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; size_t v_sz_5498_; size_t v___x_5499_; lean_object* v___x_5500_; 
v_cs_5495_ = lean_ctor_get(v_n_5483_, 0);
v___x_5496_ = lean_box(0);
v___x_5497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5497_, 0, v___x_5496_);
lean_ctor_set(v___x_5497_, 1, v_b_5484_);
v_sz_5498_ = lean_array_size(v_cs_5495_);
v___x_5499_ = ((size_t)0ULL);
v___x_5500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5482_, v_cs_5495_, v_sz_5498_, v___x_5499_, v___x_5497_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
if (lean_obj_tag(v___x_5500_) == 0)
{
lean_object* v_a_5501_; lean_object* v___x_5503_; uint8_t v_isShared_5504_; uint8_t v_isSharedCheck_5515_; 
v_a_5501_ = lean_ctor_get(v___x_5500_, 0);
v_isSharedCheck_5515_ = !lean_is_exclusive(v___x_5500_);
if (v_isSharedCheck_5515_ == 0)
{
v___x_5503_ = v___x_5500_;
v_isShared_5504_ = v_isSharedCheck_5515_;
goto v_resetjp_5502_;
}
else
{
lean_inc(v_a_5501_);
lean_dec(v___x_5500_);
v___x_5503_ = lean_box(0);
v_isShared_5504_ = v_isSharedCheck_5515_;
goto v_resetjp_5502_;
}
v_resetjp_5502_:
{
lean_object* v_fst_5505_; 
v_fst_5505_ = lean_ctor_get(v_a_5501_, 0);
if (lean_obj_tag(v_fst_5505_) == 0)
{
lean_object* v_snd_5506_; lean_object* v___x_5507_; lean_object* v___x_5509_; 
v_snd_5506_ = lean_ctor_get(v_a_5501_, 1);
lean_inc(v_snd_5506_);
lean_dec(v_a_5501_);
v___x_5507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5507_, 0, v_snd_5506_);
if (v_isShared_5504_ == 0)
{
lean_ctor_set(v___x_5503_, 0, v___x_5507_);
v___x_5509_ = v___x_5503_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v___x_5507_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
}
}
else
{
lean_object* v_val_5511_; lean_object* v___x_5513_; 
lean_inc_ref(v_fst_5505_);
lean_dec(v_a_5501_);
v_val_5511_ = lean_ctor_get(v_fst_5505_, 0);
lean_inc(v_val_5511_);
lean_dec_ref_known(v_fst_5505_, 1);
if (v_isShared_5504_ == 0)
{
lean_ctor_set(v___x_5503_, 0, v_val_5511_);
v___x_5513_ = v___x_5503_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_val_5511_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
}
}
else
{
lean_object* v_a_5516_; lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5523_; 
v_a_5516_ = lean_ctor_get(v___x_5500_, 0);
v_isSharedCheck_5523_ = !lean_is_exclusive(v___x_5500_);
if (v_isSharedCheck_5523_ == 0)
{
v___x_5518_ = v___x_5500_;
v_isShared_5519_ = v_isSharedCheck_5523_;
goto v_resetjp_5517_;
}
else
{
lean_inc(v_a_5516_);
lean_dec(v___x_5500_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5523_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v___x_5521_; 
if (v_isShared_5519_ == 0)
{
v___x_5521_ = v___x_5518_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_a_5516_);
v___x_5521_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
return v___x_5521_;
}
}
}
}
else
{
lean_object* v_vs_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; size_t v_sz_5527_; size_t v___x_5528_; lean_object* v___x_5529_; 
v_vs_5524_ = lean_ctor_get(v_n_5483_, 0);
v___x_5525_ = lean_box(0);
v___x_5526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5526_, 0, v___x_5525_);
lean_ctor_set(v___x_5526_, 1, v_b_5484_);
v_sz_5527_ = lean_array_size(v_vs_5524_);
v___x_5528_ = ((size_t)0ULL);
v___x_5529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5524_, v_sz_5527_, v___x_5528_, v___x_5526_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_);
if (lean_obj_tag(v___x_5529_) == 0)
{
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5544_; 
v_a_5530_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5544_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5544_ == 0)
{
v___x_5532_ = v___x_5529_;
v_isShared_5533_ = v_isSharedCheck_5544_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5529_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5544_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v_fst_5534_; 
v_fst_5534_ = lean_ctor_get(v_a_5530_, 0);
if (lean_obj_tag(v_fst_5534_) == 0)
{
lean_object* v_snd_5535_; lean_object* v___x_5536_; lean_object* v___x_5538_; 
v_snd_5535_ = lean_ctor_get(v_a_5530_, 1);
lean_inc(v_snd_5535_);
lean_dec(v_a_5530_);
v___x_5536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5536_, 0, v_snd_5535_);
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 0, v___x_5536_);
v___x_5538_ = v___x_5532_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v___x_5536_);
v___x_5538_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
return v___x_5538_;
}
}
else
{
lean_object* v_val_5540_; lean_object* v___x_5542_; 
lean_inc_ref(v_fst_5534_);
lean_dec(v_a_5530_);
v_val_5540_ = lean_ctor_get(v_fst_5534_, 0);
lean_inc(v_val_5540_);
lean_dec_ref_known(v_fst_5534_, 1);
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 0, v_val_5540_);
v___x_5542_ = v___x_5532_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v_val_5540_);
v___x_5542_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
return v___x_5542_;
}
}
}
}
else
{
lean_object* v_a_5545_; lean_object* v___x_5547_; uint8_t v_isShared_5548_; uint8_t v_isSharedCheck_5552_; 
v_a_5545_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5552_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5547_ = v___x_5529_;
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
else
{
lean_inc(v_a_5545_);
lean_dec(v___x_5529_);
v___x_5547_ = lean_box(0);
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
v_resetjp_5546_:
{
lean_object* v___x_5550_; 
if (v_isShared_5548_ == 0)
{
v___x_5550_ = v___x_5547_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_a_5545_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
return v___x_5550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5553_, lean_object* v_as_5554_, size_t v_sz_5555_, size_t v_i_5556_, lean_object* v_b_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_){
_start:
{
uint8_t v___x_5568_; 
v___x_5568_ = lean_usize_dec_lt(v_i_5556_, v_sz_5555_);
if (v___x_5568_ == 0)
{
lean_object* v___x_5569_; 
v___x_5569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5569_, 0, v_b_5557_);
return v___x_5569_;
}
else
{
lean_object* v_snd_5570_; lean_object* v___x_5572_; uint8_t v_isShared_5573_; uint8_t v_isSharedCheck_5604_; 
v_snd_5570_ = lean_ctor_get(v_b_5557_, 1);
v_isSharedCheck_5604_ = !lean_is_exclusive(v_b_5557_);
if (v_isSharedCheck_5604_ == 0)
{
lean_object* v_unused_5605_; 
v_unused_5605_ = lean_ctor_get(v_b_5557_, 0);
lean_dec(v_unused_5605_);
v___x_5572_ = v_b_5557_;
v_isShared_5573_ = v_isSharedCheck_5604_;
goto v_resetjp_5571_;
}
else
{
lean_inc(v_snd_5570_);
lean_dec(v_b_5557_);
v___x_5572_ = lean_box(0);
v_isShared_5573_ = v_isSharedCheck_5604_;
goto v_resetjp_5571_;
}
v_resetjp_5571_:
{
lean_object* v___x_5574_; lean_object* v_a_5575_; lean_object* v___x_5576_; 
v___x_5574_ = lean_box(0);
v_a_5575_ = lean_array_uget_borrowed(v_as_5554_, v_i_5556_);
lean_inc(v_snd_5570_);
v___x_5576_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5553_, v_a_5575_, v_snd_5570_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_);
if (lean_obj_tag(v___x_5576_) == 0)
{
lean_object* v_a_5577_; lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5595_; 
v_a_5577_ = lean_ctor_get(v___x_5576_, 0);
v_isSharedCheck_5595_ = !lean_is_exclusive(v___x_5576_);
if (v_isSharedCheck_5595_ == 0)
{
v___x_5579_ = v___x_5576_;
v_isShared_5580_ = v_isSharedCheck_5595_;
goto v_resetjp_5578_;
}
else
{
lean_inc(v_a_5577_);
lean_dec(v___x_5576_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5595_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
if (lean_obj_tag(v_a_5577_) == 0)
{
lean_object* v___x_5581_; lean_object* v___x_5583_; 
v___x_5581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5581_, 0, v_a_5577_);
if (v_isShared_5573_ == 0)
{
lean_ctor_set(v___x_5572_, 0, v___x_5581_);
v___x_5583_ = v___x_5572_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v___x_5581_);
lean_ctor_set(v_reuseFailAlloc_5587_, 1, v_snd_5570_);
v___x_5583_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
lean_object* v___x_5585_; 
if (v_isShared_5580_ == 0)
{
lean_ctor_set(v___x_5579_, 0, v___x_5583_);
v___x_5585_ = v___x_5579_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v___x_5583_);
v___x_5585_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
return v___x_5585_;
}
}
}
else
{
lean_object* v_a_5588_; lean_object* v___x_5590_; 
lean_del_object(v___x_5579_);
lean_dec(v_snd_5570_);
v_a_5588_ = lean_ctor_get(v_a_5577_, 0);
lean_inc(v_a_5588_);
lean_dec_ref_known(v_a_5577_, 1);
if (v_isShared_5573_ == 0)
{
lean_ctor_set(v___x_5572_, 1, v_a_5588_);
lean_ctor_set(v___x_5572_, 0, v___x_5574_);
v___x_5590_ = v___x_5572_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5574_);
lean_ctor_set(v_reuseFailAlloc_5594_, 1, v_a_5588_);
v___x_5590_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
size_t v___x_5591_; size_t v___x_5592_; 
v___x_5591_ = ((size_t)1ULL);
v___x_5592_ = lean_usize_add(v_i_5556_, v___x_5591_);
v_i_5556_ = v___x_5592_;
v_b_5557_ = v___x_5590_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5596_; lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5603_; 
lean_del_object(v___x_5572_);
lean_dec(v_snd_5570_);
v_a_5596_ = lean_ctor_get(v___x_5576_, 0);
v_isSharedCheck_5603_ = !lean_is_exclusive(v___x_5576_);
if (v_isSharedCheck_5603_ == 0)
{
v___x_5598_ = v___x_5576_;
v_isShared_5599_ = v_isSharedCheck_5603_;
goto v_resetjp_5597_;
}
else
{
lean_inc(v_a_5596_);
lean_dec(v___x_5576_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5603_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
lean_object* v___x_5601_; 
if (v_isShared_5599_ == 0)
{
v___x_5601_ = v___x_5598_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_a_5596_);
v___x_5601_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
return v___x_5601_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5606_, lean_object* v_as_5607_, lean_object* v_sz_5608_, lean_object* v_i_5609_, lean_object* v_b_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_){
_start:
{
size_t v_sz_boxed_5621_; size_t v_i_boxed_5622_; lean_object* v_res_5623_; 
v_sz_boxed_5621_ = lean_unbox_usize(v_sz_5608_);
lean_dec(v_sz_5608_);
v_i_boxed_5622_ = lean_unbox_usize(v_i_5609_);
lean_dec(v_i_5609_);
v_res_5623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5606_, v_as_5607_, v_sz_boxed_5621_, v_i_boxed_5622_, v_b_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
lean_dec(v___y_5619_);
lean_dec_ref(v___y_5618_);
lean_dec(v___y_5617_);
lean_dec_ref(v___y_5616_);
lean_dec(v___y_5615_);
lean_dec_ref(v___y_5614_);
lean_dec(v___y_5613_);
lean_dec_ref(v___y_5612_);
lean_dec(v___y_5611_);
lean_dec_ref(v_as_5607_);
lean_dec_ref(v_init_5606_);
return v_res_5623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5624_, lean_object* v_n_5625_, lean_object* v_b_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_){
_start:
{
lean_object* v_res_5637_; 
v_res_5637_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5624_, v_n_5625_, v_b_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec(v___y_5629_);
lean_dec_ref(v___y_5628_);
lean_dec(v___y_5627_);
lean_dec_ref(v_n_5625_);
lean_dec_ref(v_init_5624_);
return v_res_5637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5638_, lean_object* v_init_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_){
_start:
{
lean_object* v_root_5650_; lean_object* v_tail_5651_; lean_object* v___x_5652_; 
v_root_5650_ = lean_ctor_get(v_t_5638_, 0);
v_tail_5651_ = lean_ctor_get(v_t_5638_, 1);
lean_inc_ref(v_init_5639_);
v___x_5652_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5639_, v_root_5650_, v_init_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_);
lean_dec_ref(v_init_5639_);
if (lean_obj_tag(v___x_5652_) == 0)
{
lean_object* v_a_5653_; lean_object* v___x_5655_; uint8_t v_isShared_5656_; uint8_t v_isSharedCheck_5689_; 
v_a_5653_ = lean_ctor_get(v___x_5652_, 0);
v_isSharedCheck_5689_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5689_ == 0)
{
v___x_5655_ = v___x_5652_;
v_isShared_5656_ = v_isSharedCheck_5689_;
goto v_resetjp_5654_;
}
else
{
lean_inc(v_a_5653_);
lean_dec(v___x_5652_);
v___x_5655_ = lean_box(0);
v_isShared_5656_ = v_isSharedCheck_5689_;
goto v_resetjp_5654_;
}
v_resetjp_5654_:
{
if (lean_obj_tag(v_a_5653_) == 0)
{
lean_object* v_a_5657_; lean_object* v___x_5659_; 
v_a_5657_ = lean_ctor_get(v_a_5653_, 0);
lean_inc(v_a_5657_);
lean_dec_ref_known(v_a_5653_, 1);
if (v_isShared_5656_ == 0)
{
lean_ctor_set(v___x_5655_, 0, v_a_5657_);
v___x_5659_ = v___x_5655_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_a_5657_);
v___x_5659_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
return v___x_5659_;
}
}
else
{
lean_object* v_a_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; size_t v_sz_5664_; size_t v___x_5665_; lean_object* v___x_5666_; 
lean_del_object(v___x_5655_);
v_a_5661_ = lean_ctor_get(v_a_5653_, 0);
lean_inc(v_a_5661_);
lean_dec_ref_known(v_a_5653_, 1);
v___x_5662_ = lean_box(0);
v___x_5663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
lean_ctor_set(v___x_5663_, 1, v_a_5661_);
v_sz_5664_ = lean_array_size(v_tail_5651_);
v___x_5665_ = ((size_t)0ULL);
v___x_5666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5651_, v_sz_5664_, v___x_5665_, v___x_5663_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_);
if (lean_obj_tag(v___x_5666_) == 0)
{
lean_object* v_a_5667_; lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5680_; 
v_a_5667_ = lean_ctor_get(v___x_5666_, 0);
v_isSharedCheck_5680_ = !lean_is_exclusive(v___x_5666_);
if (v_isSharedCheck_5680_ == 0)
{
v___x_5669_ = v___x_5666_;
v_isShared_5670_ = v_isSharedCheck_5680_;
goto v_resetjp_5668_;
}
else
{
lean_inc(v_a_5667_);
lean_dec(v___x_5666_);
v___x_5669_ = lean_box(0);
v_isShared_5670_ = v_isSharedCheck_5680_;
goto v_resetjp_5668_;
}
v_resetjp_5668_:
{
lean_object* v_fst_5671_; 
v_fst_5671_ = lean_ctor_get(v_a_5667_, 0);
if (lean_obj_tag(v_fst_5671_) == 0)
{
lean_object* v_snd_5672_; lean_object* v___x_5674_; 
v_snd_5672_ = lean_ctor_get(v_a_5667_, 1);
lean_inc(v_snd_5672_);
lean_dec(v_a_5667_);
if (v_isShared_5670_ == 0)
{
lean_ctor_set(v___x_5669_, 0, v_snd_5672_);
v___x_5674_ = v___x_5669_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_snd_5672_);
v___x_5674_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
return v___x_5674_;
}
}
else
{
lean_object* v_val_5676_; lean_object* v___x_5678_; 
lean_inc_ref(v_fst_5671_);
lean_dec(v_a_5667_);
v_val_5676_ = lean_ctor_get(v_fst_5671_, 0);
lean_inc(v_val_5676_);
lean_dec_ref_known(v_fst_5671_, 1);
if (v_isShared_5670_ == 0)
{
lean_ctor_set(v___x_5669_, 0, v_val_5676_);
v___x_5678_ = v___x_5669_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_val_5676_);
v___x_5678_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
return v___x_5678_;
}
}
}
}
else
{
lean_object* v_a_5681_; lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5688_; 
v_a_5681_ = lean_ctor_get(v___x_5666_, 0);
v_isSharedCheck_5688_ = !lean_is_exclusive(v___x_5666_);
if (v_isSharedCheck_5688_ == 0)
{
v___x_5683_ = v___x_5666_;
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
else
{
lean_inc(v_a_5681_);
lean_dec(v___x_5666_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v___x_5686_; 
if (v_isShared_5684_ == 0)
{
v___x_5686_ = v___x_5683_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_a_5681_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
}
}
}
else
{
lean_object* v_a_5690_; lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5697_; 
v_a_5690_ = lean_ctor_get(v___x_5652_, 0);
v_isSharedCheck_5697_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5697_ == 0)
{
v___x_5692_ = v___x_5652_;
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_a_5690_);
lean_dec(v___x_5652_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5698_, lean_object* v_init_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_){
_start:
{
lean_object* v_res_5710_; 
v_res_5710_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5698_, v_init_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_);
lean_dec(v___y_5708_);
lean_dec_ref(v___y_5707_);
lean_dec(v___y_5706_);
lean_dec_ref(v___y_5705_);
lean_dec(v___y_5704_);
lean_dec_ref(v___y_5703_);
lean_dec(v___y_5702_);
lean_dec_ref(v___y_5701_);
lean_dec(v___y_5700_);
lean_dec_ref(v_t_5698_);
return v_res_5710_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; 
v___x_5711_ = lean_unsigned_to_nat(32u);
v___x_5712_ = lean_mk_empty_array_with_capacity(v___x_5711_);
v___x_5713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5712_);
return v___x_5713_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v_result_5719_; 
v___x_5714_ = ((size_t)5ULL);
v___x_5715_ = lean_unsigned_to_nat(0u);
v___x_5716_ = lean_unsigned_to_nat(32u);
v___x_5717_ = lean_mk_empty_array_with_capacity(v___x_5716_);
v___x_5718_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5719_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5719_, 0, v___x_5718_);
lean_ctor_set(v_result_5719_, 1, v___x_5717_);
lean_ctor_set(v_result_5719_, 2, v___x_5715_);
lean_ctor_set(v_result_5719_, 3, v___x_5715_);
lean_ctor_set_usize(v_result_5719_, 4, v___x_5714_);
return v_result_5719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_, lean_object* v_a_5723_, lean_object* v_a_5724_, lean_object* v_a_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_){
_start:
{
lean_object* v_result_5731_; lean_object* v___x_5732_; 
v_result_5731_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5732_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5720_, v_result_5731_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_, v_a_5728_, v_a_5729_);
return v___x_5732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_, lean_object* v_a_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_){
_start:
{
lean_object* v_res_5744_; 
v_res_5744_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_);
lean_dec(v_a_5742_);
lean_dec_ref(v_a_5741_);
lean_dec(v_a_5740_);
lean_dec_ref(v_a_5739_);
lean_dec(v_a_5738_);
lean_dec_ref(v_a_5737_);
lean_dec(v_a_5736_);
lean_dec_ref(v_a_5735_);
lean_dec(v_a_5734_);
lean_dec_ref(v_thms_5733_);
return v_res_5744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(lean_object* v___x_5745_, uint8_t v___x_5746_, lean_object* v_keepIdentParam_5747_, lean_object* v_x_5748_, lean_object* v_mod_x3f_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_){
_start:
{
lean_object* v___x_5757_; lean_object* v_id_5758_; lean_object* v___x_5759_; uint8_t v___x_5760_; 
v___x_5757_ = lean_unsigned_to_nat(2u);
v_id_5758_ = l_Lean_Syntax_getArg(v___x_5745_, v___x_5757_);
v___x_5759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v_id_5758_);
v___x_5760_ = l_Lean_Syntax_isOfKind(v_id_5758_, v___x_5759_);
if (v___x_5760_ == 0)
{
lean_object* v___x_5761_; lean_object* v___x_5762_; 
lean_dec(v_id_5758_);
lean_dec(v_mod_x3f_5749_);
lean_dec_ref(v_keepIdentParam_5747_);
v___x_5761_ = lean_box(v___x_5746_);
v___x_5762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5761_);
return v___x_5762_;
}
else
{
lean_object* v___x_5763_; 
lean_inc(v___y_5755_);
lean_inc_ref(v___y_5754_);
lean_inc(v___y_5753_);
lean_inc_ref(v___y_5752_);
lean_inc(v___y_5751_);
lean_inc_ref(v___y_5750_);
v___x_5763_ = lean_apply_9(v_keepIdentParam_5747_, v_mod_x3f_5749_, v_id_5758_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_, lean_box(0));
return v___x_5763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1___boxed(lean_object* v___x_5764_, lean_object* v___x_5765_, lean_object* v_keepIdentParam_5766_, lean_object* v_x_5767_, lean_object* v_mod_x3f_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_){
_start:
{
uint8_t v___x_6759__boxed_5776_; lean_object* v_res_5777_; 
v___x_6759__boxed_5776_ = lean_unbox(v___x_5765_);
v_res_5777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(v___x_5764_, v___x_6759__boxed_5776_, v_keepIdentParam_5766_, v_x_5767_, v_mod_x3f_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_, v___y_5774_);
lean_dec(v___y_5774_);
lean_dec_ref(v___y_5773_);
lean_dec(v___y_5772_);
lean_dec_ref(v___y_5771_);
lean_dec(v___y_5770_);
lean_dec_ref(v___y_5769_);
lean_dec(v___x_5764_);
return v_res_5777_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0(void){
_start:
{
lean_object* v___x_5778_; lean_object* v___x_5779_; 
v___x_5778_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_5779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5779_, 0, v___x_5778_);
return v___x_5779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0(uint8_t v___x_5780_, uint8_t v___x_5781_, lean_object* v_mod_x3f_5782_, lean_object* v_id_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_){
_start:
{
lean_object* v___y_5792_; lean_object* v___y_5793_; lean_object* v___y_5794_; lean_object* v___y_5795_; lean_object* v___x_5848_; lean_object* v___x_5849_; 
v___x_5848_ = l_Lean_TSyntax_getId(v_id_5783_);
v___x_5849_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_5848_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
if (lean_obj_tag(v___x_5849_) == 0)
{
lean_object* v_a_5850_; lean_object* v___x_5852_; uint8_t v_isShared_5853_; uint8_t v_isSharedCheck_5860_; 
v_a_5850_ = lean_ctor_get(v___x_5849_, 0);
v_isSharedCheck_5860_ = !lean_is_exclusive(v___x_5849_);
if (v_isSharedCheck_5860_ == 0)
{
v___x_5852_ = v___x_5849_;
v_isShared_5853_ = v_isSharedCheck_5860_;
goto v_resetjp_5851_;
}
else
{
lean_inc(v_a_5850_);
lean_dec(v___x_5849_);
v___x_5852_ = lean_box(0);
v_isShared_5853_ = v_isSharedCheck_5860_;
goto v_resetjp_5851_;
}
v_resetjp_5851_:
{
if (lean_obj_tag(v_a_5850_) == 1)
{
lean_object* v_val_5854_; lean_object* v_snd_5855_; 
v_val_5854_ = lean_ctor_get(v_a_5850_, 0);
lean_inc(v_val_5854_);
lean_dec_ref_known(v_a_5850_, 1);
v_snd_5855_ = lean_ctor_get(v_val_5854_, 1);
lean_inc(v_snd_5855_);
lean_dec(v_val_5854_);
if (lean_obj_tag(v_snd_5855_) == 1)
{
lean_object* v___x_5856_; lean_object* v___x_5858_; 
lean_dec_ref_known(v_snd_5855_, 2);
lean_dec(v_id_5783_);
lean_dec(v_mod_x3f_5782_);
v___x_5856_ = lean_box(v___x_5781_);
if (v_isShared_5853_ == 0)
{
lean_ctor_set(v___x_5852_, 0, v___x_5856_);
v___x_5858_ = v___x_5852_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v___x_5856_);
v___x_5858_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5857_;
}
v_reusejp_5857_:
{
return v___x_5858_;
}
}
else
{
lean_dec(v_snd_5855_);
lean_del_object(v___x_5852_);
goto v___jp_5820_;
}
}
else
{
lean_del_object(v___x_5852_);
lean_dec(v_a_5850_);
goto v___jp_5820_;
}
}
}
else
{
lean_object* v_a_5861_; lean_object* v___x_5863_; uint8_t v_isShared_5864_; uint8_t v_isSharedCheck_5868_; 
lean_dec(v_id_5783_);
lean_dec(v_mod_x3f_5782_);
v_a_5861_ = lean_ctor_get(v___x_5849_, 0);
v_isSharedCheck_5868_ = !lean_is_exclusive(v___x_5849_);
if (v_isSharedCheck_5868_ == 0)
{
v___x_5863_ = v___x_5849_;
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
else
{
lean_inc(v_a_5861_);
lean_dec(v___x_5849_);
v___x_5863_ = lean_box(0);
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
v_resetjp_5862_:
{
lean_object* v___x_5866_; 
if (v_isShared_5864_ == 0)
{
v___x_5866_ = v___x_5863_;
goto v_reusejp_5865_;
}
else
{
lean_object* v_reuseFailAlloc_5867_; 
v_reuseFailAlloc_5867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_a_5861_);
v___x_5866_ = v_reuseFailAlloc_5867_;
goto v_reusejp_5865_;
}
v_reusejp_5865_:
{
return v___x_5866_;
}
}
}
v___jp_5791_:
{
lean_object* v___x_5796_; 
v___x_5796_ = l_Lean_realizeGlobalConstNoOverload(v_id_5783_, v___y_5794_, v___y_5795_);
if (lean_obj_tag(v___x_5796_) == 0)
{
lean_object* v_a_5797_; lean_object* v___x_5798_; 
v_a_5797_ = lean_ctor_get(v___x_5796_, 0);
lean_inc_n(v_a_5797_, 2);
lean_dec_ref_known(v___x_5796_, 1);
v___x_5798_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_a_5797_, v___x_5780_, v___y_5794_, v___y_5795_);
if (lean_obj_tag(v___x_5798_) == 0)
{
lean_object* v_a_5799_; uint8_t v___x_5800_; 
v_a_5799_ = lean_ctor_get(v___x_5798_, 0);
v___x_5800_ = lean_unbox(v_a_5799_);
if (v___x_5800_ == 0)
{
lean_object* v___x_5801_; lean_object* v___x_5802_; 
lean_dec_ref_known(v___x_5798_, 1);
v___x_5801_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0);
v___x_5802_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(v_a_5797_, v___x_5801_, v___y_5792_, v___y_5793_, v___y_5794_, v___y_5795_);
return v___x_5802_;
}
else
{
lean_dec(v_a_5797_);
return v___x_5798_;
}
}
else
{
lean_dec(v_a_5797_);
return v___x_5798_;
}
}
else
{
lean_object* v_a_5803_; lean_object* v___x_5805_; uint8_t v_isShared_5806_; uint8_t v_isSharedCheck_5819_; 
v_a_5803_ = lean_ctor_get(v___x_5796_, 0);
v_isSharedCheck_5819_ = !lean_is_exclusive(v___x_5796_);
if (v_isSharedCheck_5819_ == 0)
{
v___x_5805_ = v___x_5796_;
v_isShared_5806_ = v_isSharedCheck_5819_;
goto v_resetjp_5804_;
}
else
{
lean_inc(v_a_5803_);
lean_dec(v___x_5796_);
v___x_5805_ = lean_box(0);
v_isShared_5806_ = v_isSharedCheck_5819_;
goto v_resetjp_5804_;
}
v_resetjp_5804_:
{
uint8_t v___x_5807_; 
v___x_5807_ = l_Lean_Exception_isInterrupt(v_a_5803_);
if (v___x_5807_ == 0)
{
uint8_t v___x_5808_; 
lean_inc(v_a_5803_);
v___x_5808_ = l_Lean_Exception_isRuntime(v_a_5803_);
if (v___x_5808_ == 0)
{
lean_object* v___x_5809_; lean_object* v___x_5811_; 
lean_dec(v_a_5803_);
v___x_5809_ = lean_box(v___x_5808_);
if (v_isShared_5806_ == 0)
{
lean_ctor_set_tag(v___x_5805_, 0);
lean_ctor_set(v___x_5805_, 0, v___x_5809_);
v___x_5811_ = v___x_5805_;
goto v_reusejp_5810_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v___x_5809_);
v___x_5811_ = v_reuseFailAlloc_5812_;
goto v_reusejp_5810_;
}
v_reusejp_5810_:
{
return v___x_5811_;
}
}
else
{
lean_object* v___x_5814_; 
if (v_isShared_5806_ == 0)
{
v___x_5814_ = v___x_5805_;
goto v_reusejp_5813_;
}
else
{
lean_object* v_reuseFailAlloc_5815_; 
v_reuseFailAlloc_5815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5815_, 0, v_a_5803_);
v___x_5814_ = v_reuseFailAlloc_5815_;
goto v_reusejp_5813_;
}
v_reusejp_5813_:
{
return v___x_5814_;
}
}
}
else
{
lean_object* v___x_5817_; 
if (v_isShared_5806_ == 0)
{
v___x_5817_ = v___x_5805_;
goto v_reusejp_5816_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v_a_5803_);
v___x_5817_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5816_;
}
v_reusejp_5816_:
{
return v___x_5817_;
}
}
}
}
}
v___jp_5820_:
{
if (lean_obj_tag(v_mod_x3f_5782_) == 1)
{
lean_object* v_val_5821_; lean_object* v___x_5822_; 
v_val_5821_ = lean_ctor_get(v_mod_x3f_5782_, 0);
lean_inc(v_val_5821_);
lean_dec_ref_known(v_mod_x3f_5782_, 1);
v___x_5822_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_5821_, v___y_5788_, v___y_5789_);
if (lean_obj_tag(v___x_5822_) == 0)
{
lean_object* v_a_5823_; lean_object* v___x_5825_; uint8_t v_isShared_5826_; uint8_t v_isSharedCheck_5839_; 
v_a_5823_ = lean_ctor_get(v___x_5822_, 0);
v_isSharedCheck_5839_ = !lean_is_exclusive(v___x_5822_);
if (v_isSharedCheck_5839_ == 0)
{
v___x_5825_ = v___x_5822_;
v_isShared_5826_ = v_isSharedCheck_5839_;
goto v_resetjp_5824_;
}
else
{
lean_inc(v_a_5823_);
lean_dec(v___x_5822_);
v___x_5825_ = lean_box(0);
v_isShared_5826_ = v_isSharedCheck_5839_;
goto v_resetjp_5824_;
}
v_resetjp_5824_:
{
switch(lean_obj_tag(v_a_5823_))
{
case 0:
{
lean_object* v___x_5827_; lean_object* v___x_5829_; 
lean_dec_ref_known(v_a_5823_, 1);
lean_dec(v_id_5783_);
v___x_5827_ = lean_box(v___x_5780_);
if (v_isShared_5826_ == 0)
{
lean_ctor_set(v___x_5825_, 0, v___x_5827_);
v___x_5829_ = v___x_5825_;
goto v_reusejp_5828_;
}
else
{
lean_object* v_reuseFailAlloc_5830_; 
v_reuseFailAlloc_5830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5830_, 0, v___x_5827_);
v___x_5829_ = v_reuseFailAlloc_5830_;
goto v_reusejp_5828_;
}
v_reusejp_5828_:
{
return v___x_5829_;
}
}
case 2:
{
lean_object* v___x_5831_; lean_object* v___x_5833_; 
lean_dec(v_id_5783_);
v___x_5831_ = lean_box(v___x_5780_);
if (v_isShared_5826_ == 0)
{
lean_ctor_set(v___x_5825_, 0, v___x_5831_);
v___x_5833_ = v___x_5825_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5834_; 
v_reuseFailAlloc_5834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5834_, 0, v___x_5831_);
v___x_5833_ = v_reuseFailAlloc_5834_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
return v___x_5833_;
}
}
case 3:
{
lean_del_object(v___x_5825_);
v___y_5792_ = v___y_5786_;
v___y_5793_ = v___y_5787_;
v___y_5794_ = v___y_5788_;
v___y_5795_ = v___y_5789_;
goto v___jp_5791_;
}
default: 
{
lean_object* v___x_5835_; lean_object* v___x_5837_; 
lean_dec(v_a_5823_);
lean_dec(v_id_5783_);
v___x_5835_ = lean_box(v___x_5781_);
if (v_isShared_5826_ == 0)
{
lean_ctor_set(v___x_5825_, 0, v___x_5835_);
v___x_5837_ = v___x_5825_;
goto v_reusejp_5836_;
}
else
{
lean_object* v_reuseFailAlloc_5838_; 
v_reuseFailAlloc_5838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5838_, 0, v___x_5835_);
v___x_5837_ = v_reuseFailAlloc_5838_;
goto v_reusejp_5836_;
}
v_reusejp_5836_:
{
return v___x_5837_;
}
}
}
}
}
else
{
lean_object* v_a_5840_; lean_object* v___x_5842_; uint8_t v_isShared_5843_; uint8_t v_isSharedCheck_5847_; 
lean_dec(v_id_5783_);
v_a_5840_ = lean_ctor_get(v___x_5822_, 0);
v_isSharedCheck_5847_ = !lean_is_exclusive(v___x_5822_);
if (v_isSharedCheck_5847_ == 0)
{
v___x_5842_ = v___x_5822_;
v_isShared_5843_ = v_isSharedCheck_5847_;
goto v_resetjp_5841_;
}
else
{
lean_inc(v_a_5840_);
lean_dec(v___x_5822_);
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
else
{
lean_dec(v_mod_x3f_5782_);
v___y_5792_ = v___y_5786_;
v___y_5793_ = v___y_5787_;
v___y_5794_ = v___y_5788_;
v___y_5795_ = v___y_5789_;
goto v___jp_5791_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___boxed(lean_object* v___x_5869_, lean_object* v___x_5870_, lean_object* v_mod_x3f_5871_, lean_object* v_id_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_){
_start:
{
uint8_t v___x_6806__boxed_5880_; uint8_t v___x_6807__boxed_5881_; lean_object* v_res_5882_; 
v___x_6806__boxed_5880_ = lean_unbox(v___x_5869_);
v___x_6807__boxed_5881_ = lean_unbox(v___x_5870_);
v_res_5882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0(v___x_6806__boxed_5880_, v___x_6807__boxed_5881_, v_mod_x3f_5871_, v_id_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_);
lean_dec(v___y_5878_);
lean_dec_ref(v___y_5877_);
lean_dec(v___y_5876_);
lean_dec_ref(v___y_5875_);
lean_dec(v___y_5874_);
lean_dec_ref(v___y_5873_);
return v_res_5882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(lean_object* v___x_5883_, uint8_t v___x_5884_, lean_object* v_keepIdentParam_5885_, lean_object* v_x_5886_, lean_object* v_mod_x3f_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_){
_start:
{
lean_object* v___x_5895_; lean_object* v_id_5896_; lean_object* v___x_5897_; uint8_t v___x_5898_; 
v___x_5895_ = lean_unsigned_to_nat(1u);
v_id_5896_ = l_Lean_Syntax_getArg(v___x_5883_, v___x_5895_);
v___x_5897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v_id_5896_);
v___x_5898_ = l_Lean_Syntax_isOfKind(v_id_5896_, v___x_5897_);
if (v___x_5898_ == 0)
{
lean_object* v___x_5899_; lean_object* v___x_5900_; 
lean_dec(v_id_5896_);
lean_dec(v_mod_x3f_5887_);
lean_dec_ref(v_keepIdentParam_5885_);
v___x_5899_ = lean_box(v___x_5884_);
v___x_5900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5899_);
return v___x_5900_;
}
else
{
lean_object* v___x_5901_; 
lean_inc(v___y_5893_);
lean_inc_ref(v___y_5892_);
lean_inc(v___y_5891_);
lean_inc_ref(v___y_5890_);
lean_inc(v___y_5889_);
lean_inc_ref(v___y_5888_);
v___x_5901_ = lean_apply_9(v_keepIdentParam_5885_, v_mod_x3f_5887_, v_id_5896_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_, lean_box(0));
return v___x_5901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2___boxed(lean_object* v___x_5902_, lean_object* v___x_5903_, lean_object* v_keepIdentParam_5904_, lean_object* v_x_5905_, lean_object* v_mod_x3f_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_){
_start:
{
uint8_t v___x_6999__boxed_5914_; lean_object* v_res_5915_; 
v___x_6999__boxed_5914_ = lean_unbox(v___x_5903_);
v_res_5915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(v___x_5902_, v___x_6999__boxed_5914_, v_keepIdentParam_5904_, v_x_5905_, v_mod_x3f_5906_, v___y_5907_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_);
lean_dec(v___y_5912_);
lean_dec_ref(v___y_5911_);
lean_dec(v___y_5910_);
lean_dec_ref(v___y_5909_);
lean_dec(v___y_5908_);
lean_dec_ref(v___y_5907_);
lean_dec(v___x_5902_);
return v_res_5915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(lean_object* v_as_5916_, size_t v_i_5917_, size_t v_stop_5918_, lean_object* v_b_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_){
_start:
{
lean_object* v_a_5928_; uint8_t v___x_5932_; 
v___x_5932_ = lean_usize_dec_eq(v_i_5917_, v_stop_5918_);
if (v___x_5932_ == 0)
{
lean_object* v___x_5933_; lean_object* v___y_5937_; lean_object* v___x_5948_; uint8_t v___x_5949_; 
v___x_5933_ = lean_array_uget_borrowed(v_as_5916_, v_i_5917_);
v___x_5948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v___x_5933_);
v___x_5949_ = l_Lean_Syntax_isOfKind(v___x_5933_, v___x_5948_);
if (v___x_5949_ == 0)
{
goto v___jp_5934_;
}
else
{
lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v_keepIdentParam_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; uint8_t v___x_5956_; 
v___x_5950_ = lean_box(v___x_5932_);
v___x_5951_ = lean_box(v___x_5949_);
v_keepIdentParam_5952_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___boxed), 11, 2);
lean_closure_set(v_keepIdentParam_5952_, 0, v___x_5950_);
lean_closure_set(v_keepIdentParam_5952_, 1, v___x_5951_);
v___x_5953_ = lean_unsigned_to_nat(0u);
v___x_5954_ = l_Lean_Syntax_getArg(v___x_5933_, v___x_5953_);
v___x_5955_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_5954_);
v___x_5956_ = l_Lean_Syntax_isOfKind(v___x_5954_, v___x_5955_);
if (v___x_5956_ == 0)
{
lean_object* v___x_5957_; uint8_t v___x_5958_; 
v___x_5957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_5954_);
v___x_5958_ = l_Lean_Syntax_isOfKind(v___x_5954_, v___x_5957_);
if (v___x_5958_ == 0)
{
lean_object* v___x_5959_; uint8_t v___x_5960_; 
lean_dec_ref(v_keepIdentParam_5952_);
v___x_5959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_5954_);
v___x_5960_ = l_Lean_Syntax_isOfKind(v___x_5954_, v___x_5959_);
if (v___x_5960_ == 0)
{
lean_object* v___x_5961_; uint8_t v___x_5962_; 
v___x_5961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_5954_);
v___x_5962_ = l_Lean_Syntax_isOfKind(v___x_5954_, v___x_5961_);
if (v___x_5962_ == 0)
{
lean_dec(v___x_5954_);
goto v___jp_5934_;
}
else
{
lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; uint8_t v___x_5966_; 
v___x_5963_ = lean_unsigned_to_nat(1u);
v___x_5964_ = l_Lean_Syntax_getArg(v___x_5954_, v___x_5963_);
lean_dec(v___x_5954_);
v___x_5965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13));
v___x_5966_ = l_Lean_Syntax_isOfKind(v___x_5964_, v___x_5965_);
if (v___x_5966_ == 0)
{
goto v___jp_5934_;
}
else
{
v_a_5928_ = v_b_5919_;
goto v___jp_5927_;
}
}
}
else
{
lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; uint8_t v___x_5970_; 
v___x_5967_ = lean_unsigned_to_nat(1u);
v___x_5968_ = l_Lean_Syntax_getArg(v___x_5954_, v___x_5967_);
lean_dec(v___x_5954_);
v___x_5969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
v___x_5970_ = l_Lean_Syntax_isOfKind(v___x_5968_, v___x_5969_);
if (v___x_5970_ == 0)
{
goto v___jp_5934_;
}
else
{
v_a_5928_ = v_b_5919_;
goto v___jp_5927_;
}
}
}
else
{
lean_object* v___x_5971_; lean_object* v___x_5972_; uint8_t v___x_5973_; 
v___x_5971_ = lean_unsigned_to_nat(1u);
v___x_5972_ = l_Lean_Syntax_getArg(v___x_5954_, v___x_5971_);
v___x_5973_ = l_Lean_Syntax_isNone(v___x_5972_);
if (v___x_5973_ == 0)
{
uint8_t v___x_5974_; 
lean_inc(v___x_5972_);
v___x_5974_ = l_Lean_Syntax_matchesNull(v___x_5972_, v___x_5971_);
if (v___x_5974_ == 0)
{
lean_dec(v___x_5972_);
lean_dec(v___x_5954_);
lean_dec_ref(v_keepIdentParam_5952_);
goto v___jp_5934_;
}
else
{
lean_object* v_mod_x3f_5975_; lean_object* v___x_5976_; uint8_t v___x_5977_; 
v_mod_x3f_5975_ = l_Lean_Syntax_getArg(v___x_5972_, v___x_5953_);
lean_dec(v___x_5972_);
v___x_5976_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v_mod_x3f_5975_);
v___x_5977_ = l_Lean_Syntax_isOfKind(v_mod_x3f_5975_, v___x_5976_);
if (v___x_5977_ == 0)
{
lean_dec(v_mod_x3f_5975_);
lean_dec(v___x_5954_);
lean_dec_ref(v_keepIdentParam_5952_);
goto v___jp_5934_;
}
else
{
lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; 
v___x_5978_ = lean_box(0);
v___x_5979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5979_, 0, v_mod_x3f_5975_);
v___x_5980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(v___x_5954_, v___x_5949_, v_keepIdentParam_5952_, v___x_5978_, v___x_5979_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
lean_dec(v___x_5954_);
v___y_5937_ = v___x_5980_;
goto v___jp_5936_;
}
}
}
else
{
lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; 
lean_dec(v___x_5972_);
v___x_5981_ = lean_box(0);
v___x_5982_ = lean_box(0);
v___x_5983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(v___x_5954_, v___x_5949_, v_keepIdentParam_5952_, v___x_5981_, v___x_5982_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
lean_dec(v___x_5954_);
v___y_5937_ = v___x_5983_;
goto v___jp_5936_;
}
}
}
else
{
lean_object* v___x_5984_; uint8_t v___x_5985_; 
v___x_5984_ = l_Lean_Syntax_getArg(v___x_5954_, v___x_5953_);
v___x_5985_ = l_Lean_Syntax_isNone(v___x_5984_);
if (v___x_5985_ == 0)
{
lean_object* v___x_5986_; uint8_t v___x_5987_; 
v___x_5986_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_5984_);
v___x_5987_ = l_Lean_Syntax_matchesNull(v___x_5984_, v___x_5986_);
if (v___x_5987_ == 0)
{
lean_dec(v___x_5984_);
lean_dec(v___x_5954_);
lean_dec_ref(v_keepIdentParam_5952_);
goto v___jp_5934_;
}
else
{
lean_object* v_mod_x3f_5988_; lean_object* v___x_5989_; uint8_t v___x_5990_; 
v_mod_x3f_5988_ = l_Lean_Syntax_getArg(v___x_5984_, v___x_5953_);
lean_dec(v___x_5984_);
v___x_5989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v_mod_x3f_5988_);
v___x_5990_ = l_Lean_Syntax_isOfKind(v_mod_x3f_5988_, v___x_5989_);
if (v___x_5990_ == 0)
{
lean_dec(v_mod_x3f_5988_);
lean_dec(v___x_5954_);
lean_dec_ref(v_keepIdentParam_5952_);
goto v___jp_5934_;
}
else
{
lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; 
v___x_5991_ = lean_box(0);
v___x_5992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5992_, 0, v_mod_x3f_5988_);
v___x_5993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(v___x_5954_, v___x_5949_, v_keepIdentParam_5952_, v___x_5991_, v___x_5992_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
lean_dec(v___x_5954_);
v___y_5937_ = v___x_5993_;
goto v___jp_5936_;
}
}
}
else
{
lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; 
lean_dec(v___x_5984_);
v___x_5994_ = lean_box(0);
v___x_5995_ = lean_box(0);
v___x_5996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(v___x_5954_, v___x_5949_, v_keepIdentParam_5952_, v___x_5994_, v___x_5995_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
lean_dec(v___x_5954_);
v___y_5937_ = v___x_5996_;
goto v___jp_5936_;
}
}
}
v___jp_5934_:
{
lean_object* v___x_5935_; 
lean_inc(v___x_5933_);
v___x_5935_ = lean_array_push(v_b_5919_, v___x_5933_);
v_a_5928_ = v___x_5935_;
goto v___jp_5927_;
}
v___jp_5936_:
{
if (lean_obj_tag(v___y_5937_) == 0)
{
lean_object* v_a_5938_; uint8_t v___x_5939_; 
v_a_5938_ = lean_ctor_get(v___y_5937_, 0);
lean_inc(v_a_5938_);
lean_dec_ref_known(v___y_5937_, 1);
v___x_5939_ = lean_unbox(v_a_5938_);
lean_dec(v_a_5938_);
if (v___x_5939_ == 0)
{
v_a_5928_ = v_b_5919_;
goto v___jp_5927_;
}
else
{
goto v___jp_5934_;
}
}
else
{
lean_object* v_a_5940_; lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_5947_; 
lean_dec_ref(v_b_5919_);
v_a_5940_ = lean_ctor_get(v___y_5937_, 0);
v_isSharedCheck_5947_ = !lean_is_exclusive(v___y_5937_);
if (v_isSharedCheck_5947_ == 0)
{
v___x_5942_ = v___y_5937_;
v_isShared_5943_ = v_isSharedCheck_5947_;
goto v_resetjp_5941_;
}
else
{
lean_inc(v_a_5940_);
lean_dec(v___y_5937_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_5947_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v___x_5945_; 
if (v_isShared_5943_ == 0)
{
v___x_5945_ = v___x_5942_;
goto v_reusejp_5944_;
}
else
{
lean_object* v_reuseFailAlloc_5946_; 
v_reuseFailAlloc_5946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5946_, 0, v_a_5940_);
v___x_5945_ = v_reuseFailAlloc_5946_;
goto v_reusejp_5944_;
}
v_reusejp_5944_:
{
return v___x_5945_;
}
}
}
}
}
else
{
lean_object* v___x_5997_; 
v___x_5997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5997_, 0, v_b_5919_);
return v___x_5997_;
}
v___jp_5927_:
{
size_t v___x_5929_; size_t v___x_5930_; 
v___x_5929_ = ((size_t)1ULL);
v___x_5930_ = lean_usize_add(v_i_5917_, v___x_5929_);
v_i_5917_ = v___x_5930_;
v_b_5919_ = v_a_5928_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___boxed(lean_object* v_as_5998_, lean_object* v_i_5999_, lean_object* v_stop_6000_, lean_object* v_b_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_){
_start:
{
size_t v_i_boxed_6009_; size_t v_stop_boxed_6010_; lean_object* v_res_6011_; 
v_i_boxed_6009_ = lean_unbox_usize(v_i_5999_);
lean_dec(v_i_5999_);
v_stop_boxed_6010_ = lean_unbox_usize(v_stop_6000_);
lean_dec(v_stop_6000_);
v_res_6011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(v_as_5998_, v_i_boxed_6009_, v_stop_boxed_6010_, v_b_6001_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_);
lean_dec(v___y_6007_);
lean_dec_ref(v___y_6006_);
lean_dec(v___y_6005_);
lean_dec_ref(v___y_6004_);
lean_dec(v___y_6003_);
lean_dec_ref(v___y_6002_);
lean_dec_ref(v_as_5998_);
return v_res_6011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_getPreservedParams(lean_object* v_params_6014_, lean_object* v_a_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_){
_start:
{
lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; uint8_t v___x_6025_; 
v___x_6022_ = lean_unsigned_to_nat(0u);
v___x_6023_ = lean_array_get_size(v_params_6014_);
v___x_6024_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_getPreservedParams___closed__0));
v___x_6025_ = lean_nat_dec_lt(v___x_6022_, v___x_6023_);
if (v___x_6025_ == 0)
{
lean_object* v___x_6026_; 
v___x_6026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6026_, 0, v___x_6024_);
return v___x_6026_;
}
else
{
size_t v___x_6027_; size_t v___x_6028_; lean_object* v___x_6029_; 
v___x_6027_ = ((size_t)0ULL);
v___x_6028_ = lean_usize_of_nat(v___x_6023_);
v___x_6029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(v_params_6014_, v___x_6027_, v___x_6028_, v___x_6024_, v_a_6015_, v_a_6016_, v_a_6017_, v_a_6018_, v_a_6019_, v_a_6020_);
return v___x_6029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_getPreservedParams___boxed(lean_object* v_params_6030_, lean_object* v_a_6031_, lean_object* v_a_6032_, lean_object* v_a_6033_, lean_object* v_a_6034_, lean_object* v_a_6035_, lean_object* v_a_6036_, lean_object* v_a_6037_){
_start:
{
lean_object* v_res_6038_; 
v_res_6038_ = l_Lean_Elab_Tactic_Grind_getPreservedParams(v_params_6030_, v_a_6031_, v_a_6032_, v_a_6033_, v_a_6034_, v_a_6035_, v_a_6036_);
lean_dec(v_a_6036_);
lean_dec_ref(v_a_6035_);
lean_dec(v_a_6034_);
lean_dec_ref(v_a_6033_);
lean_dec(v_a_6032_);
lean_dec_ref(v_a_6031_);
lean_dec_ref(v_params_6030_);
return v_res_6038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_6041_, lean_object* v_newThms_6042_, lean_object* v_gmt_6043_, lean_object* v_numInstances_6044_, lean_object* v_numDelayedInstances_6045_, lean_object* v_num_6046_, lean_object* v_preInstances_6047_, lean_object* v_nextThmIdx_6048_, lean_object* v_matchEqNames_6049_, lean_object* v_delayedThmInsts_6050_, lean_object* v_nextDeclIdx_6051_, lean_object* v_enodeMap_6052_, lean_object* v_exprs_6053_, lean_object* v_parents_6054_, lean_object* v_congrTable_6055_, lean_object* v_appMap_6056_, lean_object* v_indicesFound_6057_, lean_object* v_toProcess_6058_, lean_object* v_internalizing_6059_, uint8_t v_inconsistent_6060_, lean_object* v_nextIdx_6061_, lean_object* v_newRawFacts_6062_, lean_object* v_facts_6063_, lean_object* v_extThms_6064_, lean_object* v_inj_6065_, lean_object* v_split_6066_, lean_object* v_clean_6067_, lean_object* v_sstates_6068_, lean_object* v_goalStack_6069_, lean_object* v_mvarId_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_){
_start:
{
lean_object* v___x_6081_; 
v___x_6081_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_6041_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_);
if (lean_obj_tag(v___x_6081_) == 0)
{
lean_object* v_a_6082_; lean_object* v___x_6083_; 
v_a_6082_ = lean_ctor_get(v___x_6081_, 0);
lean_inc(v_a_6082_);
lean_dec_ref_known(v___x_6081_, 1);
v___x_6083_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_6042_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_);
if (lean_obj_tag(v___x_6083_) == 0)
{
lean_object* v_a_6084_; lean_object* v___x_6086_; uint8_t v_isShared_6087_; uint8_t v_isSharedCheck_6095_; 
v_a_6084_ = lean_ctor_get(v___x_6083_, 0);
v_isSharedCheck_6095_ = !lean_is_exclusive(v___x_6083_);
if (v_isSharedCheck_6095_ == 0)
{
v___x_6086_ = v___x_6083_;
v_isShared_6087_ = v_isSharedCheck_6095_;
goto v_resetjp_6085_;
}
else
{
lean_inc(v_a_6084_);
lean_dec(v___x_6083_);
v___x_6086_ = lean_box(0);
v_isShared_6087_ = v_isSharedCheck_6095_;
goto v_resetjp_6085_;
}
v_resetjp_6085_:
{
lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6093_; 
v___x_6088_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_6089_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6088_);
lean_ctor_set(v___x_6089_, 1, v_gmt_6043_);
lean_ctor_set(v___x_6089_, 2, v_a_6082_);
lean_ctor_set(v___x_6089_, 3, v_a_6084_);
lean_ctor_set(v___x_6089_, 4, v_numInstances_6044_);
lean_ctor_set(v___x_6089_, 5, v_numDelayedInstances_6045_);
lean_ctor_set(v___x_6089_, 6, v_num_6046_);
lean_ctor_set(v___x_6089_, 7, v_preInstances_6047_);
lean_ctor_set(v___x_6089_, 8, v_nextThmIdx_6048_);
lean_ctor_set(v___x_6089_, 9, v_matchEqNames_6049_);
lean_ctor_set(v___x_6089_, 10, v_delayedThmInsts_6050_);
v___x_6090_ = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(v___x_6090_, 0, v_nextDeclIdx_6051_);
lean_ctor_set(v___x_6090_, 1, v_enodeMap_6052_);
lean_ctor_set(v___x_6090_, 2, v_exprs_6053_);
lean_ctor_set(v___x_6090_, 3, v_parents_6054_);
lean_ctor_set(v___x_6090_, 4, v_congrTable_6055_);
lean_ctor_set(v___x_6090_, 5, v_appMap_6056_);
lean_ctor_set(v___x_6090_, 6, v_indicesFound_6057_);
lean_ctor_set(v___x_6090_, 7, v_toProcess_6058_);
lean_ctor_set(v___x_6090_, 8, v_internalizing_6059_);
lean_ctor_set(v___x_6090_, 9, v_nextIdx_6061_);
lean_ctor_set(v___x_6090_, 10, v_newRawFacts_6062_);
lean_ctor_set(v___x_6090_, 11, v_facts_6063_);
lean_ctor_set(v___x_6090_, 12, v_extThms_6064_);
lean_ctor_set(v___x_6090_, 13, v___x_6089_);
lean_ctor_set(v___x_6090_, 14, v_inj_6065_);
lean_ctor_set(v___x_6090_, 15, v_split_6066_);
lean_ctor_set(v___x_6090_, 16, v_clean_6067_);
lean_ctor_set(v___x_6090_, 17, v_sstates_6068_);
lean_ctor_set(v___x_6090_, 18, v_goalStack_6069_);
lean_ctor_set_uint8(v___x_6090_, sizeof(void*)*19, v_inconsistent_6060_);
v___x_6091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6090_);
lean_ctor_set(v___x_6091_, 1, v_mvarId_6070_);
if (v_isShared_6087_ == 0)
{
lean_ctor_set(v___x_6086_, 0, v___x_6091_);
v___x_6093_ = v___x_6086_;
goto v_reusejp_6092_;
}
else
{
lean_object* v_reuseFailAlloc_6094_; 
v_reuseFailAlloc_6094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6094_, 0, v___x_6091_);
v___x_6093_ = v_reuseFailAlloc_6094_;
goto v_reusejp_6092_;
}
v_reusejp_6092_:
{
return v___x_6093_;
}
}
}
else
{
lean_object* v_a_6096_; lean_object* v___x_6098_; uint8_t v_isShared_6099_; uint8_t v_isSharedCheck_6103_; 
lean_dec(v_a_6082_);
lean_dec(v_mvarId_6070_);
lean_dec_ref(v_goalStack_6069_);
lean_dec_ref(v_sstates_6068_);
lean_dec_ref(v_clean_6067_);
lean_dec_ref(v_split_6066_);
lean_dec_ref(v_inj_6065_);
lean_dec_ref(v_extThms_6064_);
lean_dec_ref(v_facts_6063_);
lean_dec_ref(v_newRawFacts_6062_);
lean_dec(v_nextIdx_6061_);
lean_dec_ref(v_internalizing_6059_);
lean_dec_ref(v_toProcess_6058_);
lean_dec_ref(v_indicesFound_6057_);
lean_dec_ref(v_appMap_6056_);
lean_dec_ref(v_congrTable_6055_);
lean_dec_ref(v_parents_6054_);
lean_dec_ref(v_exprs_6053_);
lean_dec_ref(v_enodeMap_6052_);
lean_dec(v_nextDeclIdx_6051_);
lean_dec_ref(v_delayedThmInsts_6050_);
lean_dec_ref(v_matchEqNames_6049_);
lean_dec(v_nextThmIdx_6048_);
lean_dec_ref(v_preInstances_6047_);
lean_dec(v_num_6046_);
lean_dec(v_numDelayedInstances_6045_);
lean_dec(v_numInstances_6044_);
lean_dec(v_gmt_6043_);
v_a_6096_ = lean_ctor_get(v___x_6083_, 0);
v_isSharedCheck_6103_ = !lean_is_exclusive(v___x_6083_);
if (v_isSharedCheck_6103_ == 0)
{
v___x_6098_ = v___x_6083_;
v_isShared_6099_ = v_isSharedCheck_6103_;
goto v_resetjp_6097_;
}
else
{
lean_inc(v_a_6096_);
lean_dec(v___x_6083_);
v___x_6098_ = lean_box(0);
v_isShared_6099_ = v_isSharedCheck_6103_;
goto v_resetjp_6097_;
}
v_resetjp_6097_:
{
lean_object* v___x_6101_; 
if (v_isShared_6099_ == 0)
{
v___x_6101_ = v___x_6098_;
goto v_reusejp_6100_;
}
else
{
lean_object* v_reuseFailAlloc_6102_; 
v_reuseFailAlloc_6102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6102_, 0, v_a_6096_);
v___x_6101_ = v_reuseFailAlloc_6102_;
goto v_reusejp_6100_;
}
v_reusejp_6100_:
{
return v___x_6101_;
}
}
}
}
else
{
lean_object* v_a_6104_; lean_object* v___x_6106_; uint8_t v_isShared_6107_; uint8_t v_isSharedCheck_6111_; 
lean_dec(v_mvarId_6070_);
lean_dec_ref(v_goalStack_6069_);
lean_dec_ref(v_sstates_6068_);
lean_dec_ref(v_clean_6067_);
lean_dec_ref(v_split_6066_);
lean_dec_ref(v_inj_6065_);
lean_dec_ref(v_extThms_6064_);
lean_dec_ref(v_facts_6063_);
lean_dec_ref(v_newRawFacts_6062_);
lean_dec(v_nextIdx_6061_);
lean_dec_ref(v_internalizing_6059_);
lean_dec_ref(v_toProcess_6058_);
lean_dec_ref(v_indicesFound_6057_);
lean_dec_ref(v_appMap_6056_);
lean_dec_ref(v_congrTable_6055_);
lean_dec_ref(v_parents_6054_);
lean_dec_ref(v_exprs_6053_);
lean_dec_ref(v_enodeMap_6052_);
lean_dec(v_nextDeclIdx_6051_);
lean_dec_ref(v_delayedThmInsts_6050_);
lean_dec_ref(v_matchEqNames_6049_);
lean_dec(v_nextThmIdx_6048_);
lean_dec_ref(v_preInstances_6047_);
lean_dec(v_num_6046_);
lean_dec(v_numDelayedInstances_6045_);
lean_dec(v_numInstances_6044_);
lean_dec(v_gmt_6043_);
v_a_6104_ = lean_ctor_get(v___x_6081_, 0);
v_isSharedCheck_6111_ = !lean_is_exclusive(v___x_6081_);
if (v_isSharedCheck_6111_ == 0)
{
v___x_6106_ = v___x_6081_;
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
else
{
lean_inc(v_a_6104_);
lean_dec(v___x_6081_);
v___x_6106_ = lean_box(0);
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
v_resetjp_6105_:
{
lean_object* v___x_6109_; 
if (v_isShared_6107_ == 0)
{
v___x_6109_ = v___x_6106_;
goto v_reusejp_6108_;
}
else
{
lean_object* v_reuseFailAlloc_6110_; 
v_reuseFailAlloc_6110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6110_, 0, v_a_6104_);
v___x_6109_ = v_reuseFailAlloc_6110_;
goto v_reusejp_6108_;
}
v_reusejp_6108_:
{
return v___x_6109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_6112_ = _args[0];
lean_object* v_newThms_6113_ = _args[1];
lean_object* v_gmt_6114_ = _args[2];
lean_object* v_numInstances_6115_ = _args[3];
lean_object* v_numDelayedInstances_6116_ = _args[4];
lean_object* v_num_6117_ = _args[5];
lean_object* v_preInstances_6118_ = _args[6];
lean_object* v_nextThmIdx_6119_ = _args[7];
lean_object* v_matchEqNames_6120_ = _args[8];
lean_object* v_delayedThmInsts_6121_ = _args[9];
lean_object* v_nextDeclIdx_6122_ = _args[10];
lean_object* v_enodeMap_6123_ = _args[11];
lean_object* v_exprs_6124_ = _args[12];
lean_object* v_parents_6125_ = _args[13];
lean_object* v_congrTable_6126_ = _args[14];
lean_object* v_appMap_6127_ = _args[15];
lean_object* v_indicesFound_6128_ = _args[16];
lean_object* v_toProcess_6129_ = _args[17];
lean_object* v_internalizing_6130_ = _args[18];
lean_object* v_inconsistent_6131_ = _args[19];
lean_object* v_nextIdx_6132_ = _args[20];
lean_object* v_newRawFacts_6133_ = _args[21];
lean_object* v_facts_6134_ = _args[22];
lean_object* v_extThms_6135_ = _args[23];
lean_object* v_inj_6136_ = _args[24];
lean_object* v_split_6137_ = _args[25];
lean_object* v_clean_6138_ = _args[26];
lean_object* v_sstates_6139_ = _args[27];
lean_object* v_goalStack_6140_ = _args[28];
lean_object* v_mvarId_6141_ = _args[29];
lean_object* v___y_6142_ = _args[30];
lean_object* v___y_6143_ = _args[31];
lean_object* v___y_6144_ = _args[32];
lean_object* v___y_6145_ = _args[33];
lean_object* v___y_6146_ = _args[34];
lean_object* v___y_6147_ = _args[35];
lean_object* v___y_6148_ = _args[36];
lean_object* v___y_6149_ = _args[37];
lean_object* v___y_6150_ = _args[38];
lean_object* v___y_6151_ = _args[39];
_start:
{
uint8_t v_inconsistent_boxed_6152_; lean_object* v_res_6153_; 
v_inconsistent_boxed_6152_ = lean_unbox(v_inconsistent_6131_);
v_res_6153_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_6112_, v_newThms_6113_, v_gmt_6114_, v_numInstances_6115_, v_numDelayedInstances_6116_, v_num_6117_, v_preInstances_6118_, v_nextThmIdx_6119_, v_matchEqNames_6120_, v_delayedThmInsts_6121_, v_nextDeclIdx_6122_, v_enodeMap_6123_, v_exprs_6124_, v_parents_6125_, v_congrTable_6126_, v_appMap_6127_, v_indicesFound_6128_, v_toProcess_6129_, v_internalizing_6130_, v_inconsistent_boxed_6152_, v_nextIdx_6132_, v_newRawFacts_6133_, v_facts_6134_, v_extThms_6135_, v_inj_6136_, v_split_6137_, v_clean_6138_, v_sstates_6139_, v_goalStack_6140_, v_mvarId_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_);
lean_dec(v___y_6150_);
lean_dec_ref(v___y_6149_);
lean_dec(v___y_6148_);
lean_dec_ref(v___y_6147_);
lean_dec(v___y_6146_);
lean_dec_ref(v___y_6145_);
lean_dec(v___y_6144_);
lean_dec_ref(v___y_6143_);
lean_dec(v___y_6142_);
lean_dec_ref(v_newThms_6113_);
lean_dec_ref(v_thms_6112_);
return v_res_6153_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_6154_; 
v___x_6154_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_6154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_6155_, size_t v_i_6156_, lean_object* v_bs_6157_){
_start:
{
uint8_t v___x_6158_; 
v___x_6158_ = lean_usize_dec_lt(v_i_6156_, v_sz_6155_);
if (v___x_6158_ == 0)
{
return v_bs_6157_;
}
else
{
lean_object* v_v_6159_; lean_object* v_casesTypes_6160_; lean_object* v_extThms_6161_; lean_object* v_funCC_6162_; lean_object* v_inj_6163_; lean_object* v___x_6165_; uint8_t v_isShared_6166_; uint8_t v_isSharedCheck_6177_; 
v_v_6159_ = lean_array_uget(v_bs_6157_, v_i_6156_);
v_casesTypes_6160_ = lean_ctor_get(v_v_6159_, 0);
v_extThms_6161_ = lean_ctor_get(v_v_6159_, 1);
v_funCC_6162_ = lean_ctor_get(v_v_6159_, 2);
v_inj_6163_ = lean_ctor_get(v_v_6159_, 4);
v_isSharedCheck_6177_ = !lean_is_exclusive(v_v_6159_);
if (v_isSharedCheck_6177_ == 0)
{
lean_object* v_unused_6178_; 
v_unused_6178_ = lean_ctor_get(v_v_6159_, 3);
lean_dec(v_unused_6178_);
v___x_6165_ = v_v_6159_;
v_isShared_6166_ = v_isSharedCheck_6177_;
goto v_resetjp_6164_;
}
else
{
lean_inc(v_inj_6163_);
lean_inc(v_funCC_6162_);
lean_inc(v_extThms_6161_);
lean_inc(v_casesTypes_6160_);
lean_dec(v_v_6159_);
v___x_6165_ = lean_box(0);
v_isShared_6166_ = v_isSharedCheck_6177_;
goto v_resetjp_6164_;
}
v_resetjp_6164_:
{
lean_object* v___x_6167_; lean_object* v_bs_x27_6168_; lean_object* v___x_6169_; lean_object* v___x_6171_; 
v___x_6167_ = lean_unsigned_to_nat(0u);
v_bs_x27_6168_ = lean_array_uset(v_bs_6157_, v_i_6156_, v___x_6167_);
v___x_6169_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_6166_ == 0)
{
lean_ctor_set(v___x_6165_, 3, v___x_6169_);
v___x_6171_ = v___x_6165_;
goto v_reusejp_6170_;
}
else
{
lean_object* v_reuseFailAlloc_6176_; 
v_reuseFailAlloc_6176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6176_, 0, v_casesTypes_6160_);
lean_ctor_set(v_reuseFailAlloc_6176_, 1, v_extThms_6161_);
lean_ctor_set(v_reuseFailAlloc_6176_, 2, v_funCC_6162_);
lean_ctor_set(v_reuseFailAlloc_6176_, 3, v___x_6169_);
lean_ctor_set(v_reuseFailAlloc_6176_, 4, v_inj_6163_);
v___x_6171_ = v_reuseFailAlloc_6176_;
goto v_reusejp_6170_;
}
v_reusejp_6170_:
{
size_t v___x_6172_; size_t v___x_6173_; lean_object* v___x_6174_; 
v___x_6172_ = ((size_t)1ULL);
v___x_6173_ = lean_usize_add(v_i_6156_, v___x_6172_);
v___x_6174_ = lean_array_uset(v_bs_x27_6168_, v_i_6156_, v___x_6171_);
v_i_6156_ = v___x_6173_;
v_bs_6157_ = v___x_6174_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_6179_, lean_object* v_i_6180_, lean_object* v_bs_6181_){
_start:
{
size_t v_sz_boxed_6182_; size_t v_i_boxed_6183_; lean_object* v_res_6184_; 
v_sz_boxed_6182_ = lean_unbox_usize(v_sz_6179_);
lean_dec(v_sz_6179_);
v_i_boxed_6183_ = lean_unbox_usize(v_i_6180_);
lean_dec(v_i_6180_);
v_res_6184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_6182_, v_i_boxed_6183_, v_bs_6181_);
return v_res_6184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_6185_, lean_object* v_ps_6186_, uint8_t v_only_6187_, lean_object* v_k_6188_, lean_object* v_a_6189_, lean_object* v_a_6190_, lean_object* v_a_6191_, lean_object* v_a_6192_, lean_object* v_a_6193_, lean_object* v_a_6194_, lean_object* v_a_6195_, lean_object* v_a_6196_){
_start:
{
lean_object* v___y_6199_; lean_object* v___y_6200_; lean_object* v___y_6201_; lean_object* v___y_6202_; lean_object* v___y_6203_; lean_object* v___y_6204_; lean_object* v___y_6205_; lean_object* v___y_6206_; lean_object* v___y_6207_; uint8_t v___y_6220_; uint8_t v___y_6221_; lean_object* v_params_6222_; lean_object* v___y_6223_; lean_object* v___y_6224_; lean_object* v___y_6225_; lean_object* v___y_6226_; lean_object* v___y_6227_; lean_object* v___y_6228_; lean_object* v___y_6229_; lean_object* v___y_6230_; uint8_t v___y_6337_; 
if (v_only_6187_ == 0)
{
lean_object* v___x_6360_; lean_object* v___x_6361_; uint8_t v___x_6362_; 
v___x_6360_ = lean_array_get_size(v_ps_6186_);
v___x_6361_ = lean_unsigned_to_nat(0u);
v___x_6362_ = lean_nat_dec_eq(v___x_6360_, v___x_6361_);
if (v___x_6362_ == 0)
{
v___y_6337_ = v___x_6362_;
goto v___jp_6336_;
}
else
{
lean_object* v___x_6363_; 
lean_dec_ref(v_params_6185_);
lean_inc(v_a_6196_);
lean_inc_ref(v_a_6195_);
lean_inc(v_a_6194_);
lean_inc_ref(v_a_6193_);
lean_inc(v_a_6192_);
lean_inc_ref(v_a_6191_);
lean_inc(v_a_6190_);
lean_inc_ref(v_a_6189_);
v___x_6363_ = lean_apply_9(v_k_6188_, v_a_6189_, v_a_6190_, v_a_6191_, v_a_6192_, v_a_6193_, v_a_6194_, v_a_6195_, v_a_6196_, lean_box(0));
return v___x_6363_;
}
}
else
{
uint8_t v___x_6364_; 
v___x_6364_ = 0;
v___y_6337_ = v___x_6364_;
goto v___jp_6336_;
}
v___jp_6198_:
{
lean_object* v___x_6208_; lean_object* v___x_6209_; 
v___x_6208_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_6208_, 0, v___y_6199_);
v___x_6209_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_6208_, v___y_6200_, v___y_6201_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_);
if (lean_obj_tag(v___x_6209_) == 0)
{
lean_object* v___x_6210_; 
lean_dec_ref_known(v___x_6209_, 1);
lean_inc(v___y_6207_);
lean_inc_ref(v___y_6206_);
lean_inc(v___y_6205_);
lean_inc_ref(v___y_6204_);
lean_inc(v___y_6203_);
lean_inc_ref(v___y_6202_);
lean_inc(v___y_6201_);
v___x_6210_ = lean_apply_9(v_k_6188_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, lean_box(0));
return v___x_6210_;
}
else
{
lean_object* v_a_6211_; lean_object* v___x_6213_; uint8_t v_isShared_6214_; uint8_t v_isSharedCheck_6218_; 
lean_dec_ref(v___y_6200_);
lean_dec_ref(v_k_6188_);
v_a_6211_ = lean_ctor_get(v___x_6209_, 0);
v_isSharedCheck_6218_ = !lean_is_exclusive(v___x_6209_);
if (v_isSharedCheck_6218_ == 0)
{
v___x_6213_ = v___x_6209_;
v_isShared_6214_ = v_isSharedCheck_6218_;
goto v_resetjp_6212_;
}
else
{
lean_inc(v_a_6211_);
lean_dec(v___x_6209_);
v___x_6213_ = lean_box(0);
v_isShared_6214_ = v_isSharedCheck_6218_;
goto v_resetjp_6212_;
}
v_resetjp_6212_:
{
lean_object* v___x_6216_; 
if (v_isShared_6214_ == 0)
{
v___x_6216_ = v___x_6213_;
goto v_reusejp_6215_;
}
else
{
lean_object* v_reuseFailAlloc_6217_; 
v_reuseFailAlloc_6217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6217_, 0, v_a_6211_);
v___x_6216_ = v_reuseFailAlloc_6217_;
goto v_reusejp_6215_;
}
v_reusejp_6215_:
{
return v___x_6216_;
}
}
}
}
v___jp_6219_:
{
lean_object* v___x_6231_; 
v___x_6231_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_6222_, v_ps_6186_, v_only_6187_, v___y_6221_, v___y_6220_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
if (lean_obj_tag(v___x_6231_) == 0)
{
lean_object* v_a_6232_; lean_object* v_ctx_6233_; lean_object* v_anchorRefs_x3f_6234_; lean_object* v_toContext_6235_; lean_object* v_sctx_6236_; lean_object* v_methods_6237_; uint8_t v_sym_6238_; lean_object* v_simp_6239_; lean_object* v_simpMethods_6240_; lean_object* v_symSimpMethods_6241_; lean_object* v_symDSimpMethods_6242_; lean_object* v_config_6243_; lean_object* v_identity_6244_; lean_object* v_activeSolvers_6245_; uint8_t v_cheapCases_6246_; uint8_t v_reportMVarIssue_6247_; lean_object* v_splitSource_6248_; lean_object* v_ematchDiagSource_6249_; lean_object* v_symPrios_6250_; lean_object* v_extensions_6251_; uint8_t v_debug_6252_; uint8_t v_ematchDiag_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; 
v_a_6232_ = lean_ctor_get(v___x_6231_, 0);
lean_inc_n(v_a_6232_, 2);
lean_dec_ref_known(v___x_6231_, 1);
v_ctx_6233_ = lean_ctor_get(v___y_6223_, 1);
v_anchorRefs_x3f_6234_ = lean_ctor_get(v_a_6232_, 9);
v_toContext_6235_ = lean_ctor_get(v___y_6223_, 0);
v_sctx_6236_ = lean_ctor_get(v___y_6223_, 2);
v_methods_6237_ = lean_ctor_get(v___y_6223_, 3);
v_sym_6238_ = lean_ctor_get_uint8(v___y_6223_, sizeof(void*)*5);
v_simp_6239_ = lean_ctor_get(v_ctx_6233_, 0);
v_simpMethods_6240_ = lean_ctor_get(v_ctx_6233_, 1);
v_symSimpMethods_6241_ = lean_ctor_get(v_ctx_6233_, 2);
v_symDSimpMethods_6242_ = lean_ctor_get(v_ctx_6233_, 3);
v_config_6243_ = lean_ctor_get(v_ctx_6233_, 4);
v_identity_6244_ = lean_ctor_get(v_ctx_6233_, 5);
v_activeSolvers_6245_ = lean_ctor_get(v_ctx_6233_, 6);
v_cheapCases_6246_ = lean_ctor_get_uint8(v_ctx_6233_, sizeof(void*)*12);
v_reportMVarIssue_6247_ = lean_ctor_get_uint8(v_ctx_6233_, sizeof(void*)*12 + 1);
v_splitSource_6248_ = lean_ctor_get(v_ctx_6233_, 8);
v_ematchDiagSource_6249_ = lean_ctor_get(v_ctx_6233_, 9);
v_symPrios_6250_ = lean_ctor_get(v_ctx_6233_, 10);
v_extensions_6251_ = lean_ctor_get(v_ctx_6233_, 11);
v_debug_6252_ = lean_ctor_get_uint8(v_ctx_6233_, sizeof(void*)*12 + 2);
v_ematchDiag_6253_ = lean_ctor_get_uint8(v_ctx_6233_, sizeof(void*)*12 + 3);
lean_inc_ref(v_extensions_6251_);
lean_inc_ref(v_symPrios_6250_);
lean_inc(v_ematchDiagSource_6249_);
lean_inc(v_splitSource_6248_);
lean_inc(v_anchorRefs_x3f_6234_);
lean_inc_ref(v_activeSolvers_6245_);
lean_inc(v_identity_6244_);
lean_inc_ref(v_config_6243_);
lean_inc_ref(v_symDSimpMethods_6242_);
lean_inc_ref(v_symSimpMethods_6241_);
lean_inc_ref(v_simpMethods_6240_);
lean_inc_ref(v_simp_6239_);
v___x_6254_ = lean_alloc_ctor(0, 12, 4);
lean_ctor_set(v___x_6254_, 0, v_simp_6239_);
lean_ctor_set(v___x_6254_, 1, v_simpMethods_6240_);
lean_ctor_set(v___x_6254_, 2, v_symSimpMethods_6241_);
lean_ctor_set(v___x_6254_, 3, v_symDSimpMethods_6242_);
lean_ctor_set(v___x_6254_, 4, v_config_6243_);
lean_ctor_set(v___x_6254_, 5, v_identity_6244_);
lean_ctor_set(v___x_6254_, 6, v_activeSolvers_6245_);
lean_ctor_set(v___x_6254_, 7, v_anchorRefs_x3f_6234_);
lean_ctor_set(v___x_6254_, 8, v_splitSource_6248_);
lean_ctor_set(v___x_6254_, 9, v_ematchDiagSource_6249_);
lean_ctor_set(v___x_6254_, 10, v_symPrios_6250_);
lean_ctor_set(v___x_6254_, 11, v_extensions_6251_);
lean_ctor_set_uint8(v___x_6254_, sizeof(void*)*12, v_cheapCases_6246_);
lean_ctor_set_uint8(v___x_6254_, sizeof(void*)*12 + 1, v_reportMVarIssue_6247_);
lean_ctor_set_uint8(v___x_6254_, sizeof(void*)*12 + 2, v_debug_6252_);
lean_ctor_set_uint8(v___x_6254_, sizeof(void*)*12 + 3, v_ematchDiag_6253_);
lean_inc_ref(v_methods_6237_);
lean_inc_ref(v_sctx_6236_);
lean_inc_ref(v_toContext_6235_);
v___x_6255_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_6255_, 0, v_toContext_6235_);
lean_ctor_set(v___x_6255_, 1, v___x_6254_);
lean_ctor_set(v___x_6255_, 2, v_sctx_6236_);
lean_ctor_set(v___x_6255_, 3, v_methods_6237_);
lean_ctor_set(v___x_6255_, 4, v_a_6232_);
lean_ctor_set_uint8(v___x_6255_, sizeof(void*)*5, v_sym_6238_);
if (v_only_6187_ == 0)
{
v___y_6199_ = v_a_6232_;
v___y_6200_ = v___x_6255_;
v___y_6201_ = v___y_6224_;
v___y_6202_ = v___y_6225_;
v___y_6203_ = v___y_6226_;
v___y_6204_ = v___y_6227_;
v___y_6205_ = v___y_6228_;
v___y_6206_ = v___y_6229_;
v___y_6207_ = v___y_6230_;
goto v___jp_6198_;
}
else
{
lean_object* v___x_6256_; 
v___x_6256_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_6224_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
if (lean_obj_tag(v___x_6256_) == 0)
{
lean_object* v_a_6257_; lean_object* v_toGoalState_6258_; lean_object* v_ematch_6259_; lean_object* v_mvarId_6260_; lean_object* v___x_6262_; uint8_t v_isShared_6263_; uint8_t v_isSharedCheck_6318_; 
v_a_6257_ = lean_ctor_get(v___x_6256_, 0);
lean_inc(v_a_6257_);
lean_dec_ref_known(v___x_6256_, 1);
v_toGoalState_6258_ = lean_ctor_get(v_a_6257_, 0);
lean_inc_ref(v_toGoalState_6258_);
v_ematch_6259_ = lean_ctor_get(v_toGoalState_6258_, 13);
lean_inc_ref(v_ematch_6259_);
v_mvarId_6260_ = lean_ctor_get(v_a_6257_, 1);
v_isSharedCheck_6318_ = !lean_is_exclusive(v_a_6257_);
if (v_isSharedCheck_6318_ == 0)
{
lean_object* v_unused_6319_; 
v_unused_6319_ = lean_ctor_get(v_a_6257_, 0);
lean_dec(v_unused_6319_);
v___x_6262_ = v_a_6257_;
v_isShared_6263_ = v_isSharedCheck_6318_;
goto v_resetjp_6261_;
}
else
{
lean_inc(v_mvarId_6260_);
lean_dec(v_a_6257_);
v___x_6262_ = lean_box(0);
v_isShared_6263_ = v_isSharedCheck_6318_;
goto v_resetjp_6261_;
}
v_resetjp_6261_:
{
lean_object* v_nextDeclIdx_6264_; lean_object* v_enodeMap_6265_; lean_object* v_exprs_6266_; lean_object* v_parents_6267_; lean_object* v_congrTable_6268_; lean_object* v_appMap_6269_; lean_object* v_indicesFound_6270_; lean_object* v_toProcess_6271_; lean_object* v_internalizing_6272_; uint8_t v_inconsistent_6273_; lean_object* v_nextIdx_6274_; lean_object* v_newRawFacts_6275_; lean_object* v_facts_6276_; lean_object* v_extThms_6277_; lean_object* v_inj_6278_; lean_object* v_split_6279_; lean_object* v_clean_6280_; lean_object* v_sstates_6281_; lean_object* v_goalStack_6282_; lean_object* v_gmt_6283_; lean_object* v_thms_6284_; lean_object* v_newThms_6285_; lean_object* v_numInstances_6286_; lean_object* v_numDelayedInstances_6287_; lean_object* v_num_6288_; lean_object* v_preInstances_6289_; lean_object* v_nextThmIdx_6290_; lean_object* v_matchEqNames_6291_; lean_object* v_delayedThmInsts_6292_; lean_object* v___x_6293_; lean_object* v___f_6294_; lean_object* v___x_6295_; 
v_nextDeclIdx_6264_ = lean_ctor_get(v_toGoalState_6258_, 0);
lean_inc(v_nextDeclIdx_6264_);
v_enodeMap_6265_ = lean_ctor_get(v_toGoalState_6258_, 1);
lean_inc_ref(v_enodeMap_6265_);
v_exprs_6266_ = lean_ctor_get(v_toGoalState_6258_, 2);
lean_inc_ref(v_exprs_6266_);
v_parents_6267_ = lean_ctor_get(v_toGoalState_6258_, 3);
lean_inc_ref(v_parents_6267_);
v_congrTable_6268_ = lean_ctor_get(v_toGoalState_6258_, 4);
lean_inc_ref(v_congrTable_6268_);
v_appMap_6269_ = lean_ctor_get(v_toGoalState_6258_, 5);
lean_inc_ref(v_appMap_6269_);
v_indicesFound_6270_ = lean_ctor_get(v_toGoalState_6258_, 6);
lean_inc_ref(v_indicesFound_6270_);
v_toProcess_6271_ = lean_ctor_get(v_toGoalState_6258_, 7);
lean_inc_ref(v_toProcess_6271_);
v_internalizing_6272_ = lean_ctor_get(v_toGoalState_6258_, 8);
lean_inc_ref(v_internalizing_6272_);
v_inconsistent_6273_ = lean_ctor_get_uint8(v_toGoalState_6258_, sizeof(void*)*19);
v_nextIdx_6274_ = lean_ctor_get(v_toGoalState_6258_, 9);
lean_inc(v_nextIdx_6274_);
v_newRawFacts_6275_ = lean_ctor_get(v_toGoalState_6258_, 10);
lean_inc_ref(v_newRawFacts_6275_);
v_facts_6276_ = lean_ctor_get(v_toGoalState_6258_, 11);
lean_inc_ref(v_facts_6276_);
v_extThms_6277_ = lean_ctor_get(v_toGoalState_6258_, 12);
lean_inc_ref(v_extThms_6277_);
v_inj_6278_ = lean_ctor_get(v_toGoalState_6258_, 14);
lean_inc_ref(v_inj_6278_);
v_split_6279_ = lean_ctor_get(v_toGoalState_6258_, 15);
lean_inc_ref(v_split_6279_);
v_clean_6280_ = lean_ctor_get(v_toGoalState_6258_, 16);
lean_inc_ref(v_clean_6280_);
v_sstates_6281_ = lean_ctor_get(v_toGoalState_6258_, 17);
lean_inc_ref(v_sstates_6281_);
v_goalStack_6282_ = lean_ctor_get(v_toGoalState_6258_, 18);
lean_inc_ref(v_goalStack_6282_);
lean_dec_ref(v_toGoalState_6258_);
v_gmt_6283_ = lean_ctor_get(v_ematch_6259_, 1);
lean_inc(v_gmt_6283_);
v_thms_6284_ = lean_ctor_get(v_ematch_6259_, 2);
lean_inc_ref(v_thms_6284_);
v_newThms_6285_ = lean_ctor_get(v_ematch_6259_, 3);
lean_inc_ref(v_newThms_6285_);
v_numInstances_6286_ = lean_ctor_get(v_ematch_6259_, 4);
lean_inc(v_numInstances_6286_);
v_numDelayedInstances_6287_ = lean_ctor_get(v_ematch_6259_, 5);
lean_inc(v_numDelayedInstances_6287_);
v_num_6288_ = lean_ctor_get(v_ematch_6259_, 6);
lean_inc(v_num_6288_);
v_preInstances_6289_ = lean_ctor_get(v_ematch_6259_, 7);
lean_inc_ref(v_preInstances_6289_);
v_nextThmIdx_6290_ = lean_ctor_get(v_ematch_6259_, 8);
lean_inc(v_nextThmIdx_6290_);
v_matchEqNames_6291_ = lean_ctor_get(v_ematch_6259_, 9);
lean_inc_ref(v_matchEqNames_6291_);
v_delayedThmInsts_6292_ = lean_ctor_get(v_ematch_6259_, 10);
lean_inc_ref(v_delayedThmInsts_6292_);
lean_dec_ref(v_ematch_6259_);
v___x_6293_ = lean_box(v_inconsistent_6273_);
v___f_6294_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 40, 30);
lean_closure_set(v___f_6294_, 0, v_thms_6284_);
lean_closure_set(v___f_6294_, 1, v_newThms_6285_);
lean_closure_set(v___f_6294_, 2, v_gmt_6283_);
lean_closure_set(v___f_6294_, 3, v_numInstances_6286_);
lean_closure_set(v___f_6294_, 4, v_numDelayedInstances_6287_);
lean_closure_set(v___f_6294_, 5, v_num_6288_);
lean_closure_set(v___f_6294_, 6, v_preInstances_6289_);
lean_closure_set(v___f_6294_, 7, v_nextThmIdx_6290_);
lean_closure_set(v___f_6294_, 8, v_matchEqNames_6291_);
lean_closure_set(v___f_6294_, 9, v_delayedThmInsts_6292_);
lean_closure_set(v___f_6294_, 10, v_nextDeclIdx_6264_);
lean_closure_set(v___f_6294_, 11, v_enodeMap_6265_);
lean_closure_set(v___f_6294_, 12, v_exprs_6266_);
lean_closure_set(v___f_6294_, 13, v_parents_6267_);
lean_closure_set(v___f_6294_, 14, v_congrTable_6268_);
lean_closure_set(v___f_6294_, 15, v_appMap_6269_);
lean_closure_set(v___f_6294_, 16, v_indicesFound_6270_);
lean_closure_set(v___f_6294_, 17, v_toProcess_6271_);
lean_closure_set(v___f_6294_, 18, v_internalizing_6272_);
lean_closure_set(v___f_6294_, 19, v___x_6293_);
lean_closure_set(v___f_6294_, 20, v_nextIdx_6274_);
lean_closure_set(v___f_6294_, 21, v_newRawFacts_6275_);
lean_closure_set(v___f_6294_, 22, v_facts_6276_);
lean_closure_set(v___f_6294_, 23, v_extThms_6277_);
lean_closure_set(v___f_6294_, 24, v_inj_6278_);
lean_closure_set(v___f_6294_, 25, v_split_6279_);
lean_closure_set(v___f_6294_, 26, v_clean_6280_);
lean_closure_set(v___f_6294_, 27, v_sstates_6281_);
lean_closure_set(v___f_6294_, 28, v_goalStack_6282_);
lean_closure_set(v___f_6294_, 29, v_mvarId_6260_);
v___x_6295_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_6294_, v___x_6255_, v___y_6224_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
if (lean_obj_tag(v___x_6295_) == 0)
{
lean_object* v_a_6296_; lean_object* v___x_6297_; lean_object* v___x_6299_; 
v_a_6296_ = lean_ctor_get(v___x_6295_, 0);
lean_inc(v_a_6296_);
lean_dec_ref_known(v___x_6295_, 1);
v___x_6297_ = lean_box(0);
if (v_isShared_6263_ == 0)
{
lean_ctor_set_tag(v___x_6262_, 1);
lean_ctor_set(v___x_6262_, 1, v___x_6297_);
lean_ctor_set(v___x_6262_, 0, v_a_6296_);
v___x_6299_ = v___x_6262_;
goto v_reusejp_6298_;
}
else
{
lean_object* v_reuseFailAlloc_6309_; 
v_reuseFailAlloc_6309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6309_, 0, v_a_6296_);
lean_ctor_set(v_reuseFailAlloc_6309_, 1, v___x_6297_);
v___x_6299_ = v_reuseFailAlloc_6309_;
goto v_reusejp_6298_;
}
v_reusejp_6298_:
{
lean_object* v___x_6300_; 
v___x_6300_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_6299_, v___y_6224_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
if (lean_obj_tag(v___x_6300_) == 0)
{
lean_dec_ref_known(v___x_6300_, 1);
v___y_6199_ = v_a_6232_;
v___y_6200_ = v___x_6255_;
v___y_6201_ = v___y_6224_;
v___y_6202_ = v___y_6225_;
v___y_6203_ = v___y_6226_;
v___y_6204_ = v___y_6227_;
v___y_6205_ = v___y_6228_;
v___y_6206_ = v___y_6229_;
v___y_6207_ = v___y_6230_;
goto v___jp_6198_;
}
else
{
lean_object* v_a_6301_; lean_object* v___x_6303_; uint8_t v_isShared_6304_; uint8_t v_isSharedCheck_6308_; 
lean_dec_ref_known(v___x_6255_, 5);
lean_dec(v_a_6232_);
lean_dec_ref(v_k_6188_);
v_a_6301_ = lean_ctor_get(v___x_6300_, 0);
v_isSharedCheck_6308_ = !lean_is_exclusive(v___x_6300_);
if (v_isSharedCheck_6308_ == 0)
{
v___x_6303_ = v___x_6300_;
v_isShared_6304_ = v_isSharedCheck_6308_;
goto v_resetjp_6302_;
}
else
{
lean_inc(v_a_6301_);
lean_dec(v___x_6300_);
v___x_6303_ = lean_box(0);
v_isShared_6304_ = v_isSharedCheck_6308_;
goto v_resetjp_6302_;
}
v_resetjp_6302_:
{
lean_object* v___x_6306_; 
if (v_isShared_6304_ == 0)
{
v___x_6306_ = v___x_6303_;
goto v_reusejp_6305_;
}
else
{
lean_object* v_reuseFailAlloc_6307_; 
v_reuseFailAlloc_6307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6307_, 0, v_a_6301_);
v___x_6306_ = v_reuseFailAlloc_6307_;
goto v_reusejp_6305_;
}
v_reusejp_6305_:
{
return v___x_6306_;
}
}
}
}
}
else
{
lean_object* v_a_6310_; lean_object* v___x_6312_; uint8_t v_isShared_6313_; uint8_t v_isSharedCheck_6317_; 
lean_del_object(v___x_6262_);
lean_dec_ref_known(v___x_6255_, 5);
lean_dec(v_a_6232_);
lean_dec_ref(v_k_6188_);
v_a_6310_ = lean_ctor_get(v___x_6295_, 0);
v_isSharedCheck_6317_ = !lean_is_exclusive(v___x_6295_);
if (v_isSharedCheck_6317_ == 0)
{
v___x_6312_ = v___x_6295_;
v_isShared_6313_ = v_isSharedCheck_6317_;
goto v_resetjp_6311_;
}
else
{
lean_inc(v_a_6310_);
lean_dec(v___x_6295_);
v___x_6312_ = lean_box(0);
v_isShared_6313_ = v_isSharedCheck_6317_;
goto v_resetjp_6311_;
}
v_resetjp_6311_:
{
lean_object* v___x_6315_; 
if (v_isShared_6313_ == 0)
{
v___x_6315_ = v___x_6312_;
goto v_reusejp_6314_;
}
else
{
lean_object* v_reuseFailAlloc_6316_; 
v_reuseFailAlloc_6316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6316_, 0, v_a_6310_);
v___x_6315_ = v_reuseFailAlloc_6316_;
goto v_reusejp_6314_;
}
v_reusejp_6314_:
{
return v___x_6315_;
}
}
}
}
}
else
{
lean_object* v_a_6320_; lean_object* v___x_6322_; uint8_t v_isShared_6323_; uint8_t v_isSharedCheck_6327_; 
lean_dec_ref_known(v___x_6255_, 5);
lean_dec(v_a_6232_);
lean_dec_ref(v_k_6188_);
v_a_6320_ = lean_ctor_get(v___x_6256_, 0);
v_isSharedCheck_6327_ = !lean_is_exclusive(v___x_6256_);
if (v_isSharedCheck_6327_ == 0)
{
v___x_6322_ = v___x_6256_;
v_isShared_6323_ = v_isSharedCheck_6327_;
goto v_resetjp_6321_;
}
else
{
lean_inc(v_a_6320_);
lean_dec(v___x_6256_);
v___x_6322_ = lean_box(0);
v_isShared_6323_ = v_isSharedCheck_6327_;
goto v_resetjp_6321_;
}
v_resetjp_6321_:
{
lean_object* v___x_6325_; 
if (v_isShared_6323_ == 0)
{
v___x_6325_ = v___x_6322_;
goto v_reusejp_6324_;
}
else
{
lean_object* v_reuseFailAlloc_6326_; 
v_reuseFailAlloc_6326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6326_, 0, v_a_6320_);
v___x_6325_ = v_reuseFailAlloc_6326_;
goto v_reusejp_6324_;
}
v_reusejp_6324_:
{
return v___x_6325_;
}
}
}
}
}
else
{
lean_object* v_a_6328_; lean_object* v___x_6330_; uint8_t v_isShared_6331_; uint8_t v_isSharedCheck_6335_; 
lean_dec_ref(v_k_6188_);
v_a_6328_ = lean_ctor_get(v___x_6231_, 0);
v_isSharedCheck_6335_ = !lean_is_exclusive(v___x_6231_);
if (v_isSharedCheck_6335_ == 0)
{
v___x_6330_ = v___x_6231_;
v_isShared_6331_ = v_isSharedCheck_6335_;
goto v_resetjp_6329_;
}
else
{
lean_inc(v_a_6328_);
lean_dec(v___x_6231_);
v___x_6330_ = lean_box(0);
v_isShared_6331_ = v_isSharedCheck_6335_;
goto v_resetjp_6329_;
}
v_resetjp_6329_:
{
lean_object* v___x_6333_; 
if (v_isShared_6331_ == 0)
{
v___x_6333_ = v___x_6330_;
goto v_reusejp_6332_;
}
else
{
lean_object* v_reuseFailAlloc_6334_; 
v_reuseFailAlloc_6334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6334_, 0, v_a_6328_);
v___x_6333_ = v_reuseFailAlloc_6334_;
goto v_reusejp_6332_;
}
v_reusejp_6332_:
{
return v___x_6333_;
}
}
}
}
v___jp_6336_:
{
uint8_t v___x_6338_; 
v___x_6338_ = 1;
if (v_only_6187_ == 0)
{
v___y_6220_ = v___x_6338_;
v___y_6221_ = v___y_6337_;
v_params_6222_ = v_params_6185_;
v___y_6223_ = v_a_6189_;
v___y_6224_ = v_a_6190_;
v___y_6225_ = v_a_6191_;
v___y_6226_ = v_a_6192_;
v___y_6227_ = v_a_6193_;
v___y_6228_ = v_a_6194_;
v___y_6229_ = v_a_6195_;
v___y_6230_ = v_a_6196_;
goto v___jp_6219_;
}
else
{
lean_object* v_config_6339_; lean_object* v_identity_6340_; lean_object* v_extensions_6341_; lean_object* v_extra_6342_; lean_object* v_extraInj_6343_; lean_object* v_extraFacts_6344_; lean_object* v_symPrios_6345_; lean_object* v_norm_6346_; lean_object* v_normProcs_6347_; lean_object* v___x_6349_; uint8_t v_isShared_6350_; uint8_t v_isSharedCheck_6358_; 
v_config_6339_ = lean_ctor_get(v_params_6185_, 0);
v_identity_6340_ = lean_ctor_get(v_params_6185_, 1);
v_extensions_6341_ = lean_ctor_get(v_params_6185_, 2);
v_extra_6342_ = lean_ctor_get(v_params_6185_, 3);
v_extraInj_6343_ = lean_ctor_get(v_params_6185_, 4);
v_extraFacts_6344_ = lean_ctor_get(v_params_6185_, 5);
v_symPrios_6345_ = lean_ctor_get(v_params_6185_, 6);
v_norm_6346_ = lean_ctor_get(v_params_6185_, 7);
v_normProcs_6347_ = lean_ctor_get(v_params_6185_, 8);
v_isSharedCheck_6358_ = !lean_is_exclusive(v_params_6185_);
if (v_isSharedCheck_6358_ == 0)
{
lean_object* v_unused_6359_; 
v_unused_6359_ = lean_ctor_get(v_params_6185_, 9);
lean_dec(v_unused_6359_);
v___x_6349_ = v_params_6185_;
v_isShared_6350_ = v_isSharedCheck_6358_;
goto v_resetjp_6348_;
}
else
{
lean_inc(v_normProcs_6347_);
lean_inc(v_norm_6346_);
lean_inc(v_symPrios_6345_);
lean_inc(v_extraFacts_6344_);
lean_inc(v_extraInj_6343_);
lean_inc(v_extra_6342_);
lean_inc(v_extensions_6341_);
lean_inc(v_identity_6340_);
lean_inc(v_config_6339_);
lean_dec(v_params_6185_);
v___x_6349_ = lean_box(0);
v_isShared_6350_ = v_isSharedCheck_6358_;
goto v_resetjp_6348_;
}
v_resetjp_6348_:
{
size_t v_sz_6351_; size_t v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v_params_6356_; 
v_sz_6351_ = lean_array_size(v_extensions_6341_);
v___x_6352_ = ((size_t)0ULL);
v___x_6353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_6351_, v___x_6352_, v_extensions_6341_);
v___x_6354_ = lean_box(0);
if (v_isShared_6350_ == 0)
{
lean_ctor_set(v___x_6349_, 9, v___x_6354_);
lean_ctor_set(v___x_6349_, 2, v___x_6353_);
v_params_6356_ = v___x_6349_;
goto v_reusejp_6355_;
}
else
{
lean_object* v_reuseFailAlloc_6357_; 
v_reuseFailAlloc_6357_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6357_, 0, v_config_6339_);
lean_ctor_set(v_reuseFailAlloc_6357_, 1, v_identity_6340_);
lean_ctor_set(v_reuseFailAlloc_6357_, 2, v___x_6353_);
lean_ctor_set(v_reuseFailAlloc_6357_, 3, v_extra_6342_);
lean_ctor_set(v_reuseFailAlloc_6357_, 4, v_extraInj_6343_);
lean_ctor_set(v_reuseFailAlloc_6357_, 5, v_extraFacts_6344_);
lean_ctor_set(v_reuseFailAlloc_6357_, 6, v_symPrios_6345_);
lean_ctor_set(v_reuseFailAlloc_6357_, 7, v_norm_6346_);
lean_ctor_set(v_reuseFailAlloc_6357_, 8, v_normProcs_6347_);
lean_ctor_set(v_reuseFailAlloc_6357_, 9, v___x_6354_);
v_params_6356_ = v_reuseFailAlloc_6357_;
goto v_reusejp_6355_;
}
v_reusejp_6355_:
{
v___y_6220_ = v___x_6338_;
v___y_6221_ = v___y_6337_;
v_params_6222_ = v_params_6356_;
v___y_6223_ = v_a_6189_;
v___y_6224_ = v_a_6190_;
v___y_6225_ = v_a_6191_;
v___y_6226_ = v_a_6192_;
v___y_6227_ = v_a_6193_;
v___y_6228_ = v_a_6194_;
v___y_6229_ = v_a_6195_;
v___y_6230_ = v_a_6196_;
goto v___jp_6219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_6365_, lean_object* v_ps_6366_, lean_object* v_only_6367_, lean_object* v_k_6368_, lean_object* v_a_6369_, lean_object* v_a_6370_, lean_object* v_a_6371_, lean_object* v_a_6372_, lean_object* v_a_6373_, lean_object* v_a_6374_, lean_object* v_a_6375_, lean_object* v_a_6376_, lean_object* v_a_6377_){
_start:
{
uint8_t v_only_boxed_6378_; lean_object* v_res_6379_; 
v_only_boxed_6378_ = lean_unbox(v_only_6367_);
v_res_6379_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_6365_, v_ps_6366_, v_only_boxed_6378_, v_k_6368_, v_a_6369_, v_a_6370_, v_a_6371_, v_a_6372_, v_a_6373_, v_a_6374_, v_a_6375_, v_a_6376_);
lean_dec(v_a_6376_);
lean_dec_ref(v_a_6375_);
lean_dec(v_a_6374_);
lean_dec_ref(v_a_6373_);
lean_dec(v_a_6372_);
lean_dec_ref(v_a_6371_);
lean_dec(v_a_6370_);
lean_dec_ref(v_a_6369_);
lean_dec_ref(v_ps_6366_);
return v_res_6379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_6380_, lean_object* v_params_6381_, lean_object* v_ps_6382_, uint8_t v_only_6383_, lean_object* v_k_6384_, lean_object* v_a_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_, lean_object* v_a_6388_, lean_object* v_a_6389_, lean_object* v_a_6390_, lean_object* v_a_6391_, lean_object* v_a_6392_){
_start:
{
lean_object* v___x_6394_; 
v___x_6394_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_6381_, v_ps_6382_, v_only_6383_, v_k_6384_, v_a_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_);
return v___x_6394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_6395_, lean_object* v_params_6396_, lean_object* v_ps_6397_, lean_object* v_only_6398_, lean_object* v_k_6399_, lean_object* v_a_6400_, lean_object* v_a_6401_, lean_object* v_a_6402_, lean_object* v_a_6403_, lean_object* v_a_6404_, lean_object* v_a_6405_, lean_object* v_a_6406_, lean_object* v_a_6407_, lean_object* v_a_6408_){
_start:
{
uint8_t v_only_boxed_6409_; lean_object* v_res_6410_; 
v_only_boxed_6409_ = lean_unbox(v_only_6398_);
v_res_6410_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_6395_, v_params_6396_, v_ps_6397_, v_only_boxed_6409_, v_k_6399_, v_a_6400_, v_a_6401_, v_a_6402_, v_a_6403_, v_a_6404_, v_a_6405_, v_a_6406_, v_a_6407_);
lean_dec(v_a_6407_);
lean_dec_ref(v_a_6406_);
lean_dec(v_a_6405_);
lean_dec_ref(v_a_6404_);
lean_dec(v_a_6403_);
lean_dec_ref(v_a_6402_);
lean_dec(v_a_6401_);
lean_dec_ref(v_a_6400_);
lean_dec_ref(v_ps_6397_);
return v_res_6410_;
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
