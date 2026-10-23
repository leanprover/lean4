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
uint8_t v___x_1649__boxed_324_; size_t v_i_boxed_325_; size_t v_stop_boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v___x_1649__boxed_324_ = lean_unbox(v___x_320_);
v_i_boxed_325_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_stop_boxed_326_ = lean_unbox_usize(v_stop_323_);
lean_dec(v_stop_323_);
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_319_, v___x_1649__boxed_324_, v_as_321_, v_i_boxed_325_, v_stop_boxed_326_);
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
uint8_t v___y_645_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v_toCold_652_; lean_object* v___y_653_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; uint8_t v___y_687_; uint8_t v___y_688_; lean_object* v___y_689_; lean_object* v___y_709_; lean_object* v___y_710_; uint8_t v___y_711_; lean_object* v___y_712_; uint8_t v___y_713_; uint8_t v___y_714_; lean_object* v___y_715_; uint8_t v___y_719_; uint8_t v___y_720_; uint8_t v___x_730_; uint8_t v___y_732_; uint8_t v___x_738_; 
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
lean_ctor_set(v___x_657_, 1, v___y_651_);
lean_inc_ref(v___y_648_);
lean_inc_ref(v___y_649_);
v___x_658_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_658_, 0, v___y_649_);
lean_ctor_set(v___x_658_, 1, v___y_646_);
lean_ctor_set(v___x_658_, 2, v___y_650_);
lean_ctor_set(v___x_658_, 3, v___y_648_);
lean_ctor_set(v___x_658_, 4, v___x_657_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*5, v___y_647_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*5 + 1, v___y_645_);
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
v_fileName_690_ = lean_ctor_get(v___y_684_, 0);
v_fileMap_691_ = lean_ctor_get(v___y_684_, 1);
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
v___x_698_ = l_Lean_FileMap_toPosition(v_fileMap_691_, v___y_685_);
lean_dec(v___y_685_);
v___x_699_ = l_Lean_FileMap_toPosition(v_fileMap_691_, v___y_689_);
lean_dec(v___y_689_);
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
v___x_701_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_688_ == 0)
{
lean_del_object(v___x_696_);
lean_dec_ref(v___y_683_);
v___y_645_ = v___y_686_;
v___y_646_ = v___x_698_;
v___y_647_ = v___y_687_;
v___y_648_ = v___x_701_;
v___y_649_ = v_fileName_690_;
v___y_650_ = v___x_700_;
v___y_651_ = v_a_694_;
v_toCold_652_ = v___y_682_;
v___y_653_ = v___y_642_;
goto v___jp_644_;
}
else
{
uint8_t v___x_702_; 
lean_inc(v_a_694_);
v___x_702_ = l_Lean_MessageData_hasTag(v___y_683_, v_a_694_);
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
v___y_645_ = v___y_686_;
v___y_646_ = v___x_698_;
v___y_647_ = v___y_687_;
v___y_648_ = v___x_701_;
v___y_649_ = v_fileName_690_;
v___y_650_ = v___x_700_;
v___y_651_ = v_a_694_;
v_toCold_652_ = v___y_682_;
v___y_653_ = v___y_642_;
goto v___jp_644_;
}
}
}
}
v___jp_708_:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Syntax_getTailPos_x3f(v___y_712_, v___y_714_);
lean_dec(v___y_712_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_inc(v___y_715_);
v___y_682_ = v___y_709_;
v___y_683_ = v___y_710_;
v___y_684_ = v___y_709_;
v___y_685_ = v___y_715_;
v___y_686_ = v___y_713_;
v___y_687_ = v___y_714_;
v___y_688_ = v___y_711_;
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
v___y_684_ = v___y_709_;
v___y_685_ = v___y_715_;
v___y_686_ = v___y_713_;
v___y_687_ = v___y_714_;
v___y_688_ = v___y_711_;
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
v___y_709_ = v_toCold_721_;
v___y_710_ = v___f_725_;
v___y_711_ = v_suppressElabErrors_723_;
v___y_712_ = v_ref_726_;
v___y_713_ = v___y_720_;
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
v___y_709_ = v_toCold_721_;
v___y_710_ = v___f_725_;
v___y_711_ = v_suppressElabErrors_723_;
v___y_712_ = v_ref_726_;
v___y_713_ = v___y_720_;
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
lean_inc_ref(v___x_1106_);
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
v___x_1115_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1106_, v_declHint_1097_);
lean_dec_ref(v___x_1106_);
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
lean_object* v_toCold_1197_; lean_object* v_currRecDepth_1198_; lean_object* v_ref_1199_; uint16_t v_optionFlags_1200_; uint8_t v_suppressElabErrors_1201_; uint8_t v_checkDeprecated_1202_; uint8_t v_isRecordingDeps_1203_; lean_object* v_ref_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_toCold_1197_ = lean_ctor_get(v___y_1194_, 0);
v_currRecDepth_1198_ = lean_ctor_get(v___y_1194_, 1);
v_ref_1199_ = lean_ctor_get(v___y_1194_, 2);
v_optionFlags_1200_ = lean_ctor_get_uint16(v___y_1194_, sizeof(void*)*3);
v_suppressElabErrors_1201_ = lean_ctor_get_uint8(v___y_1194_, sizeof(void*)*3 + 2);
v_checkDeprecated_1202_ = lean_ctor_get_uint8(v___y_1194_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1203_ = lean_ctor_get_uint8(v___y_1194_, sizeof(void*)*3 + 4);
v_ref_1204_ = l_Lean_replaceRef(v_ref_1190_, v_ref_1199_);
lean_inc(v_currRecDepth_1198_);
lean_inc_ref(v_toCold_1197_);
v___x_1205_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1205_, 0, v_toCold_1197_);
lean_ctor_set(v___x_1205_, 1, v_currRecDepth_1198_);
lean_ctor_set(v___x_1205_, 2, v_ref_1204_);
lean_ctor_set_uint16(v___x_1205_, sizeof(void*)*3, v_optionFlags_1200_);
lean_ctor_set_uint8(v___x_1205_, sizeof(void*)*3 + 2, v_suppressElabErrors_1201_);
lean_ctor_set_uint8(v___x_1205_, sizeof(void*)*3 + 3, v_checkDeprecated_1202_);
lean_ctor_set_uint8(v___x_1205_, sizeof(void*)*3 + 4, v_isRecordingDeps_1203_);
v___x_1206_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1191_, v___y_1192_, v___y_1193_, v___x_1205_, v___y_1195_);
lean_dec_ref_known(v___x_1205_, 3);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1207_, lean_object* v_msg_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1207_, v_msg_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v_ref_1207_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1215_, lean_object* v_msg_1216_, lean_object* v_declHint_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v_a_1224_; lean_object* v___x_1225_; 
v___x_1223_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1216_, v_declHint_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref(v___x_1223_);
v___x_1225_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1215_, v_a_1224_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1226_, lean_object* v_msg_1227_, lean_object* v_declHint_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1226_, v_msg_1227_, v_declHint_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v_ref_1226_);
return v_res_1234_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1237_ = l_Lean_stringToMessageData(v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1238_, lean_object* v_constName_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; uint8_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1245_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1246_ = 0;
lean_inc(v_constName_1239_);
v___x_1247_ = l_Lean_MessageData_ofConstName(v_constName_1239_, v___x_1246_);
v___x_1248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1245_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1238_, v___x_1250_, v_constName_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1252_, lean_object* v_constName_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1252_, v_constName_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v_ref_1252_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_constName_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_ref_1266_; lean_object* v___x_1267_; 
v_ref_1266_ = lean_ctor_get(v___y_1263_, 2);
v___x_1267_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1266_, v_constName_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* v_constName_1275_, uint8_t v_skipRealize_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; lean_object* v_env_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_st_ref_get(v___y_1280_);
v_env_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc_ref(v_env_1283_);
lean_dec(v___x_1282_);
lean_inc(v_constName_1275_);
v___x_1284_ = l_Lean_Environment_findAsync_x3f(v_env_1283_, v_constName_1275_, v_skipRealize_1276_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1275_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1285_;
}
else
{
lean_object* v_val_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_constName_1275_);
v_val_1286_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1284_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_val_1286_);
lean_dec(v___x_1284_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set_tag(v___x_1288_, 0);
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_val_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* v_constName_1294_, lean_object* v_skipRealize_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
uint8_t v_skipRealize_boxed_1301_; lean_object* v_res_1302_; 
v_skipRealize_boxed_1301_ = lean_unbox(v_skipRealize_1295_);
v_res_1302_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1294_, v_skipRealize_boxed_1301_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* v_declName_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; lean_object* v_env_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1306_ = lean_st_ref_get(v___y_1304_);
v_env_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc_ref(v_env_1307_);
lean_dec(v___x_1306_);
v___x_1308_ = l_Lean_getReducibilityStatusCore(v_env_1307_, v_declName_1303_);
v___x_1309_ = lean_box(v___x_1308_);
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_declName_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1311_, v___y_1312_);
lean_dec(v___y_1312_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* v_declName_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1337_; 
v___x_1321_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1315_, v___y_1319_);
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1337_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1337_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_unbox(v_a_1322_);
lean_dec(v_a_1322_);
if (v___x_1326_ == 0)
{
uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1327_ = 1;
v___x_1328_ = lean_box(v___x_1327_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1328_);
v___x_1330_ = v___x_1324_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
else
{
uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1332_ = 0;
v___x_1333_ = lean_box(v___x_1332_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1333_);
v___x_1335_ = v___x_1324_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* v_declName_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
return v_res_1344_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
v___x_1347_ = l_Lean_stringToMessageData(v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
v___x_1350_ = l_Lean_stringToMessageData(v___x_1349_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
v___x_1353_ = l_Lean_stringToMessageData(v___x_1352_);
return v___x_1353_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* v_params_1360_, lean_object* v_id_1361_, lean_object* v_declName_1362_, lean_object* v_kind_1363_, uint8_t v_minIndexable_1364_, uint8_t v_suggest_1365_, uint8_t v_warn_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v___y_1373_; lean_object* v_thm_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; uint8_t v___x_1428_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___x_1625_; 
v___x_1428_ = 0;
lean_inc(v_declName_1362_);
v___x_1625_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1362_, v___x_1428_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; uint8_t v_kind_1627_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v_kind_1627_ = lean_ctor_get_uint8(v_a_1626_, sizeof(void*)*3);
lean_dec(v_a_1626_);
switch(v_kind_1627_)
{
case 1:
{
v___y_1556_ = v_a_1367_;
v___y_1557_ = v_a_1368_;
v___y_1558_ = v_a_1369_;
v___y_1559_ = v_a_1370_;
goto v___jp_1555_;
}
case 2:
{
v___y_1556_ = v_a_1367_;
v___y_1557_ = v_a_1368_;
v___y_1558_ = v_a_1369_;
v___y_1559_ = v_a_1370_;
goto v___jp_1555_;
}
case 6:
{
v___y_1556_ = v_a_1367_;
v___y_1557_ = v_a_1368_;
v___y_1558_ = v_a_1369_;
v___y_1559_ = v_a_1370_;
goto v___jp_1555_;
}
case 0:
{
lean_object* v___x_1628_; 
lean_dec(v_id_1361_);
lean_inc(v_declName_1362_);
v___x_1628_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1362_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; uint8_t v___x_1630_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1630_ = lean_unbox(v_a_1629_);
lean_dec(v_a_1629_);
if (v___x_1630_ == 0)
{
v___y_1486_ = v_a_1367_;
v___y_1487_ = v_a_1368_;
v___y_1488_ = v_a_1369_;
v___y_1489_ = v_a_1370_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_kind_1363_);
lean_dec_ref(v_params_1360_);
v___x_1631_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1632_ = l_Lean_MessageData_ofConstName(v_declName_1362_, v___x_1428_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1635_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
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
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v_kind_1363_);
lean_dec(v_declName_1362_);
lean_dec_ref(v_params_1360_);
v_a_1645_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1628_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1628_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
default: 
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_dec(v_kind_1363_);
lean_dec(v_id_1361_);
lean_dec_ref(v_params_1360_);
v___x_1653_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1654_ = l_Lean_MessageData_ofConstName(v_declName_1362_, v___x_1428_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1657_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
return v___x_1658_;
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_kind_1363_);
lean_dec(v_declName_1362_);
lean_dec(v_id_1361_);
lean_dec_ref(v_params_1360_);
v_a_1659_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1625_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1625_);
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
v___jp_1372_:
{
lean_object* v_config_1374_; lean_object* v_extensions_1375_; lean_object* v_extra_1376_; lean_object* v_extraInj_1377_; lean_object* v_extraFacts_1378_; lean_object* v_symPrios_1379_; lean_object* v_norm_1380_; lean_object* v_normProcs_1381_; lean_object* v_anchorRefs_x3f_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1391_; 
v_config_1374_ = lean_ctor_get(v_params_1360_, 0);
v_extensions_1375_ = lean_ctor_get(v_params_1360_, 1);
v_extra_1376_ = lean_ctor_get(v_params_1360_, 2);
v_extraInj_1377_ = lean_ctor_get(v_params_1360_, 3);
v_extraFacts_1378_ = lean_ctor_get(v_params_1360_, 4);
v_symPrios_1379_ = lean_ctor_get(v_params_1360_, 5);
v_norm_1380_ = lean_ctor_get(v_params_1360_, 6);
v_normProcs_1381_ = lean_ctor_get(v_params_1360_, 7);
v_anchorRefs_x3f_1382_ = lean_ctor_get(v_params_1360_, 8);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_params_1360_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1384_ = v_params_1360_;
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_anchorRefs_x3f_1382_);
lean_inc(v_normProcs_1381_);
lean_inc(v_norm_1380_);
lean_inc(v_symPrios_1379_);
lean_inc(v_extraFacts_1378_);
lean_inc(v_extraInj_1377_);
lean_inc(v_extra_1376_);
lean_inc(v_extensions_1375_);
lean_inc(v_config_1374_);
lean_dec(v_params_1360_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1386_ = l_Lean_PersistentArray_push___redArg(v_extra_1376_, v___y_1373_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 2, v___x_1386_);
v___x_1388_ = v___x_1384_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_config_1374_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_extensions_1375_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_extraInj_1377_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_extraFacts_1378_);
lean_ctor_set(v_reuseFailAlloc_1390_, 5, v_symPrios_1379_);
lean_ctor_set(v_reuseFailAlloc_1390_, 6, v_norm_1380_);
lean_ctor_set(v_reuseFailAlloc_1390_, 7, v_normProcs_1381_);
lean_ctor_set(v_reuseFailAlloc_1390_, 8, v_anchorRefs_x3f_1382_);
v___x_1388_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
}
v___jp_1392_:
{
if (v_warn_1366_ == 0)
{
lean_dec(v_declName_1362_);
v___y_1373_ = v_thm_1393_;
goto v___jp_1372_;
}
else
{
lean_object* v_extensions_1398_; lean_object* v_patterns_1399_; lean_object* v_origin_1400_; lean_object* v_cnstrs_1401_; uint8_t v___x_1402_; 
v_extensions_1398_ = lean_ctor_get(v_params_1360_, 1);
v_patterns_1399_ = lean_ctor_get(v_thm_1393_, 3);
v_origin_1400_ = lean_ctor_get(v_thm_1393_, 5);
v_cnstrs_1401_ = lean_ctor_get(v_thm_1393_, 7);
v___x_1402_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1398_, v_origin_1400_, v_patterns_1399_, v_cnstrs_1401_);
if (v___x_1402_ == 0)
{
lean_dec(v_declName_1362_);
v___y_1373_ = v_thm_1393_;
goto v___jp_1372_;
}
else
{
lean_object* v___x_1403_; 
v___x_1403_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1398_, v_declName_1362_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_dec_ref_known(v___x_1403_, 1);
v___y_1373_ = v_thm_1393_;
goto v___jp_1372_;
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v_thm_1393_);
lean_dec_ref(v_params_1360_);
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
}
v___jp_1412_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1424_ = l_Lean_PersistentArray_push___redArg(v___y_1421_, v___y_1416_);
v___x_1425_ = l_Lean_PersistentArray_push___redArg(v___x_1424_, v___y_1419_);
v___x_1426_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1426_, 0, v___y_1413_);
lean_ctor_set(v___x_1426_, 1, v___y_1418_);
lean_ctor_set(v___x_1426_, 2, v___x_1425_);
lean_ctor_set(v___x_1426_, 3, v___y_1420_);
lean_ctor_set(v___x_1426_, 4, v___y_1422_);
lean_ctor_set(v___x_1426_, 5, v___y_1415_);
lean_ctor_set(v___x_1426_, 6, v___y_1414_);
lean_ctor_set(v___x_1426_, 7, v___y_1417_);
lean_ctor_set(v___x_1426_, 8, v___y_1423_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
v___jp_1429_:
{
lean_object* v___x_1434_; 
v___x_1434_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1364_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v___x_1435_; 
lean_dec_ref_known(v___x_1434_, 1);
lean_inc(v_declName_1362_);
v___x_1435_ = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(v_declName_1362_, v___x_1428_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1468_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1468_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1468_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
if (lean_obj_tag(v_a_1436_) == 1)
{
lean_object* v_val_1440_; lean_object* v_config_1441_; lean_object* v_extensions_1442_; lean_object* v_extra_1443_; lean_object* v_extraInj_1444_; lean_object* v_extraFacts_1445_; lean_object* v_symPrios_1446_; lean_object* v_norm_1447_; lean_object* v_normProcs_1448_; lean_object* v_anchorRefs_x3f_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_declName_1362_);
v_val_1440_ = lean_ctor_get(v_a_1436_, 0);
lean_inc(v_val_1440_);
lean_dec_ref_known(v_a_1436_, 1);
v_config_1441_ = lean_ctor_get(v_params_1360_, 0);
v_extensions_1442_ = lean_ctor_get(v_params_1360_, 1);
v_extra_1443_ = lean_ctor_get(v_params_1360_, 2);
v_extraInj_1444_ = lean_ctor_get(v_params_1360_, 3);
v_extraFacts_1445_ = lean_ctor_get(v_params_1360_, 4);
v_symPrios_1446_ = lean_ctor_get(v_params_1360_, 5);
v_norm_1447_ = lean_ctor_get(v_params_1360_, 6);
v_normProcs_1448_ = lean_ctor_get(v_params_1360_, 7);
v_anchorRefs_x3f_1449_ = lean_ctor_get(v_params_1360_, 8);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_params_1360_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1451_ = v_params_1360_;
v_isShared_1452_ = v_isSharedCheck_1461_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_anchorRefs_x3f_1449_);
lean_inc(v_normProcs_1448_);
lean_inc(v_norm_1447_);
lean_inc(v_symPrios_1446_);
lean_inc(v_extraFacts_1445_);
lean_inc(v_extraInj_1444_);
lean_inc(v_extra_1443_);
lean_inc(v_extensions_1442_);
lean_inc(v_config_1441_);
lean_dec(v_params_1360_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1461_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1453_ = l_Lean_Array_toPArray_x27___redArg(v_val_1440_);
lean_dec(v_val_1440_);
v___x_1454_ = l_Lean_PersistentArray_append___redArg(v_extra_1443_, v___x_1453_);
lean_dec_ref(v___x_1453_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 2, v___x_1454_);
v___x_1456_ = v___x_1451_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_config_1441_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_extensions_1442_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_extraInj_1444_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v_extraFacts_1445_);
lean_ctor_set(v_reuseFailAlloc_1460_, 5, v_symPrios_1446_);
lean_ctor_set(v_reuseFailAlloc_1460_, 6, v_norm_1447_);
lean_ctor_set(v_reuseFailAlloc_1460_, 7, v_normProcs_1448_);
lean_ctor_set(v_reuseFailAlloc_1460_, 8, v_anchorRefs_x3f_1449_);
v___x_1456_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1458_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1456_);
v___x_1458_ = v___x_1438_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_del_object(v___x_1438_);
lean_dec(v_a_1436_);
lean_dec_ref(v_params_1360_);
v___x_1462_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__1, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
v___x_1463_ = l_Lean_MessageData_ofConstName(v_declName_1362_, v___x_1428_);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1466_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v___x_1467_;
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_declName_1362_);
lean_dec_ref(v_params_1360_);
v_a_1469_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1435_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1435_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec(v_declName_1362_);
lean_dec_ref(v_params_1360_);
v_a_1477_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1434_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1434_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
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
v___jp_1485_:
{
uint8_t v___x_1490_; 
v___x_1490_ = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(v_kind_1363_);
if (v___x_1490_ == 0)
{
uint8_t v___x_1491_; 
v___x_1491_ = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(v_kind_1363_);
lean_dec(v_kind_1363_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec_ref(v_params_1360_);
v___x_1492_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1493_ = l_Lean_MessageData_ofConstName(v_declName_1362_, v___x_1428_);
v___x_1494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__5, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1496_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
else
{
v___y_1430_ = v___y_1486_;
v___y_1431_ = v___y_1487_;
v___y_1432_ = v___y_1488_;
v___y_1433_ = v___y_1489_;
goto v___jp_1429_;
}
}
else
{
lean_dec(v_kind_1363_);
v___y_1430_ = v___y_1486_;
v___y_1431_ = v___y_1487_;
v___y_1432_ = v___y_1488_;
v___y_1433_ = v___y_1489_;
goto v___jp_1429_;
}
}
v___jp_1506_:
{
lean_object* v_symPrios_1511_; lean_object* v___x_1512_; 
v_symPrios_1511_ = lean_ctor_get(v_params_1360_, 5);
lean_inc_ref(v_symPrios_1511_);
lean_inc(v_declName_1362_);
v___x_1512_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1362_, v_kind_1363_, v_symPrios_1511_, v___x_1428_, v_minIndexable_1364_, v___y_1509_, v___y_1508_, v___y_1507_, v___y_1510_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v_thm_1393_ = v_a_1513_;
v___y_1394_ = v___y_1509_;
v___y_1395_ = v___y_1508_;
v___y_1396_ = v___y_1507_;
v___y_1397_ = v___y_1510_;
goto v___jp_1392_;
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v_declName_1362_);
lean_dec_ref(v_params_1360_);
v_a_1514_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1512_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1512_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
v___jp_1522_:
{
if (v_suggest_1365_ == 0)
{
lean_dec(v_id_1361_);
v___y_1507_ = v___y_1525_;
v___y_1508_ = v___y_1524_;
v___y_1509_ = v___y_1523_;
v___y_1510_ = v___y_1526_;
goto v___jp_1506_;
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1527_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1525_);
v___x_1528_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1529_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_1527_, v___x_1528_);
lean_dec_ref(v___x_1527_);
if (v___x_1529_ == 0)
{
lean_object* v_symPrios_1530_; lean_object* v___x_1531_; 
lean_dec(v_kind_1363_);
v_symPrios_1530_ = lean_ctor_get(v_params_1360_, 5);
lean_inc_ref(v_symPrios_1530_);
lean_inc(v_declName_1362_);
v___x_1531_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1361_, v_declName_1362_, v_symPrios_1530_, v_minIndexable_1364_, v_suggest_1365_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v_thm_1393_ = v_a_1532_;
v___y_1394_ = v___y_1523_;
v___y_1395_ = v___y_1524_;
v___y_1396_ = v___y_1525_;
v___y_1397_ = v___y_1526_;
goto v___jp_1392_;
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_declName_1362_);
lean_dec_ref(v_params_1360_);
v_a_1533_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1531_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1531_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_dec(v_id_1361_);
v___y_1507_ = v___y_1525_;
v___y_1508_ = v___y_1524_;
v___y_1509_ = v___y_1523_;
v___y_1510_ = v___y_1526_;
goto v___jp_1506_;
}
}
}
v___jp_1541_:
{
lean_object* v___x_1546_; 
v___x_1546_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1364_, v___y_1542_, v___y_1545_, v___y_1544_, v___y_1543_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_dec_ref_known(v___x_1546_, 1);
v___y_1523_ = v___y_1542_;
v___y_1524_ = v___y_1545_;
v___y_1525_ = v___y_1544_;
v___y_1526_ = v___y_1543_;
goto v___jp_1522_;
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_kind_1363_);
lean_dec(v_declName_1362_);
lean_dec(v_id_1361_);
lean_dec_ref(v_params_1360_);
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
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
v___jp_1555_:
{
if (lean_obj_tag(v_kind_1363_) == 2)
{
uint8_t v_gen_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1624_; 
lean_dec(v_id_1361_);
v_gen_1560_ = lean_ctor_get_uint8(v_kind_1363_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_kind_1363_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1562_ = v_kind_1363_;
v_isShared_1563_ = v_isSharedCheck_1624_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v_kind_1363_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1624_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; 
v___x_1564_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1364_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_config_1565_; lean_object* v_extensions_1566_; lean_object* v_extra_1567_; lean_object* v_extraInj_1568_; lean_object* v_extraFacts_1569_; lean_object* v_symPrios_1570_; lean_object* v_norm_1571_; lean_object* v_normProcs_1572_; lean_object* v_anchorRefs_x3f_1573_; lean_object* v___x_1575_; 
lean_dec_ref_known(v___x_1564_, 1);
v_config_1565_ = lean_ctor_get(v_params_1360_, 0);
lean_inc_ref(v_config_1565_);
v_extensions_1566_ = lean_ctor_get(v_params_1360_, 1);
lean_inc_ref(v_extensions_1566_);
v_extra_1567_ = lean_ctor_get(v_params_1360_, 2);
lean_inc_ref(v_extra_1567_);
v_extraInj_1568_ = lean_ctor_get(v_params_1360_, 3);
lean_inc_ref(v_extraInj_1568_);
v_extraFacts_1569_ = lean_ctor_get(v_params_1360_, 4);
lean_inc_ref(v_extraFacts_1569_);
v_symPrios_1570_ = lean_ctor_get(v_params_1360_, 5);
lean_inc_ref(v_symPrios_1570_);
v_norm_1571_ = lean_ctor_get(v_params_1360_, 6);
lean_inc_ref(v_norm_1571_);
v_normProcs_1572_ = lean_ctor_get(v_params_1360_, 7);
lean_inc_ref(v_normProcs_1572_);
v_anchorRefs_x3f_1573_ = lean_ctor_get(v_params_1360_, 8);
lean_inc(v_anchorRefs_x3f_1573_);
lean_dec_ref(v_params_1360_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set_tag(v___x_1562_, 0);
v___x_1575_ = v___x_1562_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, 0, v_gen_1560_);
v___x_1575_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; 
lean_inc_ref(v_symPrios_1570_);
lean_inc(v_declName_1362_);
v___x_1576_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1362_, v___x_1575_, v_symPrios_1570_, v___x_1428_, v___x_1428_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v___x_1578_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1578_, 0, v_gen_1560_);
lean_inc_ref(v_symPrios_1570_);
lean_inc(v_declName_1362_);
v___x_1579_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1362_, v___x_1578_, v_symPrios_1570_, v___x_1428_, v___x_1428_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1579_) == 0)
{
if (v_warn_1366_ == 0)
{
lean_object* v_a_1580_; 
lean_dec(v_declName_1362_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___y_1413_ = v_config_1565_;
v___y_1414_ = v_norm_1571_;
v___y_1415_ = v_symPrios_1570_;
v___y_1416_ = v_a_1577_;
v___y_1417_ = v_normProcs_1572_;
v___y_1418_ = v_extensions_1566_;
v___y_1419_ = v_a_1580_;
v___y_1420_ = v_extraInj_1568_;
v___y_1421_ = v_extra_1567_;
v___y_1422_ = v_extraFacts_1569_;
v___y_1423_ = v_anchorRefs_x3f_1573_;
goto v___jp_1412_;
}
else
{
lean_object* v_a_1581_; lean_object* v_patterns_1582_; lean_object* v_origin_1583_; lean_object* v_cnstrs_1584_; uint8_t v___x_1585_; 
v_a_1581_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1579_, 1);
v_patterns_1582_ = lean_ctor_get(v_a_1577_, 3);
v_origin_1583_ = lean_ctor_get(v_a_1577_, 5);
v_cnstrs_1584_ = lean_ctor_get(v_a_1577_, 7);
v___x_1585_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1566_, v_origin_1583_, v_patterns_1582_, v_cnstrs_1584_);
if (v___x_1585_ == 0)
{
lean_dec(v_declName_1362_);
v___y_1413_ = v_config_1565_;
v___y_1414_ = v_norm_1571_;
v___y_1415_ = v_symPrios_1570_;
v___y_1416_ = v_a_1577_;
v___y_1417_ = v_normProcs_1572_;
v___y_1418_ = v_extensions_1566_;
v___y_1419_ = v_a_1581_;
v___y_1420_ = v_extraInj_1568_;
v___y_1421_ = v_extra_1567_;
v___y_1422_ = v_extraFacts_1569_;
v___y_1423_ = v_anchorRefs_x3f_1573_;
goto v___jp_1412_;
}
else
{
lean_object* v_patterns_1586_; lean_object* v_origin_1587_; lean_object* v_cnstrs_1588_; uint8_t v___x_1589_; 
v_patterns_1586_ = lean_ctor_get(v_a_1581_, 3);
v_origin_1587_ = lean_ctor_get(v_a_1581_, 5);
v_cnstrs_1588_ = lean_ctor_get(v_a_1581_, 7);
v___x_1589_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1566_, v_origin_1587_, v_patterns_1586_, v_cnstrs_1588_);
if (v___x_1589_ == 0)
{
lean_dec(v_declName_1362_);
v___y_1413_ = v_config_1565_;
v___y_1414_ = v_norm_1571_;
v___y_1415_ = v_symPrios_1570_;
v___y_1416_ = v_a_1577_;
v___y_1417_ = v_normProcs_1572_;
v___y_1418_ = v_extensions_1566_;
v___y_1419_ = v_a_1581_;
v___y_1420_ = v_extraInj_1568_;
v___y_1421_ = v_extra_1567_;
v___y_1422_ = v_extraFacts_1569_;
v___y_1423_ = v_anchorRefs_x3f_1573_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1566_, v_declName_1362_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_dec_ref_known(v___x_1590_, 1);
v___y_1413_ = v_config_1565_;
v___y_1414_ = v_norm_1571_;
v___y_1415_ = v_symPrios_1570_;
v___y_1416_ = v_a_1577_;
v___y_1417_ = v_normProcs_1572_;
v___y_1418_ = v_extensions_1566_;
v___y_1419_ = v_a_1581_;
v___y_1420_ = v_extraInj_1568_;
v___y_1421_ = v_extra_1567_;
v___y_1422_ = v_extraFacts_1569_;
v___y_1423_ = v_anchorRefs_x3f_1573_;
goto v___jp_1412_;
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_a_1581_);
lean_dec(v_a_1577_);
lean_dec(v_anchorRefs_x3f_1573_);
lean_dec_ref(v_normProcs_1572_);
lean_dec_ref(v_norm_1571_);
lean_dec_ref(v_symPrios_1570_);
lean_dec_ref(v_extraFacts_1569_);
lean_dec_ref(v_extraInj_1568_);
lean_dec_ref(v_extra_1567_);
lean_dec_ref(v_extensions_1566_);
lean_dec_ref(v_config_1565_);
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_a_1577_);
lean_dec(v_anchorRefs_x3f_1573_);
lean_dec_ref(v_normProcs_1572_);
lean_dec_ref(v_norm_1571_);
lean_dec_ref(v_symPrios_1570_);
lean_dec_ref(v_extraFacts_1569_);
lean_dec_ref(v_extraInj_1568_);
lean_dec_ref(v_extra_1567_);
lean_dec_ref(v_extensions_1566_);
lean_dec_ref(v_config_1565_);
lean_dec(v_declName_1362_);
v_a_1599_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1579_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1579_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v_anchorRefs_x3f_1573_);
lean_dec_ref(v_normProcs_1572_);
lean_dec_ref(v_norm_1571_);
lean_dec_ref(v_symPrios_1570_);
lean_dec_ref(v_extraFacts_1569_);
lean_dec_ref(v_extraInj_1568_);
lean_dec_ref(v_extra_1567_);
lean_dec_ref(v_extensions_1566_);
lean_dec_ref(v_config_1565_);
lean_dec(v_declName_1362_);
v_a_1607_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1576_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1576_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_del_object(v___x_1562_);
lean_dec(v_declName_1362_);
lean_dec_ref(v_params_1360_);
v_a_1616_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1564_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1564_);
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
else
{
switch(lean_obj_tag(v_kind_1363_))
{
case 0:
{
v___y_1542_ = v___y_1556_;
v___y_1543_ = v___y_1559_;
v___y_1544_ = v___y_1558_;
v___y_1545_ = v___y_1557_;
goto v___jp_1541_;
}
case 1:
{
v___y_1542_ = v___y_1556_;
v___y_1543_ = v___y_1559_;
v___y_1544_ = v___y_1558_;
v___y_1545_ = v___y_1557_;
goto v___jp_1541_;
}
default: 
{
v___y_1523_ = v___y_1556_;
v___y_1524_ = v___y_1557_;
v___y_1525_ = v___y_1558_;
v___y_1526_ = v___y_1559_;
goto v___jp_1522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object* v_params_1667_, lean_object* v_id_1668_, lean_object* v_declName_1669_, lean_object* v_kind_1670_, lean_object* v_minIndexable_1671_, lean_object* v_suggest_1672_, lean_object* v_warn_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
uint8_t v_minIndexable_boxed_1679_; uint8_t v_suggest_boxed_1680_; uint8_t v_warn_boxed_1681_; lean_object* v_res_1682_; 
v_minIndexable_boxed_1679_ = lean_unbox(v_minIndexable_1671_);
v_suggest_boxed_1680_ = lean_unbox(v_suggest_1672_);
v_warn_boxed_1681_ = lean_unbox(v_warn_1673_);
v_res_1682_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_1667_, v_id_1668_, v_declName_1669_, v_kind_1670_, v_minIndexable_boxed_1679_, v_suggest_boxed_1680_, v_warn_boxed_1681_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object* v_declName_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1683_, v___y_1687_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object* v_declName_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(v_declName_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_1697_, lean_object* v_constName_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1705_, lean_object* v_constName_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(v_00_u03b1_1705_, v_constName_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1713_, lean_object* v_ref_1714_, lean_object* v_constName_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1714_, v_constName_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_ref_1723_, lean_object* v_constName_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(v_00_u03b1_1722_, v_ref_1723_, v_constName_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v_ref_1723_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1731_, lean_object* v_ref_1732_, lean_object* v_msg_1733_, lean_object* v_declHint_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1732_, v_msg_1733_, v_declHint_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1741_, lean_object* v_ref_1742_, lean_object* v_msg_1743_, lean_object* v_declHint_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1741_, v_ref_1742_, v_msg_1743_, v_declHint_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v_ref_1742_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1751_, lean_object* v_declHint_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1751_, v_declHint_1752_, v___y_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1759_, lean_object* v_declHint_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1759_, v_declHint_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1767_, lean_object* v_ref_1768_, lean_object* v_msg_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1768_, v_msg_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1776_, lean_object* v_ref_1777_, lean_object* v_msg_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1776_, v_ref_1777_, v_msg_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v_ref_1777_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(lean_object* v_declName_1789_, lean_object* v_symPrios_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
uint8_t v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = 0;
lean_inc(v_declName_1789_);
v___x_1797_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1789_, v___x_1796_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1870_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1870_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1870_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
uint8_t v_kind_1867_; 
v_kind_1867_ = lean_ctor_get_uint8(v_a_1798_, sizeof(void*)*3);
switch(v_kind_1867_)
{
case 1:
{
goto v___jp_1802_;
}
case 2:
{
goto v___jp_1802_;
}
case 6:
{
goto v___jp_1802_;
}
default: 
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_del_object(v___x_1800_);
lean_dec(v_a_1798_);
lean_dec_ref(v_symPrios_1790_);
lean_dec(v_declName_1789_);
v___x_1868_ = lean_box(v___x_1796_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
}
v___jp_1802_:
{
lean_object* v___x_1803_; lean_object* v_levelParams_1804_; lean_object* v_type_1805_; uint8_t v___x_1806_; 
v___x_1803_ = l_Lean_AsyncConstantInfo_toConstantVal(v_a_1798_);
v_levelParams_1804_ = lean_ctor_get(v___x_1803_, 1);
lean_inc(v_levelParams_1804_);
v_type_1805_ = lean_ctor_get(v___x_1803_, 2);
lean_inc_ref(v_type_1805_);
lean_dec_ref(v___x_1803_);
v___x_1806_ = l_List_isEmpty___redArg(v_levelParams_1804_);
lean_dec(v_levelParams_1804_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1809_; 
lean_dec_ref(v_type_1805_);
lean_dec_ref(v_symPrios_1790_);
lean_dec(v_declName_1789_);
v___x_1807_ = lean_box(v___x_1796_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1807_);
v___x_1809_ = v___x_1800_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
else
{
lean_object* v___x_1811_; 
lean_del_object(v___x_1800_);
lean_inc_ref(v_type_1805_);
v___x_1811_ = l_Lean_Meta_whnfR(v_type_1805_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1858_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1858_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1858_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
uint8_t v___x_1816_; 
v___x_1816_ = l_Lean_Expr_isForall(v_a_1812_);
lean_dec(v_a_1812_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; 
lean_del_object(v___x_1814_);
v___x_1817_ = l_Lean_Meta_isProp(v_type_1805_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1853_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1853_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1853_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
uint8_t v___x_1822_; 
v___x_1822_ = lean_unbox(v_a_1818_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
lean_dec(v_a_1818_);
lean_dec_ref(v_symPrios_1790_);
lean_dec(v_declName_1789_);
v___x_1823_ = lean_box(v___x_1796_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1823_);
v___x_1825_ = v___x_1820_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_del_object(v___x_1820_);
lean_inc(v_declName_1789_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v_declName_1789_);
v___x_1828_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__0));
v___x_1829_ = lean_box(0);
v___x_1830_ = l_Lean_mkConst(v_declName_1789_, v___x_1829_);
v___x_1831_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v___x_1832_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_1827_, v___x_1828_, v___x_1830_, v___x_1831_, v_symPrios_1790_, v___x_1806_, v___x_1796_, v___x_1796_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1844_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1844_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1844_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
if (lean_obj_tag(v_a_1833_) == 0)
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v_a_1818_);
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1818_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
lean_dec_ref_known(v_a_1833_, 1);
lean_dec(v_a_1818_);
v___x_1840_ = lean_box(v___x_1816_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1840_);
v___x_1842_ = v___x_1835_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v_a_1818_);
v_a_1845_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1832_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1832_);
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
else
{
lean_dec_ref(v_symPrios_1790_);
lean_dec(v_declName_1789_);
return v___x_1817_;
}
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_dec_ref(v_type_1805_);
lean_dec_ref(v_symPrios_1790_);
lean_dec(v_declName_1789_);
v___x_1854_ = lean_box(v___x_1796_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1854_);
v___x_1856_ = v___x_1814_;
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
lean_dec_ref(v_type_1805_);
lean_dec_ref(v_symPrios_1790_);
lean_dec(v_declName_1789_);
v_a_1859_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1811_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1811_);
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
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v_symPrios_1790_);
lean_dec(v_declName_1789_);
v_a_1871_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1797_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1797_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___boxed(lean_object* v_declName_1879_, lean_object* v_symPrios_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(v_declName_1879_, v_symPrios_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(lean_object* v_params_1887_, lean_object* v_declName_1888_, uint8_t v_minIndexable_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1921_; 
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; 
v_unused_1922_ = lean_ctor_get(v___x_1895_, 0);
lean_dec(v_unused_1922_);
v___x_1897_ = v___x_1895_;
v_isShared_1898_ = v_isSharedCheck_1921_;
goto v_resetjp_1896_;
}
else
{
lean_dec(v___x_1895_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1921_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v_config_1899_; lean_object* v_extensions_1900_; lean_object* v_extra_1901_; lean_object* v_extraInj_1902_; lean_object* v_extraFacts_1903_; lean_object* v_symPrios_1904_; lean_object* v_norm_1905_; lean_object* v_normProcs_1906_; lean_object* v_anchorRefs_x3f_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1920_; 
v_config_1899_ = lean_ctor_get(v_params_1887_, 0);
v_extensions_1900_ = lean_ctor_get(v_params_1887_, 1);
v_extra_1901_ = lean_ctor_get(v_params_1887_, 2);
v_extraInj_1902_ = lean_ctor_get(v_params_1887_, 3);
v_extraFacts_1903_ = lean_ctor_get(v_params_1887_, 4);
v_symPrios_1904_ = lean_ctor_get(v_params_1887_, 5);
v_norm_1905_ = lean_ctor_get(v_params_1887_, 6);
v_normProcs_1906_ = lean_ctor_get(v_params_1887_, 7);
v_anchorRefs_x3f_1907_ = lean_ctor_get(v_params_1887_, 8);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_params_1887_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1909_ = v_params_1887_;
v_isShared_1910_ = v_isSharedCheck_1920_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_anchorRefs_x3f_1907_);
lean_inc(v_normProcs_1906_);
lean_inc(v_norm_1905_);
lean_inc(v_symPrios_1904_);
lean_inc(v_extraFacts_1903_);
lean_inc(v_extraInj_1902_);
lean_inc(v_extra_1901_);
lean_inc(v_extensions_1900_);
lean_inc(v_config_1899_);
lean_dec(v_params_1887_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1920_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1911_ = lean_box(0);
v___x_1912_ = l_Lean_mkConst(v_declName_1888_, v___x_1911_);
v___x_1913_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_1903_, v___x_1912_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 4, v___x_1913_);
v___x_1915_ = v___x_1909_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_config_1899_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_extensions_1900_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_extra_1901_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_extraInj_1902_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1919_, 5, v_symPrios_1904_);
lean_ctor_set(v_reuseFailAlloc_1919_, 6, v_norm_1905_);
lean_ctor_set(v_reuseFailAlloc_1919_, 7, v_normProcs_1906_);
lean_ctor_set(v_reuseFailAlloc_1919_, 8, v_anchorRefs_x3f_1907_);
v___x_1915_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; 
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1915_);
v___x_1917_ = v___x_1897_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec(v_declName_1888_);
lean_dec_ref(v_params_1887_);
v_a_1923_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1895_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1895_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact___boxed(lean_object* v_params_1931_, lean_object* v_declName_1932_, lean_object* v_minIndexable_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
uint8_t v_minIndexable_boxed_1939_; lean_object* v_res_1940_; 
v_minIndexable_boxed_1939_ = lean_unbox(v_minIndexable_1933_);
v_res_1940_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(v_params_1931_, v_declName_1932_, v_minIndexable_boxed_1939_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1943_, lean_object* v_val_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_config_1948_; lean_object* v_extensions_1949_; lean_object* v_extra_1950_; lean_object* v_extraInj_1951_; lean_object* v_extraFacts_1952_; lean_object* v_symPrios_1953_; lean_object* v_norm_1954_; lean_object* v_normProcs_1955_; lean_object* v_anchorRefs_x3f_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1986_; 
v_config_1948_ = lean_ctor_get(v_params_1943_, 0);
v_extensions_1949_ = lean_ctor_get(v_params_1943_, 1);
v_extra_1950_ = lean_ctor_get(v_params_1943_, 2);
v_extraInj_1951_ = lean_ctor_get(v_params_1943_, 3);
v_extraFacts_1952_ = lean_ctor_get(v_params_1943_, 4);
v_symPrios_1953_ = lean_ctor_get(v_params_1943_, 5);
v_norm_1954_ = lean_ctor_get(v_params_1943_, 6);
v_normProcs_1955_ = lean_ctor_get(v_params_1943_, 7);
v_anchorRefs_x3f_1956_ = lean_ctor_get(v_params_1943_, 8);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_params_1943_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1958_ = v_params_1943_;
v_isShared_1959_ = v_isSharedCheck_1986_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_anchorRefs_x3f_1956_);
lean_inc(v_normProcs_1955_);
lean_inc(v_norm_1954_);
lean_inc(v_symPrios_1953_);
lean_inc(v_extraFacts_1952_);
lean_inc(v_extraInj_1951_);
lean_inc(v_extra_1950_);
lean_inc(v_extensions_1949_);
lean_inc(v_config_1948_);
lean_dec(v_params_1943_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1986_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___y_1961_; 
if (lean_obj_tag(v_anchorRefs_x3f_1956_) == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_1961_ = v___x_1984_;
goto v___jp_1960_;
}
else
{
lean_object* v_val_1985_; 
v_val_1985_ = lean_ctor_get(v_anchorRefs_x3f_1956_, 0);
lean_inc(v_val_1985_);
lean_dec_ref_known(v_anchorRefs_x3f_1956_, 1);
v___y_1961_ = v_val_1985_;
goto v___jp_1960_;
}
v___jp_1960_:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1944_, v_a_1945_, v_a_1946_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1975_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1975_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1975_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1967_ = lean_array_push(v___y_1961_, v_a_1963_);
v___x_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 8, v___x_1968_);
v___x_1970_ = v___x_1958_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_config_1948_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_extensions_1949_);
lean_ctor_set(v_reuseFailAlloc_1974_, 2, v_extra_1950_);
lean_ctor_set(v_reuseFailAlloc_1974_, 3, v_extraInj_1951_);
lean_ctor_set(v_reuseFailAlloc_1974_, 4, v_extraFacts_1952_);
lean_ctor_set(v_reuseFailAlloc_1974_, 5, v_symPrios_1953_);
lean_ctor_set(v_reuseFailAlloc_1974_, 6, v_norm_1954_);
lean_ctor_set(v_reuseFailAlloc_1974_, 7, v_normProcs_1955_);
lean_ctor_set(v_reuseFailAlloc_1974_, 8, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1972_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1970_);
v___x_1972_ = v___x_1965_;
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
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec_ref(v___y_1961_);
lean_del_object(v___x_1958_);
lean_dec_ref(v_normProcs_1955_);
lean_dec_ref(v_norm_1954_);
lean_dec_ref(v_symPrios_1953_);
lean_dec_ref(v_extraFacts_1952_);
lean_dec_ref(v_extraInj_1951_);
lean_dec_ref(v_extra_1950_);
lean_dec_ref(v_extensions_1949_);
lean_dec_ref(v_config_1948_);
v_a_1976_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1962_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1962_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_1987_, lean_object* v_val_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_1987_, v_val_1988_, v_a_1989_, v_a_1990_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_val_1988_);
return v_res_1992_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_1995_ = l_Lean_stringToMessageData(v___x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v_config_2000_; uint8_t v_revert_2001_; 
v_config_2000_ = lean_ctor_get(v_params_1996_, 0);
v_revert_2001_ = lean_ctor_get_uint8(v_config_2000_, sizeof(void*)*17 + 31);
if (v_revert_2001_ == 0)
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_box(0);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
return v___x_2003_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_2005_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_2004_, v_a_1997_, v_a_1998_);
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2006_, v_a_2007_, v_a_2008_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_params_2006_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_2011_, lean_object* v___y_2012_){
_start:
{
uint8_t v___x_2014_; 
v___x_2014_ = l_Lean_Expr_hasMVar(v_e_2011_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_e_2011_);
return v___x_2015_;
}
else
{
lean_object* v___x_2016_; lean_object* v_mctx_2017_; lean_object* v___x_2018_; lean_object* v_fst_2019_; lean_object* v_snd_2020_; lean_object* v___x_2021_; lean_object* v_cache_2022_; lean_object* v_zetaDeltaFVarIds_2023_; lean_object* v_postponed_2024_; lean_object* v_diag_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2034_; 
v___x_2016_ = lean_st_ref_get(v___y_2012_);
v_mctx_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc_ref(v_mctx_2017_);
lean_dec(v___x_2016_);
v___x_2018_ = l_Lean_instantiateMVarsCore(v_mctx_2017_, v_e_2011_);
v_fst_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_fst_2019_);
v_snd_2020_ = lean_ctor_get(v___x_2018_, 1);
lean_inc(v_snd_2020_);
lean_dec_ref(v___x_2018_);
v___x_2021_ = lean_st_ref_take(v___y_2012_);
v_cache_2022_ = lean_ctor_get(v___x_2021_, 1);
v_zetaDeltaFVarIds_2023_ = lean_ctor_get(v___x_2021_, 2);
v_postponed_2024_ = lean_ctor_get(v___x_2021_, 3);
v_diag_2025_ = lean_ctor_get(v___x_2021_, 4);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; 
v_unused_2035_ = lean_ctor_get(v___x_2021_, 0);
lean_dec(v_unused_2035_);
v___x_2027_ = v___x_2021_;
v_isShared_2028_ = v_isSharedCheck_2034_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_diag_2025_);
lean_inc(v_postponed_2024_);
lean_inc(v_zetaDeltaFVarIds_2023_);
lean_inc(v_cache_2022_);
lean_dec(v___x_2021_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2034_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v_snd_2020_);
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_snd_2020_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_cache_2022_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_zetaDeltaFVarIds_2023_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v_postponed_2024_);
lean_ctor_set(v_reuseFailAlloc_2033_, 4, v_diag_2025_);
v___x_2030_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_st_ref_put(v___y_2012_, v___x_2030_);
v___x_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2032_, 0, v_fst_2019_);
return v___x_2032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_2036_, v___y_2037_);
lean_dec(v___y_2037_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_2040_, v___y_2044_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(uint8_t v___x_2058_, uint8_t v___x_2059_, uint8_t v_____do__lift_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
if (v_____do__lift_2060_ == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_box(v___x_2058_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = lean_box(v___x_2059_);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v___x_2072_, lean_object* v___x_2073_, lean_object* v_____do__lift_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
uint8_t v___x_14749__boxed_2082_; uint8_t v___x_14750__boxed_2083_; uint8_t v_____do__lift_14751__boxed_2084_; lean_object* v_res_2085_; 
v___x_14749__boxed_2082_ = lean_unbox(v___x_2072_);
v___x_14750__boxed_2083_ = lean_unbox(v___x_2073_);
v_____do__lift_14751__boxed_2084_ = lean_unbox(v_____do__lift_2074_);
v_res_2085_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_14749__boxed_2082_, v___x_14750__boxed_2083_, v_____do__lift_14751__boxed_2084_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(uint8_t v___x_2086_, uint8_t v___x_2087_, lean_object* v_as_2088_, size_t v_i_2089_, size_t v_stop_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_usize_dec_eq(v_i_2089_, v_stop_2090_);
if (v___x_2096_ == 0)
{
uint8_t v___x_2097_; uint8_t v_a_2099_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2097_ = 1;
v___x_2105_ = lean_array_uget_borrowed(v_as_2088_, v_i_2089_);
lean_inc(v___x_2105_);
v___x_2106_ = l_Lean_Meta_isProof(v___x_2105_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; uint8_t v___x_2108_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v___x_2108_ = lean_unbox(v_a_2107_);
lean_dec(v_a_2107_);
if (v___x_2108_ == 0)
{
v_a_2099_ = v___x_2086_;
goto v___jp_2098_;
}
else
{
v_a_2099_ = v___x_2087_;
goto v___jp_2098_;
}
}
else
{
return v___x_2106_;
}
v___jp_2098_:
{
if (v_a_2099_ == 0)
{
size_t v___x_2100_; size_t v___x_2101_; 
v___x_2100_ = ((size_t)1ULL);
v___x_2101_ = lean_usize_add(v_i_2089_, v___x_2100_);
v_i_2089_ = v___x_2101_;
goto _start;
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = lean_box(v___x_2097_);
v___x_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
return v___x_2104_;
}
}
}
else
{
uint8_t v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = 0;
v___x_2110_ = lean_box(v___x_2109_);
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
return v___x_2111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v___x_2112_, lean_object* v___x_2113_, lean_object* v_as_2114_, lean_object* v_i_2115_, lean_object* v_stop_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
uint8_t v___x_14787__boxed_2122_; uint8_t v___x_14788__boxed_2123_; size_t v_i_boxed_2124_; size_t v_stop_boxed_2125_; lean_object* v_res_2126_; 
v___x_14787__boxed_2122_ = lean_unbox(v___x_2112_);
v___x_14788__boxed_2123_ = lean_unbox(v___x_2113_);
v_i_boxed_2124_ = lean_unbox_usize(v_i_2115_);
lean_dec(v_i_2115_);
v_stop_boxed_2125_ = lean_unbox_usize(v_stop_2116_);
lean_dec(v_stop_2116_);
v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_14787__boxed_2122_, v___x_14788__boxed_2123_, v_as_2114_, v_i_boxed_2124_, v_stop_boxed_2125_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec_ref(v_as_2114_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_p_2127_, lean_object* v_term_2128_, lean_object* v___x_2129_, uint8_t v___x_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_toCold_2138_; lean_object* v_currRecDepth_2139_; lean_object* v_ref_2140_; uint16_t v_optionFlags_2141_; uint8_t v_suppressElabErrors_2142_; uint8_t v_checkDeprecated_2143_; uint8_t v_isRecordingDeps_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2241_; 
v_toCold_2138_ = lean_ctor_get(v___y_2135_, 0);
v_currRecDepth_2139_ = lean_ctor_get(v___y_2135_, 1);
v_ref_2140_ = lean_ctor_get(v___y_2135_, 2);
v_optionFlags_2141_ = lean_ctor_get_uint16(v___y_2135_, sizeof(void*)*3);
v_suppressElabErrors_2142_ = lean_ctor_get_uint8(v___y_2135_, sizeof(void*)*3 + 2);
v_checkDeprecated_2143_ = lean_ctor_get_uint8(v___y_2135_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2144_ = lean_ctor_get_uint8(v___y_2135_, sizeof(void*)*3 + 4);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___y_2135_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2146_ = v___y_2135_;
v_isShared_2147_ = v_isSharedCheck_2241_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_ref_2140_);
lean_inc(v_currRecDepth_2139_);
lean_inc(v_toCold_2138_);
lean_dec(v___y_2135_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2241_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v_ref_2148_; lean_object* v___x_2150_; 
v_ref_2148_ = l_Lean_replaceRef(v_p_2127_, v_ref_2140_);
lean_dec(v_ref_2140_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 2, v_ref_2148_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_toCold_2138_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_currRecDepth_2139_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_ref_2148_);
lean_ctor_set_uint16(v_reuseFailAlloc_2240_, sizeof(void*)*3, v_optionFlags_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2240_, sizeof(void*)*3 + 2, v_suppressElabErrors_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2240_, sizeof(void*)*3 + 3, v_checkDeprecated_2143_);
lean_ctor_set_uint8(v_reuseFailAlloc_2240_, sizeof(void*)*3 + 4, v_isRecordingDeps_2144_);
v___x_2150_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_Elab_Term_elabTerm(v_term_2128_, v___x_2129_, v___x_2130_, v___x_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___x_2150_, v___y_2136_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
v___x_2153_ = 1;
v___x_2154_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_2153_, v___x_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___x_2150_, v___y_2136_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v___x_2155_; lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref_known(v___x_2154_, 1);
v___x_2155_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_2152_, v___y_2134_);
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2223_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2223_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
uint8_t v___x_2160_; 
v___x_2160_ = l_Lean_Expr_hasSyntheticSorry(v_a_2156_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = l_Lean_Expr_eta(v_a_2156_);
v___x_2162_ = l_Lean_Expr_hasMVar(v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
lean_dec_ref(v___x_2150_);
v___x_2163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__0));
v___x_2164_ = lean_box(v___x_2162_);
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2161_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2163_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2167_);
v___x_2169_ = v___x_2158_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
else
{
lean_object* v___x_2171_; 
lean_del_object(v___x_2158_);
v___x_2171_ = l_Lean_Meta_abstractMVars(v___x_2161_, v___x_2130_, v___y_2133_, v___y_2134_, v___x_2150_, v___y_2136_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2210_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2210_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2210_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v_paramNames_2176_; lean_object* v_mvars_2177_; lean_object* v_expr_2178_; uint8_t v_a_2180_; lean_object* v___y_2189_; lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v_paramNames_2176_ = lean_ctor_get(v_a_2172_, 0);
lean_inc_ref(v_paramNames_2176_);
v_mvars_2177_ = lean_ctor_get(v_a_2172_, 1);
lean_inc_ref(v_mvars_2177_);
v_expr_2178_ = lean_ctor_get(v_a_2172_, 2);
lean_inc_ref(v_expr_2178_);
lean_dec(v_a_2172_);
v___x_2192_ = lean_unsigned_to_nat(0u);
v___x_2193_ = lean_array_get_size(v_mvars_2177_);
v___x_2194_ = lean_nat_dec_lt(v___x_2192_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; 
lean_dec_ref(v_mvars_2177_);
v___x_2195_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2162_, v___x_2160_, v___x_2194_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___x_2150_, v___y_2136_);
lean_dec_ref(v___x_2150_);
v___y_2189_ = v___x_2195_;
goto v___jp_2188_;
}
else
{
if (v___x_2194_ == 0)
{
lean_dec_ref(v_mvars_2177_);
lean_dec_ref(v___x_2150_);
v_a_2180_ = v___x_2162_;
goto v___jp_2179_;
}
else
{
size_t v___x_2196_; size_t v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = ((size_t)0ULL);
v___x_2197_ = lean_usize_of_nat(v___x_2193_);
v___x_2198_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2162_, v___x_2160_, v_mvars_2177_, v___x_2196_, v___x_2197_, v___y_2133_, v___y_2134_, v___x_2150_, v___y_2136_);
lean_dec_ref(v_mvars_2177_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; uint8_t v___x_2200_; lean_object* v___x_2201_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2200_ = lean_unbox(v_a_2199_);
lean_dec(v_a_2199_);
v___x_2201_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2162_, v___x_2160_, v___x_2200_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___x_2150_, v___y_2136_);
lean_dec_ref(v___x_2150_);
v___y_2189_ = v___x_2201_;
goto v___jp_2188_;
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec_ref(v_expr_2178_);
lean_dec_ref(v_paramNames_2176_);
lean_del_object(v___x_2174_);
lean_dec_ref(v___x_2150_);
v_a_2202_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2198_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2198_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
v___jp_2179_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2181_ = lean_box(v_a_2180_);
v___x_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2182_, 0, v_expr_2178_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2183_, 0, v_paramNames_2176_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2184_);
v___x_2186_ = v___x_2174_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
v___jp_2188_:
{
lean_object* v_a_2190_; uint8_t v___x_2191_; 
v_a_2190_ = lean_ctor_get(v___y_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref(v___y_2189_);
v___x_2191_ = lean_unbox(v_a_2190_);
lean_dec(v_a_2190_);
v_a_2180_ = v___x_2191_;
goto v___jp_2179_;
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec_ref(v___x_2150_);
v_a_2211_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2171_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2171_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2221_; 
lean_dec(v_a_2156_);
lean_dec_ref(v___x_2150_);
v___x_2219_ = lean_box(0);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2219_);
v___x_2221_ = v___x_2158_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_a_2152_);
lean_dec_ref(v___x_2150_);
v_a_2224_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2154_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2154_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v___x_2150_);
v_a_2232_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2151_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2151_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_p_2242_, lean_object* v_term_2243_, lean_object* v___x_2244_, lean_object* v___x_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
uint8_t v___x_14844__boxed_2253_; lean_object* v_res_2254_; 
v___x_14844__boxed_2253_ = lean_unbox(v___x_2245_);
v_res_2254_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_p_2242_, v_term_2243_, v___x_2244_, v___x_14844__boxed_2253_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v_p_2242_);
return v_res_2254_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__2));
v___x_2260_ = l_Lean_stringToMessageData(v___x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(lean_object* v_params_2261_, lean_object* v_p_2262_, lean_object* v_fst_2263_, lean_object* v_fst_2264_, uint8_t v___x_2265_, uint8_t v_minIndexable_2266_, lean_object* v_kind_2267_, lean_object* v_idx_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_symPrios_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; 
v_symPrios_2274_ = lean_ctor_get(v_params_2261_, 5);
lean_inc_ref(v_symPrios_2274_);
lean_dec_ref(v_params_2261_);
v___x_2275_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__1));
v___x_2276_ = lean_name_append_index_after(v___x_2275_, v_idx_2268_);
v___x_2277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v_p_2262_);
v___x_2278_ = 0;
v___x_2279_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2277_, v_fst_2263_, v_fst_2264_, v_kind_2267_, v_symPrios_2274_, v___x_2265_, v___x_2278_, v_minIndexable_2266_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2290_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2290_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2290_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
if (lean_obj_tag(v_a_2280_) == 1)
{
lean_object* v_val_2284_; lean_object* v___x_2286_; 
v_val_2284_ = lean_ctor_get(v_a_2280_, 0);
lean_inc(v_val_2284_);
lean_dec_ref_known(v_a_2280_, 1);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v_val_2284_);
v___x_2286_ = v___x_2282_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_val_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_del_object(v___x_2282_);
lean_dec(v_a_2280_);
v___x_2288_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3);
v___x_2289_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2288_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
return v___x_2289_;
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
v_a_2291_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2279_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2279_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed(lean_object* v_params_2299_, lean_object* v_p_2300_, lean_object* v_fst_2301_, lean_object* v_fst_2302_, lean_object* v___x_2303_, lean_object* v_minIndexable_2304_, lean_object* v_kind_2305_, lean_object* v_idx_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
uint8_t v___x_15074__boxed_2312_; uint8_t v_minIndexable_boxed_2313_; lean_object* v_res_2314_; 
v___x_15074__boxed_2312_ = lean_unbox(v___x_2303_);
v_minIndexable_boxed_2313_ = lean_unbox(v_minIndexable_2304_);
v_res_2314_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(v_params_2299_, v_p_2300_, v_fst_2301_, v_fst_2302_, v___x_15074__boxed_2312_, v_minIndexable_boxed_2313_, v_kind_2305_, v_idx_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
return v_res_2314_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_box(1);
v___x_2316_ = l_Lean_MessageData_ofFormat(v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__2));
v___x_2321_ = l_Lean_MessageData_ofFormat(v___x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(lean_object* v_x_2322_, lean_object* v_x_2323_){
_start:
{
if (lean_obj_tag(v_x_2323_) == 0)
{
return v_x_2322_;
}
else
{
lean_object* v_head_2324_; lean_object* v_tail_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2347_; 
v_head_2324_ = lean_ctor_get(v_x_2323_, 0);
v_tail_2325_ = lean_ctor_get(v_x_2323_, 1);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_x_2323_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2327_ = v_x_2323_;
v_isShared_2328_ = v_isSharedCheck_2347_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_tail_2325_);
lean_inc(v_head_2324_);
lean_dec(v_x_2323_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2347_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v_before_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2345_; 
v_before_2329_ = lean_ctor_get(v_head_2324_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_head_2324_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; 
v_unused_2346_ = lean_ctor_get(v_head_2324_, 1);
lean_dec(v_unused_2346_);
v___x_2331_ = v_head_2324_;
v_isShared_2332_ = v_isSharedCheck_2345_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_before_2329_);
lean_dec(v_head_2324_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2345_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2332_ == 0)
{
lean_ctor_set_tag(v___x_2331_, 7);
lean_ctor_set(v___x_2331_, 1, v___x_2333_);
lean_ctor_set(v___x_2331_, 0, v_x_2322_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_x_2322_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2336_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3);
if (v_isShared_2328_ == 0)
{
lean_ctor_set_tag(v___x_2327_, 7);
lean_ctor_set(v___x_2327_, 1, v___x_2336_);
lean_ctor_set(v___x_2327_, 0, v___x_2335_);
v___x_2338_ = v___x_2327_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2339_ = l_Lean_MessageData_ofSyntax(v_before_2329_);
v___x_2340_ = l_Lean_indentD(v___x_2339_);
v___x_2341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2338_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
v_x_2322_ = v___x_2341_;
v_x_2323_ = v_tail_2325_;
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
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__1));
v___x_2352_ = l_Lean_MessageData_ofFormat(v___x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(lean_object* v_msgData_2353_, lean_object* v_macroStack_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2357_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2355_);
v___x_2358_ = l_Lean_Elab_pp_macroStack;
v___x_2359_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_2357_, v___x_2358_);
lean_dec_ref(v___x_2357_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; 
lean_dec(v_macroStack_2354_);
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v_msgData_2353_);
return v___x_2360_;
}
else
{
if (lean_obj_tag(v_macroStack_2354_) == 0)
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v_msgData_2353_);
return v___x_2361_;
}
else
{
lean_object* v_head_2362_; lean_object* v_after_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2378_; 
v_head_2362_ = lean_ctor_get(v_macroStack_2354_, 0);
lean_inc(v_head_2362_);
v_after_2363_ = lean_ctor_get(v_head_2362_, 1);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_head_2362_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; 
v_unused_2379_ = lean_ctor_get(v_head_2362_, 0);
lean_dec(v_unused_2379_);
v___x_2365_ = v_head_2362_;
v_isShared_2366_ = v_isSharedCheck_2378_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_after_2363_);
lean_dec(v_head_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2378_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2367_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2366_ == 0)
{
lean_ctor_set_tag(v___x_2365_, 7);
lean_ctor_set(v___x_2365_, 1, v___x_2367_);
lean_ctor_set(v___x_2365_, 0, v_msgData_2353_);
v___x_2369_ = v___x_2365_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_msgData_2353_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v_msgData_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2370_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2);
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = l_Lean_MessageData_ofSyntax(v_after_2363_);
v___x_2373_ = l_Lean_indentD(v___x_2372_);
v_msgData_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2374_, 0, v___x_2371_);
lean_ctor_set(v_msgData_2374_, 1, v___x_2373_);
v___x_2375_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(v_msgData_2374_, v_macroStack_2354_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_2380_, lean_object* v_macroStack_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2380_, v_macroStack_2381_, v___y_2382_);
lean_dec_ref(v___y_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(lean_object* v_msg_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_ref_2393_; lean_object* v_macroStack_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v_a_2397_; lean_object* v___x_2398_; lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2407_; 
v_ref_2393_ = lean_ctor_get(v___y_2390_, 2);
v_macroStack_2394_ = lean_ctor_get(v___y_2386_, 1);
v___x_2395_ = l_Lean_Elab_getBetterRef(v_ref_2393_, v_macroStack_2394_);
v___x_2396_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2385_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref(v___x_2396_);
lean_inc(v_macroStack_2394_);
v___x_2398_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_a_2397_, v_macroStack_2394_, v___y_2390_);
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2401_ = v___x_2398_;
v_isShared_2402_ = v_isSharedCheck_2407_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2407_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2395_);
lean_ctor_set(v___x_2403_, 1, v_a_2399_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set_tag(v___x_2401_, 1);
lean_ctor_set(v___x_2401_, 0, v___x_2403_);
v___x_2405_ = v___x_2401_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg___boxed(lean_object* v_msg_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
return v_res_2416_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2419_ = l_Lean_stringToMessageData(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2422_ = l_Lean_stringToMessageData(v___x_2421_);
return v___x_2422_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2425_ = l_Lean_stringToMessageData(v___x_2424_);
return v___x_2425_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_2428_ = l_Lean_stringToMessageData(v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2429_, lean_object* v_p_2430_, lean_object* v_mod_x3f_2431_, lean_object* v_term_2432_, uint8_t v_minIndexable_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v___y_2442_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2670_; uint8_t v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v_kind_2687_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v_toCold_2797_; lean_object* v_currRecDepth_2798_; lean_object* v_ref_2799_; uint16_t v_optionFlags_2800_; uint8_t v_suppressElabErrors_2801_; uint8_t v_checkDeprecated_2802_; uint8_t v_isRecordingDeps_2803_; lean_object* v_ref_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_toCold_2797_ = lean_ctor_get(v_a_2438_, 0);
v_currRecDepth_2798_ = lean_ctor_get(v_a_2438_, 1);
v_ref_2799_ = lean_ctor_get(v_a_2438_, 2);
v_optionFlags_2800_ = lean_ctor_get_uint16(v_a_2438_, sizeof(void*)*3);
v_suppressElabErrors_2801_ = lean_ctor_get_uint8(v_a_2438_, sizeof(void*)*3 + 2);
v_checkDeprecated_2802_ = lean_ctor_get_uint8(v_a_2438_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2803_ = lean_ctor_get_uint8(v_a_2438_, sizeof(void*)*3 + 4);
v_ref_2804_ = l_Lean_replaceRef(v_p_2430_, v_ref_2799_);
lean_inc(v_currRecDepth_2798_);
lean_inc_ref(v_toCold_2797_);
v___x_2805_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2805_, 0, v_toCold_2797_);
lean_ctor_set(v___x_2805_, 1, v_currRecDepth_2798_);
lean_ctor_set(v___x_2805_, 2, v_ref_2804_);
lean_ctor_set_uint16(v___x_2805_, sizeof(void*)*3, v_optionFlags_2800_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*3 + 2, v_suppressElabErrors_2801_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*3 + 3, v_checkDeprecated_2802_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*3 + 4, v_isRecordingDeps_2803_);
v___x_2806_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2429_, v___x_2805_, v_a_2439_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_dec_ref_known(v___x_2806_, 1);
if (lean_obj_tag(v_mod_x3f_2431_) == 1)
{
lean_object* v_val_2807_; lean_object* v___x_2808_; 
v_val_2807_ = lean_ctor_get(v_mod_x3f_2431_, 0);
lean_inc(v_val_2807_);
v___x_2808_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2807_, v___x_2805_, v_a_2439_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
switch(lean_obj_tag(v_a_2809_))
{
case 0:
{
lean_object* v_k_2810_; 
v_k_2810_ = lean_ctor_get(v_a_2809_, 0);
lean_inc(v_k_2810_);
lean_dec_ref_known(v_a_2809_, 1);
if (lean_obj_tag(v_k_2810_) == 9)
{
lean_dec_ref_known(v_mod_x3f_2431_, 1);
lean_dec(v_term_2432_);
lean_dec(v_p_2430_);
lean_dec_ref(v_params_2429_);
v___y_2756_ = v_a_2434_;
v___y_2757_ = v_a_2435_;
v___y_2758_ = v_a_2436_;
v___y_2759_ = v_a_2437_;
v___y_2760_ = v___x_2805_;
v___y_2761_ = v_a_2439_;
goto v___jp_2755_;
}
else
{
v_kind_2687_ = v_k_2810_;
v___y_2688_ = v_a_2434_;
v___y_2689_ = v_a_2435_;
v___y_2690_ = v_a_2436_;
v___y_2691_ = v_a_2437_;
v___y_2692_ = v___x_2805_;
v___y_2693_ = v_a_2439_;
goto v___jp_2686_;
}
}
case 1:
{
lean_dec_ref_known(v_a_2809_, 0);
lean_dec_ref_known(v_mod_x3f_2431_, 1);
lean_dec(v_term_2432_);
lean_dec(v_p_2430_);
lean_dec_ref(v_params_2429_);
v___y_2773_ = v_a_2434_;
v___y_2774_ = v_a_2435_;
v___y_2775_ = v_a_2436_;
v___y_2776_ = v_a_2437_;
v___y_2777_ = v___x_2805_;
v___y_2778_ = v_a_2439_;
goto v___jp_2772_;
}
case 3:
{
v___y_2790_ = v_a_2434_;
v___y_2791_ = v_a_2435_;
v___y_2792_ = v_a_2436_;
v___y_2793_ = v_a_2437_;
v___y_2794_ = v___x_2805_;
v___y_2795_ = v_a_2439_;
goto v___jp_2789_;
}
case 5:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec_ref_known(v_a_2809_, 1);
lean_dec_ref_known(v_mod_x3f_2431_, 1);
lean_dec(v_term_2432_);
lean_dec(v_p_2430_);
lean_dec_ref(v_params_2429_);
v___x_2811_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2812_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2811_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v___x_2805_, v_a_2439_);
lean_dec_ref_known(v___x_2805_, 3);
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
case 8:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec_ref_known(v_a_2809_, 0);
lean_dec_ref_known(v_mod_x3f_2431_, 1);
lean_dec(v_term_2432_);
lean_dec(v_p_2430_);
lean_dec_ref(v_params_2429_);
v___x_2821_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2822_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2821_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v___x_2805_, v_a_2439_);
lean_dec_ref_known(v___x_2805_, 3);
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
case 10:
{
lean_dec_ref_known(v_a_2809_, 0);
lean_dec_ref_known(v_mod_x3f_2431_, 1);
lean_dec(v_term_2432_);
lean_dec(v_p_2430_);
lean_dec_ref(v_params_2429_);
v___y_2773_ = v_a_2434_;
v___y_2774_ = v_a_2435_;
v___y_2775_ = v_a_2436_;
v___y_2776_ = v_a_2437_;
v___y_2777_ = v___x_2805_;
v___y_2778_ = v_a_2439_;
goto v___jp_2772_;
}
default: 
{
lean_dec(v_a_2809_);
lean_dec_ref_known(v_mod_x3f_2431_, 1);
lean_dec(v_term_2432_);
lean_dec(v_p_2430_);
lean_dec_ref(v_params_2429_);
v___y_2756_ = v_a_2434_;
v___y_2757_ = v_a_2435_;
v___y_2758_ = v_a_2436_;
v___y_2759_ = v_a_2437_;
v___y_2760_ = v___x_2805_;
v___y_2761_ = v_a_2439_;
goto v___jp_2755_;
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec_ref_known(v_mod_x3f_2431_, 1);
lean_dec_ref_known(v___x_2805_, 3);
lean_dec(v_term_2432_);
lean_dec(v_p_2430_);
lean_dec_ref(v_params_2429_);
v_a_2831_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2808_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2808_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
else
{
v___y_2790_ = v_a_2434_;
v___y_2791_ = v_a_2435_;
v___y_2792_ = v_a_2436_;
v___y_2793_ = v_a_2437_;
v___y_2794_ = v___x_2805_;
v___y_2795_ = v_a_2439_;
goto v___jp_2789_;
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec_ref_known(v___x_2805_, 3);
lean_dec(v_term_2432_);
lean_dec(v_mod_x3f_2431_);
lean_dec(v_p_2430_);
lean_dec_ref(v_params_2429_);
v_a_2839_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2806_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2806_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
v___jp_2441_:
{
lean_object* v_config_2443_; lean_object* v_extensions_2444_; lean_object* v_extra_2445_; lean_object* v_extraInj_2446_; lean_object* v_extraFacts_2447_; lean_object* v_symPrios_2448_; lean_object* v_norm_2449_; lean_object* v_normProcs_2450_; lean_object* v_anchorRefs_x3f_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2460_; 
v_config_2443_ = lean_ctor_get(v_params_2429_, 0);
v_extensions_2444_ = lean_ctor_get(v_params_2429_, 1);
v_extra_2445_ = lean_ctor_get(v_params_2429_, 2);
v_extraInj_2446_ = lean_ctor_get(v_params_2429_, 3);
v_extraFacts_2447_ = lean_ctor_get(v_params_2429_, 4);
v_symPrios_2448_ = lean_ctor_get(v_params_2429_, 5);
v_norm_2449_ = lean_ctor_get(v_params_2429_, 6);
v_normProcs_2450_ = lean_ctor_get(v_params_2429_, 7);
v_anchorRefs_x3f_2451_ = lean_ctor_get(v_params_2429_, 8);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_params_2429_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2453_ = v_params_2429_;
v_isShared_2454_ = v_isSharedCheck_2460_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_anchorRefs_x3f_2451_);
lean_inc(v_normProcs_2450_);
lean_inc(v_norm_2449_);
lean_inc(v_symPrios_2448_);
lean_inc(v_extraFacts_2447_);
lean_inc(v_extraInj_2446_);
lean_inc(v_extra_2445_);
lean_inc(v_extensions_2444_);
lean_inc(v_config_2443_);
lean_dec(v_params_2429_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2460_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2447_, v___y_2442_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 4, v___x_2455_);
v___x_2457_ = v___x_2453_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_config_2443_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_extensions_2444_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_extra_2445_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_extraInj_2446_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2459_, 5, v_symPrios_2448_);
lean_ctor_set(v_reuseFailAlloc_2459_, 6, v_norm_2449_);
lean_ctor_set(v_reuseFailAlloc_2459_, 7, v_normProcs_2450_);
lean_ctor_set(v_reuseFailAlloc_2459_, 8, v_anchorRefs_x3f_2451_);
v___x_2457_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
return v___x_2458_;
}
}
}
v___jp_2461_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2471_ = lean_array_get_size(v___y_2463_);
lean_dec_ref(v___y_2463_);
v___x_2472_ = lean_unsigned_to_nat(0u);
v___x_2473_ = lean_nat_dec_eq(v___x_2471_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v___y_2464_);
lean_dec_ref(v_params_2429_);
v___x_2474_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2475_ = l_Lean_indentExpr(v___y_2462_);
v___x_2476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
v___x_2477_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2476_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec_ref(v___y_2469_);
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
lean_dec_ref(v___y_2469_);
lean_dec_ref(v___y_2462_);
v___y_2442_ = v___y_2464_;
goto v___jp_2441_;
}
}
v___jp_2486_:
{
lean_object* v___x_2503_; 
lean_inc(v___y_2502_);
lean_inc(v___y_2500_);
lean_inc_ref(v___y_2499_);
v___x_2503_ = lean_apply_7(v___y_2495_, v___y_2498_, v___y_2494_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, lean_box(0));
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2513_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2506_ = v___x_2503_;
v_isShared_2507_ = v_isSharedCheck_2513_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2513_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2508_ = l_Lean_PersistentArray_push___redArg(v___y_2497_, v_a_2504_);
v___x_2509_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2509_, 0, v___y_2496_);
lean_ctor_set(v___x_2509_, 1, v___y_2490_);
lean_ctor_set(v___x_2509_, 2, v___x_2508_);
lean_ctor_set(v___x_2509_, 3, v___y_2492_);
lean_ctor_set(v___x_2509_, 4, v___y_2487_);
lean_ctor_set(v___x_2509_, 5, v___y_2489_);
lean_ctor_set(v___x_2509_, 6, v___y_2488_);
lean_ctor_set(v___x_2509_, 7, v___y_2493_);
lean_ctor_set(v___x_2509_, 8, v___y_2491_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2509_);
v___x_2511_ = v___x_2506_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec_ref(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v___y_2487_);
v_a_2514_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2503_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2503_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
v___jp_2522_:
{
lean_object* v___x_2539_; 
v___x_2539_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2433_, v___y_2535_, v___y_2528_, v___y_2537_, v___y_2531_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_dec_ref_known(v___x_2539_, 1);
v___y_2487_ = v___y_2523_;
v___y_2488_ = v___y_2532_;
v___y_2489_ = v___y_2533_;
v___y_2490_ = v___y_2534_;
v___y_2491_ = v___y_2524_;
v___y_2492_ = v___y_2525_;
v___y_2493_ = v___y_2536_;
v___y_2494_ = v___y_2526_;
v___y_2495_ = v___y_2527_;
v___y_2496_ = v___y_2538_;
v___y_2497_ = v___y_2530_;
v___y_2498_ = v___y_2529_;
v___y_2499_ = v___y_2535_;
v___y_2500_ = v___y_2528_;
v___y_2501_ = v___y_2537_;
v___y_2502_ = v___y_2531_;
goto v___jp_2486_;
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec_ref(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec_ref(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
v___jp_2548_:
{
lean_object* v_extra_2555_; 
v_extra_2555_ = lean_ctor_get(v_params_2429_, 2);
lean_inc_ref(v_extra_2555_);
if (lean_obj_tag(v___y_2554_) == 2)
{
lean_object* v_config_2556_; lean_object* v_extensions_2557_; lean_object* v_extraInj_2558_; lean_object* v_extraFacts_2559_; lean_object* v_symPrios_2560_; lean_object* v_norm_2561_; lean_object* v_normProcs_2562_; lean_object* v_anchorRefs_x3f_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2618_; 
v_config_2556_ = lean_ctor_get(v_params_2429_, 0);
v_extensions_2557_ = lean_ctor_get(v_params_2429_, 1);
v_extraInj_2558_ = lean_ctor_get(v_params_2429_, 3);
v_extraFacts_2559_ = lean_ctor_get(v_params_2429_, 4);
v_symPrios_2560_ = lean_ctor_get(v_params_2429_, 5);
v_norm_2561_ = lean_ctor_get(v_params_2429_, 6);
v_normProcs_2562_ = lean_ctor_get(v_params_2429_, 7);
v_anchorRefs_x3f_2563_ = lean_ctor_get(v_params_2429_, 8);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_params_2429_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; 
v_unused_2619_ = lean_ctor_get(v_params_2429_, 2);
lean_dec(v_unused_2619_);
v___x_2565_ = v_params_2429_;
v_isShared_2566_ = v_isSharedCheck_2618_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_anchorRefs_x3f_2563_);
lean_inc(v_normProcs_2562_);
lean_inc(v_norm_2561_);
lean_inc(v_symPrios_2560_);
lean_inc(v_extraFacts_2559_);
lean_inc(v_extraInj_2558_);
lean_inc(v_extensions_2557_);
lean_inc(v_config_2556_);
lean_dec(v_params_2429_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2618_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_size_2567_; uint8_t v_gen_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2617_; 
v_size_2567_ = lean_ctor_get(v_extra_2555_, 2);
v_gen_2568_ = lean_ctor_get_uint8(v___y_2554_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___y_2554_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2570_ = v___y_2554_;
v_isShared_2571_ = v_isSharedCheck_2617_;
goto v_resetjp_2569_;
}
else
{
lean_dec(v___y_2554_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2617_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; 
v___x_2572_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2433_, v___y_2550_, v___y_2553_, v___y_2551_, v___y_2549_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v___x_2574_; 
lean_dec_ref_known(v___x_2572_, 1);
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 0);
v___x_2574_ = v___x_2570_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, 0, v_gen_2568_);
v___x_2574_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2575_; 
lean_inc_ref(v___y_2552_);
lean_inc(v___y_2549_);
lean_inc_ref(v___y_2551_);
lean_inc(v___y_2553_);
lean_inc_ref(v___y_2550_);
lean_inc(v_size_2567_);
v___x_2575_ = lean_apply_7(v___y_2552_, v___x_2574_, v_size_2567_, v___y_2550_, v___y_2553_, v___y_2551_, v___y_2549_, lean_box(0));
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2577_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2577_, 0, v_gen_2568_);
lean_inc(v___y_2549_);
lean_inc(v___y_2553_);
lean_inc_ref(v___y_2550_);
lean_inc(v_size_2567_);
v___x_2578_ = lean_apply_7(v___y_2552_, v___x_2577_, v_size_2567_, v___y_2550_, v___y_2553_, v___y_2551_, v___y_2549_, lean_box(0));
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2591_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2591_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2591_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2583_ = l_Lean_PersistentArray_push___redArg(v_extra_2555_, v_a_2576_);
v___x_2584_ = l_Lean_PersistentArray_push___redArg(v___x_2583_, v_a_2579_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 2, v___x_2584_);
v___x_2586_ = v___x_2565_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_config_2556_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_extensions_2557_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v_extraInj_2558_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v_extraFacts_2559_);
lean_ctor_set(v_reuseFailAlloc_2590_, 5, v_symPrios_2560_);
lean_ctor_set(v_reuseFailAlloc_2590_, 6, v_norm_2561_);
lean_ctor_set(v_reuseFailAlloc_2590_, 7, v_normProcs_2562_);
lean_ctor_set(v_reuseFailAlloc_2590_, 8, v_anchorRefs_x3f_2563_);
v___x_2586_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2588_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2586_);
v___x_2588_ = v___x_2581_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
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
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_a_2576_);
lean_del_object(v___x_2565_);
lean_dec(v_anchorRefs_x3f_2563_);
lean_dec_ref(v_normProcs_2562_);
lean_dec_ref(v_norm_2561_);
lean_dec_ref(v_symPrios_2560_);
lean_dec_ref(v_extraFacts_2559_);
lean_dec_ref(v_extraInj_2558_);
lean_dec_ref(v_extensions_2557_);
lean_dec_ref(v_config_2556_);
lean_dec_ref(v_extra_2555_);
v_a_2592_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2578_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2578_);
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
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_del_object(v___x_2565_);
lean_dec(v_anchorRefs_x3f_2563_);
lean_dec_ref(v_normProcs_2562_);
lean_dec_ref(v_norm_2561_);
lean_dec_ref(v_symPrios_2560_);
lean_dec_ref(v_extraFacts_2559_);
lean_dec_ref(v_extraInj_2558_);
lean_dec_ref(v_extensions_2557_);
lean_dec_ref(v_config_2556_);
lean_dec_ref(v_extra_2555_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v___y_2551_);
v_a_2600_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2575_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2575_);
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
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_del_object(v___x_2570_);
lean_del_object(v___x_2565_);
lean_dec(v_anchorRefs_x3f_2563_);
lean_dec_ref(v_normProcs_2562_);
lean_dec_ref(v_norm_2561_);
lean_dec_ref(v_symPrios_2560_);
lean_dec_ref(v_extraFacts_2559_);
lean_dec_ref(v_extraInj_2558_);
lean_dec_ref(v_extensions_2557_);
lean_dec_ref(v_config_2556_);
lean_dec_ref(v_extra_2555_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v___y_2551_);
v_a_2609_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2572_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2572_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
}
else
{
switch(lean_obj_tag(v___y_2554_))
{
case 0:
{
lean_object* v_config_2620_; lean_object* v_extensions_2621_; lean_object* v_extraInj_2622_; lean_object* v_extraFacts_2623_; lean_object* v_symPrios_2624_; lean_object* v_norm_2625_; lean_object* v_normProcs_2626_; lean_object* v_anchorRefs_x3f_2627_; lean_object* v_size_2628_; 
v_config_2620_ = lean_ctor_get(v_params_2429_, 0);
lean_inc_ref(v_config_2620_);
v_extensions_2621_ = lean_ctor_get(v_params_2429_, 1);
lean_inc_ref(v_extensions_2621_);
v_extraInj_2622_ = lean_ctor_get(v_params_2429_, 3);
lean_inc_ref(v_extraInj_2622_);
v_extraFacts_2623_ = lean_ctor_get(v_params_2429_, 4);
lean_inc_ref(v_extraFacts_2623_);
v_symPrios_2624_ = lean_ctor_get(v_params_2429_, 5);
lean_inc_ref(v_symPrios_2624_);
v_norm_2625_ = lean_ctor_get(v_params_2429_, 6);
lean_inc_ref(v_norm_2625_);
v_normProcs_2626_ = lean_ctor_get(v_params_2429_, 7);
lean_inc_ref(v_normProcs_2626_);
v_anchorRefs_x3f_2627_ = lean_ctor_get(v_params_2429_, 8);
lean_inc(v_anchorRefs_x3f_2627_);
lean_dec_ref(v_params_2429_);
v_size_2628_ = lean_ctor_get(v_extra_2555_, 2);
lean_inc(v_size_2628_);
v___y_2523_ = v_extraFacts_2623_;
v___y_2524_ = v_anchorRefs_x3f_2627_;
v___y_2525_ = v_extraInj_2622_;
v___y_2526_ = v_size_2628_;
v___y_2527_ = v___y_2552_;
v___y_2528_ = v___y_2553_;
v___y_2529_ = v___y_2554_;
v___y_2530_ = v_extra_2555_;
v___y_2531_ = v___y_2549_;
v___y_2532_ = v_norm_2625_;
v___y_2533_ = v_symPrios_2624_;
v___y_2534_ = v_extensions_2621_;
v___y_2535_ = v___y_2550_;
v___y_2536_ = v_normProcs_2626_;
v___y_2537_ = v___y_2551_;
v___y_2538_ = v_config_2620_;
goto v___jp_2522_;
}
case 1:
{
lean_object* v_config_2629_; lean_object* v_extensions_2630_; lean_object* v_extraInj_2631_; lean_object* v_extraFacts_2632_; lean_object* v_symPrios_2633_; lean_object* v_norm_2634_; lean_object* v_normProcs_2635_; lean_object* v_anchorRefs_x3f_2636_; lean_object* v_size_2637_; 
v_config_2629_ = lean_ctor_get(v_params_2429_, 0);
lean_inc_ref(v_config_2629_);
v_extensions_2630_ = lean_ctor_get(v_params_2429_, 1);
lean_inc_ref(v_extensions_2630_);
v_extraInj_2631_ = lean_ctor_get(v_params_2429_, 3);
lean_inc_ref(v_extraInj_2631_);
v_extraFacts_2632_ = lean_ctor_get(v_params_2429_, 4);
lean_inc_ref(v_extraFacts_2632_);
v_symPrios_2633_ = lean_ctor_get(v_params_2429_, 5);
lean_inc_ref(v_symPrios_2633_);
v_norm_2634_ = lean_ctor_get(v_params_2429_, 6);
lean_inc_ref(v_norm_2634_);
v_normProcs_2635_ = lean_ctor_get(v_params_2429_, 7);
lean_inc_ref(v_normProcs_2635_);
v_anchorRefs_x3f_2636_ = lean_ctor_get(v_params_2429_, 8);
lean_inc(v_anchorRefs_x3f_2636_);
lean_dec_ref(v_params_2429_);
v_size_2637_ = lean_ctor_get(v_extra_2555_, 2);
lean_inc(v_size_2637_);
v___y_2523_ = v_extraFacts_2632_;
v___y_2524_ = v_anchorRefs_x3f_2636_;
v___y_2525_ = v_extraInj_2631_;
v___y_2526_ = v_size_2637_;
v___y_2527_ = v___y_2552_;
v___y_2528_ = v___y_2553_;
v___y_2529_ = v___y_2554_;
v___y_2530_ = v_extra_2555_;
v___y_2531_ = v___y_2549_;
v___y_2532_ = v_norm_2634_;
v___y_2533_ = v_symPrios_2633_;
v___y_2534_ = v_extensions_2630_;
v___y_2535_ = v___y_2550_;
v___y_2536_ = v_normProcs_2635_;
v___y_2537_ = v___y_2551_;
v___y_2538_ = v_config_2629_;
goto v___jp_2522_;
}
default: 
{
lean_object* v_config_2638_; lean_object* v_extensions_2639_; lean_object* v_extraInj_2640_; lean_object* v_extraFacts_2641_; lean_object* v_symPrios_2642_; lean_object* v_norm_2643_; lean_object* v_normProcs_2644_; lean_object* v_anchorRefs_x3f_2645_; lean_object* v_size_2646_; 
v_config_2638_ = lean_ctor_get(v_params_2429_, 0);
lean_inc_ref(v_config_2638_);
v_extensions_2639_ = lean_ctor_get(v_params_2429_, 1);
lean_inc_ref(v_extensions_2639_);
v_extraInj_2640_ = lean_ctor_get(v_params_2429_, 3);
lean_inc_ref(v_extraInj_2640_);
v_extraFacts_2641_ = lean_ctor_get(v_params_2429_, 4);
lean_inc_ref(v_extraFacts_2641_);
v_symPrios_2642_ = lean_ctor_get(v_params_2429_, 5);
lean_inc_ref(v_symPrios_2642_);
v_norm_2643_ = lean_ctor_get(v_params_2429_, 6);
lean_inc_ref(v_norm_2643_);
v_normProcs_2644_ = lean_ctor_get(v_params_2429_, 7);
lean_inc_ref(v_normProcs_2644_);
v_anchorRefs_x3f_2645_ = lean_ctor_get(v_params_2429_, 8);
lean_inc(v_anchorRefs_x3f_2645_);
lean_dec_ref(v_params_2429_);
v_size_2646_ = lean_ctor_get(v_extra_2555_, 2);
lean_inc(v_size_2646_);
v___y_2487_ = v_extraFacts_2641_;
v___y_2488_ = v_norm_2643_;
v___y_2489_ = v_symPrios_2642_;
v___y_2490_ = v_extensions_2639_;
v___y_2491_ = v_anchorRefs_x3f_2645_;
v___y_2492_ = v_extraInj_2640_;
v___y_2493_ = v_normProcs_2644_;
v___y_2494_ = v_size_2646_;
v___y_2495_ = v___y_2552_;
v___y_2496_ = v_config_2638_;
v___y_2497_ = v_extra_2555_;
v___y_2498_ = v___y_2554_;
v___y_2499_ = v___y_2550_;
v___y_2500_ = v___y_2553_;
v___y_2501_ = v___y_2551_;
v___y_2502_ = v___y_2549_;
goto v___jp_2486_;
}
}
}
}
v___jp_2647_:
{
if (lean_obj_tag(v_mod_x3f_2431_) == 0)
{
v___y_2462_ = v___y_2648_;
v___y_2463_ = v___y_2653_;
v___y_2464_ = v___y_2654_;
v___y_2465_ = v___y_2656_;
v___y_2466_ = v___y_2650_;
v___y_2467_ = v___y_2651_;
v___y_2468_ = v___y_2655_;
v___y_2469_ = v___y_2652_;
v___y_2470_ = v___y_2649_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec_ref_known(v_mod_x3f_2431_, 1);
lean_dec_ref(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec_ref(v_params_2429_);
v___x_2657_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2658_ = l_Lean_indentExpr(v___y_2648_);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2659_, v___y_2656_, v___y_2650_, v___y_2651_, v___y_2655_, v___y_2652_, v___y_2649_);
lean_dec_ref(v___y_2652_);
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2660_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2660_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
v___jp_2669_:
{
uint8_t v___x_2682_; 
v___x_2682_ = l_Lean_Expr_isForall(v___y_2670_);
if (v___x_2682_ == 0)
{
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2672_);
v___y_2648_ = v___y_2670_;
v___y_2649_ = v___y_2681_;
v___y_2650_ = v___y_2677_;
v___y_2651_ = v___y_2678_;
v___y_2652_ = v___y_2680_;
v___y_2653_ = v___y_2673_;
v___y_2654_ = v___y_2674_;
v___y_2655_ = v___y_2679_;
v___y_2656_ = v___y_2676_;
goto v___jp_2647_;
}
else
{
if (v___y_2671_ == 0)
{
lean_dec_ref(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___y_2670_);
lean_dec(v_mod_x3f_2431_);
v___y_2549_ = v___y_2681_;
v___y_2550_ = v___y_2678_;
v___y_2551_ = v___y_2680_;
v___y_2552_ = v___y_2672_;
v___y_2553_ = v___y_2679_;
v___y_2554_ = v___y_2675_;
goto v___jp_2548_;
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2683_ = lean_array_get_size(v___y_2673_);
v___x_2684_ = lean_unsigned_to_nat(0u);
v___x_2685_ = lean_nat_dec_eq(v___x_2683_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_dec_ref(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___y_2670_);
lean_dec(v_mod_x3f_2431_);
v___y_2549_ = v___y_2681_;
v___y_2550_ = v___y_2678_;
v___y_2551_ = v___y_2680_;
v___y_2552_ = v___y_2672_;
v___y_2553_ = v___y_2679_;
v___y_2554_ = v___y_2675_;
goto v___jp_2548_;
}
else
{
if (lean_obj_tag(v_mod_x3f_2431_) == 0)
{
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2672_);
v___y_2648_ = v___y_2670_;
v___y_2649_ = v___y_2681_;
v___y_2650_ = v___y_2677_;
v___y_2651_ = v___y_2678_;
v___y_2652_ = v___y_2680_;
v___y_2653_ = v___y_2673_;
v___y_2654_ = v___y_2674_;
v___y_2655_ = v___y_2679_;
v___y_2656_ = v___y_2676_;
goto v___jp_2647_;
}
else
{
lean_dec_ref_known(v_mod_x3f_2431_, 1);
lean_dec_ref(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___y_2670_);
v___y_2549_ = v___y_2681_;
v___y_2550_ = v___y_2678_;
v___y_2551_ = v___y_2680_;
v___y_2552_ = v___y_2672_;
v___y_2553_ = v___y_2679_;
v___y_2554_ = v___y_2675_;
goto v___jp_2548_;
}
}
}
}
}
v___jp_2686_:
{
lean_object* v___x_2694_; uint8_t v___x_2695_; lean_object* v___x_2696_; lean_object* v___f_2697_; lean_object* v___x_2698_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = 1;
v___x_2696_ = lean_box(v___x_2695_);
lean_inc(v_p_2430_);
v___f_2697_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2697_, 0, v_p_2430_);
lean_closure_set(v___f_2697_, 1, v_term_2432_);
lean_closure_set(v___f_2697_, 2, v___x_2694_);
lean_closure_set(v___f_2697_, 3, v___x_2696_);
v___x_2698_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2697_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2746_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2701_ = v___x_2698_;
v_isShared_2702_ = v_isSharedCheck_2746_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2698_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2746_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
if (lean_obj_tag(v_a_2699_) == 1)
{
lean_object* v_val_2703_; lean_object* v_snd_2704_; lean_object* v_fst_2705_; lean_object* v_fst_2706_; lean_object* v_snd_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___f_2710_; lean_object* v___x_2711_; 
lean_del_object(v___x_2701_);
v_val_2703_ = lean_ctor_get(v_a_2699_, 0);
lean_inc(v_val_2703_);
lean_dec_ref_known(v_a_2699_, 1);
v_snd_2704_ = lean_ctor_get(v_val_2703_, 1);
lean_inc(v_snd_2704_);
v_fst_2705_ = lean_ctor_get(v_val_2703_, 0);
lean_inc_n(v_fst_2705_, 2);
lean_dec(v_val_2703_);
v_fst_2706_ = lean_ctor_get(v_snd_2704_, 0);
lean_inc_n(v_fst_2706_, 3);
v_snd_2707_ = lean_ctor_get(v_snd_2704_, 1);
lean_inc(v_snd_2707_);
lean_dec(v_snd_2704_);
v___x_2708_ = lean_box(v___x_2695_);
v___x_2709_ = lean_box(v_minIndexable_2433_);
lean_inc_ref(v_params_2429_);
v___f_2710_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed), 13, 6);
lean_closure_set(v___f_2710_, 0, v_params_2429_);
lean_closure_set(v___f_2710_, 1, v_p_2430_);
lean_closure_set(v___f_2710_, 2, v_fst_2705_);
lean_closure_set(v___f_2710_, 3, v_fst_2706_);
lean_closure_set(v___f_2710_, 4, v___x_2708_);
lean_closure_set(v___f_2710_, 5, v___x_2709_);
lean_inc(v___y_2693_);
lean_inc_ref(v___y_2692_);
lean_inc(v___y_2691_);
lean_inc_ref(v___y_2690_);
v___x_2711_ = lean_infer_type(v_fst_2706_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2713_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc_n(v_a_2712_, 2);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2713_ = l_Lean_Meta_isProp(v_a_2712_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; uint8_t v___x_2715_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2713_, 1);
v___x_2715_ = lean_unbox(v_a_2714_);
lean_dec(v_a_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_a_2712_);
lean_dec_ref(v___f_2710_);
lean_dec(v_snd_2707_);
lean_dec(v_fst_2706_);
lean_dec(v_fst_2705_);
lean_dec(v_kind_2687_);
lean_dec(v_mod_x3f_2431_);
lean_dec_ref(v_params_2429_);
v___x_2716_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2717_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2716_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec_ref(v___y_2692_);
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
else
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_unbox(v_snd_2707_);
lean_dec(v_snd_2707_);
v___y_2670_ = v_a_2712_;
v___y_2671_ = v___x_2726_;
v___y_2672_ = v___f_2710_;
v___y_2673_ = v_fst_2705_;
v___y_2674_ = v_fst_2706_;
v___y_2675_ = v_kind_2687_;
v___y_2676_ = v___y_2688_;
v___y_2677_ = v___y_2689_;
v___y_2678_ = v___y_2690_;
v___y_2679_ = v___y_2691_;
v___y_2680_ = v___y_2692_;
v___y_2681_ = v___y_2693_;
goto v___jp_2669_;
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec(v_a_2712_);
lean_dec_ref(v___f_2710_);
lean_dec(v_snd_2707_);
lean_dec(v_fst_2706_);
lean_dec(v_fst_2705_);
lean_dec_ref(v___y_2692_);
lean_dec(v_kind_2687_);
lean_dec(v_mod_x3f_2431_);
lean_dec_ref(v_params_2429_);
v_a_2727_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2713_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2713_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec_ref(v___f_2710_);
lean_dec(v_snd_2707_);
lean_dec(v_fst_2706_);
lean_dec(v_fst_2705_);
lean_dec_ref(v___y_2692_);
lean_dec(v_kind_2687_);
lean_dec(v_mod_x3f_2431_);
lean_dec_ref(v_params_2429_);
v_a_2735_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2711_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2711_);
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
}
else
{
lean_object* v___x_2744_; 
lean_dec(v_a_2699_);
lean_dec_ref(v___y_2692_);
lean_dec(v_kind_2687_);
lean_dec(v_mod_x3f_2431_);
lean_dec(v_p_2430_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 0, v_params_2429_);
v___x_2744_ = v___x_2701_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_params_2429_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec_ref(v___y_2692_);
lean_dec(v_kind_2687_);
lean_dec(v_mod_x3f_2431_);
lean_dec(v_p_2430_);
lean_dec_ref(v_params_2429_);
v_a_2747_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2698_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2698_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
v___jp_2755_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
v___x_2762_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2763_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2762_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec_ref(v___y_2760_);
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
v___jp_2772_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
v___x_2779_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2780_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2779_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec_ref(v___y_2777_);
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
v___jp_2789_:
{
lean_object* v___x_2796_; 
v___x_2796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_kind_2687_ = v___x_2796_;
v___y_2688_ = v___y_2790_;
v___y_2689_ = v___y_2791_;
v___y_2690_ = v___y_2792_;
v___y_2691_ = v___y_2793_;
v___y_2692_ = v___y_2794_;
v___y_2693_ = v___y_2795_;
goto v___jp_2686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2847_, lean_object* v_p_2848_, lean_object* v_mod_x3f_2849_, lean_object* v_term_2850_, lean_object* v_minIndexable_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
uint8_t v_minIndexable_boxed_2859_; lean_object* v_res_2860_; 
v_minIndexable_boxed_2859_ = lean_unbox(v_minIndexable_2851_);
v_res_2860_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2847_, v_p_2848_, v_mod_x3f_2849_, v_term_2850_, v_minIndexable_boxed_2859_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(uint8_t v___x_2861_, uint8_t v___x_2862_, lean_object* v_as_2863_, size_t v_i_2864_, size_t v_stop_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2861_, v___x_2862_, v_as_2863_, v_i_2864_, v_stop_2865_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v___x_2874_, lean_object* v___x_2875_, lean_object* v_as_2876_, lean_object* v_i_2877_, lean_object* v_stop_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v___x_16105__boxed_2886_; uint8_t v___x_16106__boxed_2887_; size_t v_i_boxed_2888_; size_t v_stop_boxed_2889_; lean_object* v_res_2890_; 
v___x_16105__boxed_2886_ = lean_unbox(v___x_2874_);
v___x_16106__boxed_2887_ = lean_unbox(v___x_2875_);
v_i_boxed_2888_ = lean_unbox_usize(v_i_2877_);
lean_dec(v_i_2877_);
v_stop_boxed_2889_ = lean_unbox_usize(v_stop_2878_);
lean_dec(v_stop_2878_);
v_res_2890_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v___x_16105__boxed_2886_, v___x_16106__boxed_2887_, v_as_2876_, v_i_boxed_2888_, v_stop_boxed_2889_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_as_2876_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(lean_object* v_00_u03b1_2891_, lean_object* v_msg_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___boxed(lean_object* v_00_u03b1_2901_, lean_object* v_msg_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(v_00_u03b1_2901_, v_msg_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(lean_object* v_msgData_2911_, lean_object* v_macroStack_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2911_, v_macroStack_2912_, v___y_2917_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___boxed(lean_object* v_msgData_2921_, lean_object* v_macroStack_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(v_msgData_2921_, v_macroStack_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2931_, lean_object* v_val_2932_, lean_object* v___x_2933_, uint8_t v___x_2934_, lean_object* v_____r_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___x_2943_; lean_object* v_ext_2944_; lean_object* v_toEnvExtension_2945_; lean_object* v_env_2946_; lean_object* v_config_2947_; lean_object* v_extensions_2948_; lean_object* v_extra_2949_; lean_object* v_extraInj_2950_; lean_object* v_extraFacts_2951_; lean_object* v_symPrios_2952_; lean_object* v_norm_2953_; lean_object* v_normProcs_2954_; lean_object* v_anchorRefs_x3f_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2967_; 
v___x_2943_ = lean_st_ref_get(v___y_2941_);
v_ext_2944_ = lean_ctor_get(v_val_2932_, 1);
v_toEnvExtension_2945_ = lean_ctor_get(v_ext_2944_, 0);
v_env_2946_ = lean_ctor_get(v___x_2943_, 0);
lean_inc_ref(v_env_2946_);
lean_dec(v___x_2943_);
v_config_2947_ = lean_ctor_get(v_params_2931_, 0);
v_extensions_2948_ = lean_ctor_get(v_params_2931_, 1);
v_extra_2949_ = lean_ctor_get(v_params_2931_, 2);
v_extraInj_2950_ = lean_ctor_get(v_params_2931_, 3);
v_extraFacts_2951_ = lean_ctor_get(v_params_2931_, 4);
v_symPrios_2952_ = lean_ctor_get(v_params_2931_, 5);
v_norm_2953_ = lean_ctor_get(v_params_2931_, 6);
v_normProcs_2954_ = lean_ctor_get(v_params_2931_, 7);
v_anchorRefs_x3f_2955_ = lean_ctor_get(v_params_2931_, 8);
v_isSharedCheck_2967_ = !lean_is_exclusive(v_params_2931_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2957_ = v_params_2931_;
v_isShared_2958_ = v_isSharedCheck_2967_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_anchorRefs_x3f_2955_);
lean_inc(v_normProcs_2954_);
lean_inc(v_norm_2953_);
lean_inc(v_symPrios_2952_);
lean_inc(v_extraFacts_2951_);
lean_inc(v_extraInj_2950_);
lean_inc(v_extra_2949_);
lean_inc(v_extensions_2948_);
lean_inc(v_config_2947_);
lean_dec(v_params_2931_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2967_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v_asyncMode_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2963_; 
v_asyncMode_2959_ = lean_ctor_get(v_toEnvExtension_2945_, 2);
v___x_2960_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2933_, v_val_2932_, v_env_2946_, v_asyncMode_2959_, v___x_2934_);
v___x_2961_ = lean_array_push(v_extensions_2948_, v___x_2960_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 1, v___x_2961_);
v___x_2963_ = v___x_2957_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_config_2947_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v___x_2961_);
lean_ctor_set(v_reuseFailAlloc_2966_, 2, v_extra_2949_);
lean_ctor_set(v_reuseFailAlloc_2966_, 3, v_extraInj_2950_);
lean_ctor_set(v_reuseFailAlloc_2966_, 4, v_extraFacts_2951_);
lean_ctor_set(v_reuseFailAlloc_2966_, 5, v_symPrios_2952_);
lean_ctor_set(v_reuseFailAlloc_2966_, 6, v_norm_2953_);
lean_ctor_set(v_reuseFailAlloc_2966_, 7, v_normProcs_2954_);
lean_ctor_set(v_reuseFailAlloc_2966_, 8, v_anchorRefs_x3f_2955_);
v___x_2963_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2968_, lean_object* v_val_2969_, lean_object* v___x_2970_, lean_object* v___x_2971_, lean_object* v_____r_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
uint8_t v___x_33300__boxed_2980_; lean_object* v_res_2981_; 
v___x_33300__boxed_2980_ = lean_unbox(v___x_2971_);
v_res_2981_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2968_, v_val_2969_, v___x_2970_, v___x_33300__boxed_2980_, v_____r_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec_ref(v___x_2970_);
lean_dec_ref(v_val_2969_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2982_, lean_object* v_id_2983_, uint8_t v_minIndexable_2984_, lean_object* v_as_x27_2985_, lean_object* v_b_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
if (lean_obj_tag(v_as_x27_2985_) == 0)
{
lean_object* v___x_2992_; 
lean_dec(v_id_2983_);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v_b_2986_);
return v___x_2992_;
}
else
{
lean_object* v_head_2993_; lean_object* v_tail_2994_; lean_object* v_toCold_2995_; lean_object* v_currRecDepth_2996_; lean_object* v_ref_2997_; uint16_t v_optionFlags_2998_; uint8_t v_suppressElabErrors_2999_; uint8_t v_checkDeprecated_3000_; uint8_t v_isRecordingDeps_3001_; uint8_t v___x_3002_; lean_object* v___x_3003_; lean_object* v_ref_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_head_2993_ = lean_ctor_get(v_as_x27_2985_, 0);
v_tail_2994_ = lean_ctor_get(v_as_x27_2985_, 1);
v_toCold_2995_ = lean_ctor_get(v___y_2989_, 0);
v_currRecDepth_2996_ = lean_ctor_get(v___y_2989_, 1);
v_ref_2997_ = lean_ctor_get(v___y_2989_, 2);
v_optionFlags_2998_ = lean_ctor_get_uint16(v___y_2989_, sizeof(void*)*3);
v_suppressElabErrors_2999_ = lean_ctor_get_uint8(v___y_2989_, sizeof(void*)*3 + 2);
v_checkDeprecated_3000_ = lean_ctor_get_uint8(v___y_2989_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3001_ = lean_ctor_get_uint8(v___y_2989_, sizeof(void*)*3 + 4);
v___x_3002_ = 0;
v___x_3003_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_ref_3004_ = l_Lean_replaceRef(v_p_2982_, v_ref_2997_);
lean_inc(v_currRecDepth_2996_);
lean_inc_ref(v_toCold_2995_);
v___x_3005_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3005_, 0, v_toCold_2995_);
lean_ctor_set(v___x_3005_, 1, v_currRecDepth_2996_);
lean_ctor_set(v___x_3005_, 2, v_ref_3004_);
lean_ctor_set_uint16(v___x_3005_, sizeof(void*)*3, v_optionFlags_2998_);
lean_ctor_set_uint8(v___x_3005_, sizeof(void*)*3 + 2, v_suppressElabErrors_2999_);
lean_ctor_set_uint8(v___x_3005_, sizeof(void*)*3 + 3, v_checkDeprecated_3000_);
lean_ctor_set_uint8(v___x_3005_, sizeof(void*)*3 + 4, v_isRecordingDeps_3001_);
lean_inc(v_head_2993_);
lean_inc(v_id_2983_);
v___x_3006_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2986_, v_id_2983_, v_head_2993_, v___x_3003_, v_minIndexable_2984_, v___x_3002_, v___x_3002_, v___y_2987_, v___y_2988_, v___x_3005_, v___y_2990_);
lean_dec_ref_known(v___x_3005_, 3);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v_as_x27_2985_ = v_tail_2994_;
v_b_2986_ = v_a_3007_;
goto _start;
}
else
{
lean_dec(v_id_2983_);
return v___x_3006_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_3009_, lean_object* v_id_3010_, lean_object* v_minIndexable_3011_, lean_object* v_as_x27_3012_, lean_object* v_b_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
uint8_t v_minIndexable_boxed_3019_; lean_object* v_res_3020_; 
v_minIndexable_boxed_3019_ = lean_unbox(v_minIndexable_3011_);
v_res_3020_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3009_, v_id_3010_, v_minIndexable_boxed_3019_, v_as_x27_3012_, v_b_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v_as_x27_3012_);
lean_dec(v_p_3009_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
if (lean_obj_tag(v_a_3022_) == 0)
{
lean_object* v___x_3024_; 
v___x_3024_ = l_List_reverse___redArg(v_a_3023_);
return v___x_3024_;
}
else
{
lean_object* v_head_3025_; lean_object* v_tail_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3037_; 
v_head_3025_ = lean_ctor_get(v_a_3022_, 0);
v_tail_3026_ = lean_ctor_get(v_a_3022_, 1);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_a_3022_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3028_ = v_a_3022_;
v_isShared_3029_ = v_isSharedCheck_3037_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_tail_3026_);
lean_inc(v_head_3025_);
lean_dec(v_a_3022_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3037_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v_kind_3030_; uint8_t v___x_3031_; 
v_kind_3030_ = lean_ctor_get(v_head_3025_, 6);
v___x_3031_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_3030_, v_k_3021_);
if (v___x_3031_ == 0)
{
lean_del_object(v___x_3028_);
lean_dec(v_head_3025_);
v_a_3022_ = v_tail_3026_;
goto _start;
}
else
{
lean_object* v___x_3034_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v_a_3023_);
v___x_3034_ = v___x_3028_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_head_3025_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_a_3023_);
v___x_3034_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
v_a_3022_ = v_tail_3026_;
v_a_3023_ = v___x_3034_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_3038_, v_a_3039_, v_a_3040_);
lean_dec(v_k_3038_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_3042_, lean_object* v_msg_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v_toCold_3051_; lean_object* v_currRecDepth_3052_; lean_object* v_ref_3053_; uint16_t v_optionFlags_3054_; uint8_t v_suppressElabErrors_3055_; uint8_t v_checkDeprecated_3056_; uint8_t v_isRecordingDeps_3057_; lean_object* v_ref_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v_toCold_3051_ = lean_ctor_get(v___y_3048_, 0);
v_currRecDepth_3052_ = lean_ctor_get(v___y_3048_, 1);
v_ref_3053_ = lean_ctor_get(v___y_3048_, 2);
v_optionFlags_3054_ = lean_ctor_get_uint16(v___y_3048_, sizeof(void*)*3);
v_suppressElabErrors_3055_ = lean_ctor_get_uint8(v___y_3048_, sizeof(void*)*3 + 2);
v_checkDeprecated_3056_ = lean_ctor_get_uint8(v___y_3048_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3057_ = lean_ctor_get_uint8(v___y_3048_, sizeof(void*)*3 + 4);
v_ref_3058_ = l_Lean_replaceRef(v_ref_3042_, v_ref_3053_);
lean_inc(v_currRecDepth_3052_);
lean_inc_ref(v_toCold_3051_);
v___x_3059_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3059_, 0, v_toCold_3051_);
lean_ctor_set(v___x_3059_, 1, v_currRecDepth_3052_);
lean_ctor_set(v___x_3059_, 2, v_ref_3058_);
lean_ctor_set_uint16(v___x_3059_, sizeof(void*)*3, v_optionFlags_3054_);
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*3 + 2, v_suppressElabErrors_3055_);
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*3 + 3, v_checkDeprecated_3056_);
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*3 + 4, v_isRecordingDeps_3057_);
v___x_3060_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___x_3059_, v___y_3049_);
lean_dec_ref_known(v___x_3059_, 3);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_3061_, lean_object* v_msg_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_3061_, v_msg_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v_ref_3061_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_3071_, lean_object* v_id_3072_, uint8_t v_minIndexable_3073_, lean_object* v_as_x27_3074_, lean_object* v_b_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
if (lean_obj_tag(v_as_x27_3074_) == 0)
{
lean_object* v___x_3081_; 
lean_dec(v_id_3072_);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v_b_3075_);
return v___x_3081_;
}
else
{
lean_object* v_head_3082_; lean_object* v_tail_3083_; lean_object* v_toCold_3084_; lean_object* v_currRecDepth_3085_; lean_object* v_ref_3086_; uint16_t v_optionFlags_3087_; uint8_t v_suppressElabErrors_3088_; uint8_t v_checkDeprecated_3089_; uint8_t v_isRecordingDeps_3090_; uint8_t v___x_3091_; uint8_t v___x_3092_; lean_object* v___x_3093_; lean_object* v_ref_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v_head_3082_ = lean_ctor_get(v_as_x27_3074_, 0);
v_tail_3083_ = lean_ctor_get(v_as_x27_3074_, 1);
v_toCold_3084_ = lean_ctor_get(v___y_3078_, 0);
v_currRecDepth_3085_ = lean_ctor_get(v___y_3078_, 1);
v_ref_3086_ = lean_ctor_get(v___y_3078_, 2);
v_optionFlags_3087_ = lean_ctor_get_uint16(v___y_3078_, sizeof(void*)*3);
v_suppressElabErrors_3088_ = lean_ctor_get_uint8(v___y_3078_, sizeof(void*)*3 + 2);
v_checkDeprecated_3089_ = lean_ctor_get_uint8(v___y_3078_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3090_ = lean_ctor_get_uint8(v___y_3078_, sizeof(void*)*3 + 4);
v___x_3091_ = 0;
v___x_3092_ = 1;
v___x_3093_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_ref_3094_ = l_Lean_replaceRef(v_p_3071_, v_ref_3086_);
lean_inc(v_currRecDepth_3085_);
lean_inc_ref(v_toCold_3084_);
v___x_3095_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3095_, 0, v_toCold_3084_);
lean_ctor_set(v___x_3095_, 1, v_currRecDepth_3085_);
lean_ctor_set(v___x_3095_, 2, v_ref_3094_);
lean_ctor_set_uint16(v___x_3095_, sizeof(void*)*3, v_optionFlags_3087_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*3 + 2, v_suppressElabErrors_3088_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*3 + 3, v_checkDeprecated_3089_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*3 + 4, v_isRecordingDeps_3090_);
lean_inc(v_head_3082_);
lean_inc(v_id_3072_);
v___x_3096_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_3075_, v_id_3072_, v_head_3082_, v___x_3093_, v_minIndexable_3073_, v___x_3091_, v___x_3092_, v___y_3076_, v___y_3077_, v___x_3095_, v___y_3079_);
lean_dec_ref_known(v___x_3095_, 3);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
lean_dec_ref_known(v___x_3096_, 1);
v_as_x27_3074_ = v_tail_3083_;
v_b_3075_ = v_a_3097_;
goto _start;
}
else
{
lean_dec(v_id_3072_);
return v___x_3096_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_3099_, lean_object* v_id_3100_, lean_object* v_minIndexable_3101_, lean_object* v_as_x27_3102_, lean_object* v_b_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
uint8_t v_minIndexable_boxed_3109_; lean_object* v_res_3110_; 
v_minIndexable_boxed_3109_ = lean_unbox(v_minIndexable_3101_);
v_res_3110_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3099_, v_id_3100_, v_minIndexable_boxed_3109_, v_as_x27_3102_, v_b_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v_as_x27_3102_);
lean_dec(v_p_3099_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_3111_){
_start:
{
if (lean_obj_tag(v_x_3111_) == 0)
{
lean_object* v___x_3112_; 
v___x_3112_ = lean_box(0);
return v___x_3112_;
}
else
{
lean_object* v_head_3113_; lean_object* v_tail_3114_; lean_object* v_fst_3115_; uint8_t v___x_3116_; 
v_head_3113_ = lean_ctor_get(v_x_3111_, 0);
v_tail_3114_ = lean_ctor_get(v_x_3111_, 1);
v_fst_3115_ = lean_ctor_get(v_head_3113_, 0);
v___x_3116_ = l_Lean_isPrivateName(v_fst_3115_);
if (v___x_3116_ == 0)
{
v_x_3111_ = v_tail_3114_;
goto _start;
}
else
{
lean_object* v___x_3118_; 
lean_inc(v_head_3113_);
v___x_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3118_, 0, v_head_3113_);
return v___x_3118_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_3119_);
lean_dec(v_x_3119_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_3121_, lean_object* v_msgData_3122_, uint8_t v_severity_3123_, uint8_t v_isSilent_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; uint8_t v___y_3134_; lean_object* v___y_3135_; uint8_t v___y_3136_; lean_object* v___y_3137_; lean_object* v_toCold_3138_; lean_object* v___y_3139_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; uint8_t v___y_3171_; uint8_t v___y_3172_; lean_object* v___y_3173_; uint8_t v___y_3174_; lean_object* v___y_3175_; uint8_t v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; uint8_t v___y_3198_; lean_object* v___y_3199_; uint8_t v___y_3200_; lean_object* v___y_3201_; uint8_t v___y_3205_; uint8_t v___y_3206_; uint8_t v___x_3216_; uint8_t v___y_3218_; uint8_t v___x_3224_; 
v___x_3216_ = 2;
v___x_3224_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3123_, v___x_3216_);
if (v___x_3224_ == 0)
{
v___y_3218_ = v___x_3224_;
goto v___jp_3217_;
}
else
{
uint8_t v___x_3225_; 
lean_inc_ref(v_msgData_3122_);
v___x_3225_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3122_);
if (v___x_3225_ == 0)
{
v___y_3218_ = v___x_3225_;
goto v___jp_3217_;
}
else
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_dec_ref(v_msgData_3122_);
v___x_3226_ = lean_box(0);
v___x_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
return v___x_3227_;
}
}
v___jp_3130_:
{
lean_object* v_currNamespace_3140_; lean_object* v_openDecls_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v_env_3146_; lean_object* v_nextMacroScope_3147_; lean_object* v_ngen_3148_; lean_object* v_auxDeclNGen_3149_; lean_object* v_traceState_3150_; lean_object* v_cache_3151_; lean_object* v_recordedDeps_3152_; lean_object* v_messages_3153_; lean_object* v_infoState_3154_; lean_object* v_snapshotTasks_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3166_; 
v_currNamespace_3140_ = lean_ctor_get(v_toCold_3138_, 4);
v_openDecls_3141_ = lean_ctor_get(v_toCold_3138_, 5);
lean_inc(v_openDecls_3141_);
lean_inc(v_currNamespace_3140_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_currNamespace_3140_);
lean_ctor_set(v___x_3142_, 1, v_openDecls_3141_);
v___x_3143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
lean_ctor_set(v___x_3143_, 1, v___y_3131_);
lean_inc_ref(v___y_3132_);
lean_inc_ref(v___y_3133_);
v___x_3144_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3144_, 0, v___y_3133_);
lean_ctor_set(v___x_3144_, 1, v___y_3135_);
lean_ctor_set(v___x_3144_, 2, v___y_3137_);
lean_ctor_set(v___x_3144_, 3, v___y_3132_);
lean_ctor_set(v___x_3144_, 4, v___x_3143_);
lean_ctor_set_uint8(v___x_3144_, sizeof(void*)*5, v___y_3134_);
lean_ctor_set_uint8(v___x_3144_, sizeof(void*)*5 + 1, v___y_3136_);
lean_ctor_set_uint8(v___x_3144_, sizeof(void*)*5 + 2, v_isSilent_3124_);
v___x_3145_ = lean_st_ref_take(v___y_3139_);
v_env_3146_ = lean_ctor_get(v___x_3145_, 0);
v_nextMacroScope_3147_ = lean_ctor_get(v___x_3145_, 1);
v_ngen_3148_ = lean_ctor_get(v___x_3145_, 2);
v_auxDeclNGen_3149_ = lean_ctor_get(v___x_3145_, 3);
v_traceState_3150_ = lean_ctor_get(v___x_3145_, 4);
v_cache_3151_ = lean_ctor_get(v___x_3145_, 5);
v_recordedDeps_3152_ = lean_ctor_get(v___x_3145_, 6);
v_messages_3153_ = lean_ctor_get(v___x_3145_, 7);
v_infoState_3154_ = lean_ctor_get(v___x_3145_, 8);
v_snapshotTasks_3155_ = lean_ctor_get(v___x_3145_, 9);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3157_ = v___x_3145_;
v_isShared_3158_ = v_isSharedCheck_3166_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_snapshotTasks_3155_);
lean_inc(v_infoState_3154_);
lean_inc(v_messages_3153_);
lean_inc(v_recordedDeps_3152_);
lean_inc(v_cache_3151_);
lean_inc(v_traceState_3150_);
lean_inc(v_auxDeclNGen_3149_);
lean_inc(v_ngen_3148_);
lean_inc(v_nextMacroScope_3147_);
lean_inc(v_env_3146_);
lean_dec(v___x_3145_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3166_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3159_ = lean_box(0);
v___x_3160_ = l_Lean_MessageLog_add(v___x_3144_, v_messages_3153_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 7, v___x_3160_);
v___x_3162_ = v___x_3157_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_env_3146_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_nextMacroScope_3147_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_ngen_3148_);
lean_ctor_set(v_reuseFailAlloc_3165_, 3, v_auxDeclNGen_3149_);
lean_ctor_set(v_reuseFailAlloc_3165_, 4, v_traceState_3150_);
lean_ctor_set(v_reuseFailAlloc_3165_, 5, v_cache_3151_);
lean_ctor_set(v_reuseFailAlloc_3165_, 6, v_recordedDeps_3152_);
lean_ctor_set(v_reuseFailAlloc_3165_, 7, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3165_, 8, v_infoState_3154_);
lean_ctor_set(v_reuseFailAlloc_3165_, 9, v_snapshotTasks_3155_);
v___x_3162_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = lean_st_ref_put(v___y_3139_, v___x_3162_);
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3159_);
return v___x_3164_;
}
}
}
v___jp_3167_:
{
lean_object* v_fileName_3176_; lean_object* v_fileMap_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3193_; 
v_fileName_3176_ = lean_ctor_get(v___y_3173_, 0);
v_fileMap_3177_ = lean_ctor_get(v___y_3173_, 1);
v___x_3178_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3122_);
v___x_3179_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_3178_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3182_ = v___x_3179_;
v_isShared_3183_ = v_isSharedCheck_3193_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3179_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3193_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_inc_ref_n(v_fileMap_3177_, 2);
v___x_3184_ = l_Lean_FileMap_toPosition(v_fileMap_3177_, v___y_3170_);
lean_dec(v___y_3170_);
v___x_3185_ = l_Lean_FileMap_toPosition(v_fileMap_3177_, v___y_3175_);
lean_dec(v___y_3175_);
v___x_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
v___x_3187_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_3171_ == 0)
{
lean_del_object(v___x_3182_);
lean_dec_ref(v___y_3169_);
v___y_3131_ = v_a_3180_;
v___y_3132_ = v___x_3187_;
v___y_3133_ = v_fileName_3176_;
v___y_3134_ = v___y_3172_;
v___y_3135_ = v___x_3184_;
v___y_3136_ = v___y_3174_;
v___y_3137_ = v___x_3186_;
v_toCold_3138_ = v___y_3168_;
v___y_3139_ = v___y_3128_;
goto v___jp_3130_;
}
else
{
uint8_t v___x_3188_; 
lean_inc(v_a_3180_);
v___x_3188_ = l_Lean_MessageData_hasTag(v___y_3169_, v_a_3180_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
lean_dec_ref_known(v___x_3186_, 1);
lean_dec_ref(v___x_3184_);
lean_dec(v_a_3180_);
v___x_3189_ = lean_box(0);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___x_3189_);
v___x_3191_ = v___x_3182_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
else
{
lean_del_object(v___x_3182_);
v___y_3131_ = v_a_3180_;
v___y_3132_ = v___x_3187_;
v___y_3133_ = v_fileName_3176_;
v___y_3134_ = v___y_3172_;
v___y_3135_ = v___x_3184_;
v___y_3136_ = v___y_3174_;
v___y_3137_ = v___x_3186_;
v_toCold_3138_ = v___y_3168_;
v___y_3139_ = v___y_3128_;
goto v___jp_3130_;
}
}
}
}
v___jp_3194_:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_Lean_Syntax_getTailPos_x3f(v___y_3199_, v___y_3198_);
lean_dec(v___y_3199_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_inc(v___y_3201_);
v___y_3168_ = v___y_3196_;
v___y_3169_ = v___y_3197_;
v___y_3170_ = v___y_3201_;
v___y_3171_ = v___y_3195_;
v___y_3172_ = v___y_3198_;
v___y_3173_ = v___y_3196_;
v___y_3174_ = v___y_3200_;
v___y_3175_ = v___y_3201_;
goto v___jp_3167_;
}
else
{
lean_object* v_val_3203_; 
v_val_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_val_3203_);
lean_dec_ref_known(v___x_3202_, 1);
v___y_3168_ = v___y_3196_;
v___y_3169_ = v___y_3197_;
v___y_3170_ = v___y_3201_;
v___y_3171_ = v___y_3195_;
v___y_3172_ = v___y_3198_;
v___y_3173_ = v___y_3196_;
v___y_3174_ = v___y_3200_;
v___y_3175_ = v_val_3203_;
goto v___jp_3167_;
}
}
v___jp_3204_:
{
lean_object* v_toCold_3207_; lean_object* v_ref_3208_; uint8_t v_suppressElabErrors_3209_; lean_object* v___x_3210_; lean_object* v___f_3211_; lean_object* v_ref_3212_; lean_object* v___x_3213_; 
v_toCold_3207_ = lean_ctor_get(v___y_3127_, 0);
v_ref_3208_ = lean_ctor_get(v___y_3127_, 2);
v_suppressElabErrors_3209_ = lean_ctor_get_uint8(v___y_3127_, sizeof(void*)*3 + 2);
v___x_3210_ = lean_box(v_suppressElabErrors_3209_);
v___f_3211_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3211_, 0, v___x_3210_);
v_ref_3212_ = l_Lean_replaceRef(v_ref_3121_, v_ref_3208_);
v___x_3213_ = l_Lean_Syntax_getPos_x3f(v_ref_3212_, v___y_3205_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_unsigned_to_nat(0u);
v___y_3195_ = v_suppressElabErrors_3209_;
v___y_3196_ = v_toCold_3207_;
v___y_3197_ = v___f_3211_;
v___y_3198_ = v___y_3205_;
v___y_3199_ = v_ref_3212_;
v___y_3200_ = v___y_3206_;
v___y_3201_ = v___x_3214_;
goto v___jp_3194_;
}
else
{
lean_object* v_val_3215_; 
v_val_3215_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_val_3215_);
lean_dec_ref_known(v___x_3213_, 1);
v___y_3195_ = v_suppressElabErrors_3209_;
v___y_3196_ = v_toCold_3207_;
v___y_3197_ = v___f_3211_;
v___y_3198_ = v___y_3205_;
v___y_3199_ = v_ref_3212_;
v___y_3200_ = v___y_3206_;
v___y_3201_ = v_val_3215_;
goto v___jp_3194_;
}
}
v___jp_3217_:
{
uint8_t v___x_3219_; uint8_t v___x_3220_; 
v___x_3219_ = 1;
v___x_3220_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3123_, v___x_3219_);
if (v___x_3220_ == 0)
{
v___y_3205_ = v___y_3218_;
v___y_3206_ = v_severity_3123_;
goto v___jp_3204_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; 
v___x_3221_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3127_);
v___x_3222_ = l_Lean_warningAsError;
v___x_3223_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3221_, v___x_3222_);
lean_dec_ref(v___x_3221_);
if (v___x_3223_ == 0)
{
v___y_3205_ = v___y_3218_;
v___y_3206_ = v_severity_3123_;
goto v___jp_3204_;
}
else
{
v___y_3205_ = v___y_3218_;
v___y_3206_ = v___x_3216_;
goto v___jp_3204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_3228_, lean_object* v_msgData_3229_, lean_object* v_severity_3230_, lean_object* v_isSilent_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
uint8_t v_severity_boxed_3237_; uint8_t v_isSilent_boxed_3238_; lean_object* v_res_3239_; 
v_severity_boxed_3237_ = lean_unbox(v_severity_3230_);
v_isSilent_boxed_3238_ = lean_unbox(v_isSilent_3231_);
v_res_3239_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3228_, v_msgData_3229_, v_severity_boxed_3237_, v_isSilent_boxed_3238_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v_ref_3228_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_3240_, uint8_t v_severity_3241_, uint8_t v_isSilent_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_ref_3250_; lean_object* v___x_3251_; 
v_ref_3250_ = lean_ctor_get(v___y_3247_, 2);
v___x_3251_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3250_, v_msgData_3240_, v_severity_3241_, v_isSilent_3242_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_3252_, lean_object* v_severity_3253_, lean_object* v_isSilent_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
uint8_t v_severity_boxed_3262_; uint8_t v_isSilent_boxed_3263_; lean_object* v_res_3264_; 
v_severity_boxed_3262_ = lean_unbox(v_severity_3253_);
v_isSilent_boxed_3263_ = lean_unbox(v_isSilent_3254_);
v_res_3264_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3252_, v_severity_boxed_3262_, v_isSilent_boxed_3263_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
uint8_t v___x_3273_; uint8_t v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = 1;
v___x_3274_ = 0;
v___x_3275_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3265_, v___x_3273_, v___x_3274_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___x_3288_; uint8_t v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3288_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3286_);
v___x_3289_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3288_, v_opt_3285_);
lean_dec_ref(v___x_3288_);
v___x_3290_ = lean_box(v___x_3289_);
v___x_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3292_, v___y_3293_);
lean_dec_ref(v___y_3293_);
lean_dec_ref(v_opt_3292_);
return v_res_3295_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3298_ = l_Lean_stringToMessageData(v___x_3297_);
return v___x_3298_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3301_ = l_Lean_stringToMessageData(v___x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v___x_3310_; lean_object* v_env_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3333_; 
v___x_3310_ = lean_st_ref_get(v___y_3308_);
v_env_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc_ref(v_env_3311_);
lean_dec(v___x_3310_);
v___x_3312_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3313_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3312_, v___y_3307_);
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3316_ = v___x_3313_;
v_isShared_3317_ = v_isSharedCheck_3333_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3333_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
uint8_t v_isExporting_3323_; 
v_isExporting_3323_ = lean_ctor_get_uint8(v_env_3311_, sizeof(void*)*13);
lean_dec_ref(v_env_3311_);
if (v_isExporting_3323_ == 0)
{
lean_dec(v_a_3314_);
lean_dec(v_id_3302_);
goto v___jp_3318_;
}
else
{
uint8_t v___x_3324_; 
v___x_3324_ = l_Lean_isPrivateName(v_id_3302_);
if (v___x_3324_ == 0)
{
lean_dec(v_a_3314_);
lean_dec(v_id_3302_);
goto v___jp_3318_;
}
else
{
uint8_t v___x_3325_; 
v___x_3325_ = lean_unbox(v_a_3314_);
lean_dec(v_a_3314_);
if (v___x_3325_ == 0)
{
lean_dec(v_id_3302_);
goto v___jp_3318_;
}
else
{
lean_object* v___x_3326_; uint8_t v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
lean_del_object(v___x_3316_);
v___x_3326_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3327_ = 0;
v___x_3328_ = l_Lean_MessageData_ofConstName(v_id_3302_, v___x_3327_);
v___x_3329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3326_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3329_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
v___x_3332_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3331_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
return v___x_3332_;
}
}
}
v___jp_3318_:
{
lean_object* v___x_3319_; lean_object* v___x_3321_; 
v___x_3319_ = lean_box(0);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v___x_3319_);
v___x_3321_ = v___x_3316_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3343_, uint8_t v_enableLog_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v___x_3352_; lean_object* v_toCold_3353_; lean_object* v_env_3354_; lean_object* v_currNamespace_3355_; lean_object* v_openDecls_3356_; lean_object* v___x_3357_; lean_object* v_res_3358_; lean_object* v___x_3359_; 
v___x_3352_ = lean_st_ref_get(v___y_3350_);
v_toCold_3353_ = lean_ctor_get(v___y_3349_, 0);
v_env_3354_ = lean_ctor_get(v___x_3352_, 0);
lean_inc_ref(v_env_3354_);
lean_dec(v___x_3352_);
v_currNamespace_3355_ = lean_ctor_get(v_toCold_3353_, 4);
v_openDecls_3356_ = lean_ctor_get(v_toCold_3353_, 5);
v___x_3357_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3349_);
lean_inc(v_openDecls_3356_);
lean_inc(v_currNamespace_3355_);
v_res_3358_ = l_Lean_ResolveName_resolveGlobalName(v_env_3354_, v___x_3357_, v_currNamespace_3355_, v_openDecls_3356_, v_id_3343_);
lean_dec_ref(v___x_3357_);
v___x_3359_ = lean_st_ref_get(v___y_3350_);
if (v_enableLog_3344_ == 0)
{
lean_object* v___x_3360_; 
lean_dec(v___x_3359_);
v___x_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3360_, 0, v_res_3358_);
return v___x_3360_;
}
else
{
lean_object* v_env_3361_; uint8_t v_isExporting_3362_; 
v_env_3361_ = lean_ctor_get(v___x_3359_, 0);
lean_inc_ref(v_env_3361_);
lean_dec(v___x_3359_);
v_isExporting_3362_ = lean_ctor_get_uint8(v_env_3361_, sizeof(void*)*13);
lean_dec_ref(v_env_3361_);
if (v_isExporting_3362_ == 0)
{
lean_object* v___x_3363_; 
v___x_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3363_, 0, v_res_3358_);
return v___x_3363_;
}
else
{
lean_object* v___x_3364_; 
v___x_3364_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3358_);
if (lean_obj_tag(v___x_3364_) == 1)
{
lean_object* v_val_3365_; lean_object* v_fst_3366_; lean_object* v___x_3367_; 
v_val_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_val_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v_fst_3366_ = lean_ctor_get(v_val_3365_, 0);
lean_inc(v_fst_3366_);
lean_dec(v_val_3365_);
v___x_3367_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3366_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3374_ == 0)
{
lean_object* v_unused_3375_; 
v_unused_3375_ = lean_ctor_get(v___x_3367_, 0);
lean_dec(v_unused_3375_);
v___x_3369_ = v___x_3367_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_dec(v___x_3367_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v_res_3358_);
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_res_3358_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec(v_res_3358_);
v_a_3376_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3367_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3367_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
else
{
lean_object* v___x_3384_; 
lean_dec(v___x_3364_);
v___x_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_res_3358_);
return v___x_3384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3385_, lean_object* v_enableLog_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
uint8_t v_enableLog_boxed_3394_; lean_object* v_res_3395_; 
v_enableLog_boxed_3394_ = lean_unbox(v_enableLog_3386_);
v_res_3395_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3385_, v_enableLog_boxed_3394_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
return v_res_3395_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_snd_3396_, lean_object* v_x_3397_){
_start:
{
if (lean_obj_tag(v_x_3397_) == 0)
{
uint8_t v___x_3398_; 
v___x_3398_ = 0;
return v___x_3398_;
}
else
{
lean_object* v_head_3399_; lean_object* v_tail_3400_; lean_object* v_snd_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v_head_3399_ = lean_ctor_get(v_x_3397_, 0);
v_tail_3400_ = lean_ctor_get(v_x_3397_, 1);
v_snd_3401_ = lean_ctor_get(v_head_3399_, 1);
v___x_3402_ = l_List_lengthTR___redArg(v_snd_3401_);
v___x_3403_ = l_List_lengthTR___redArg(v_snd_3396_);
v___x_3404_ = lean_nat_dec_lt(v___x_3402_, v___x_3403_);
lean_dec(v___x_3403_);
lean_dec(v___x_3402_);
if (v___x_3404_ == 0)
{
v_x_3397_ = v_tail_3400_;
goto _start;
}
else
{
return v___x_3404_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14___boxed(lean_object* v_snd_3406_, lean_object* v_x_3407_){
_start:
{
uint8_t v_res_3408_; lean_object* v_r_3409_; 
v_res_3408_ = l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_snd_3406_, v_x_3407_);
lean_dec(v_x_3407_);
lean_dec(v_snd_3406_);
v_r_3409_ = lean_box(v_res_3408_);
return v_r_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3410_, lean_object* v_findLocalDecl_x3f_3411_, lean_object* v_n_3412_, lean_object* v_projs_3413_, lean_object* v_auxDecl_x3f_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v_auxDecl_x3f_3430_; lean_object* v_imported_3461_; lean_object* v_ctx_3462_; lean_object* v_scopes_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v_imported_3461_ = lean_ctor_get(v_view_3410_, 1);
v_ctx_3462_ = lean_ctor_get(v_view_3410_, 2);
v_scopes_3463_ = lean_ctor_get(v_view_3410_, 3);
lean_inc(v_scopes_3463_);
lean_inc(v_ctx_3462_);
lean_inc(v_imported_3461_);
lean_inc(v_n_3412_);
v___x_3464_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3464_, 0, v_n_3412_);
lean_ctor_set(v___x_3464_, 1, v_imported_3461_);
lean_ctor_set(v___x_3464_, 2, v_ctx_3462_);
lean_ctor_set(v___x_3464_, 3, v_scopes_3463_);
lean_inc_ref(v_findLocalDecl_x3f_3411_);
v___x_3465_ = lean_apply_1(v_findLocalDecl_x3f_3411_, v___x_3464_);
if (lean_obj_tag(v___x_3465_) == 1)
{
lean_object* v_val_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3481_; 
v_val_3466_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3468_ = v___x_3465_;
v_isShared_3469_ = v_isSharedCheck_3481_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_val_3466_);
lean_dec(v___x_3465_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3481_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
uint8_t v___x_3470_; 
v___x_3470_ = l_Lean_LocalDecl_isAuxDecl(v_val_3466_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3474_; 
lean_dec(v_auxDecl_x3f_3414_);
lean_dec(v_n_3412_);
lean_dec_ref(v_findLocalDecl_x3f_3411_);
lean_dec_ref(v_view_3410_);
v___x_3471_ = l_Lean_LocalDecl_toExpr(v_val_3466_);
v___x_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
lean_ctor_set(v___x_3472_, 1, v_projs_3413_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3472_);
v___x_3474_ = v___x_3468_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3472_);
v___x_3474_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3475_; 
v___x_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
return v___x_3475_;
}
}
else
{
if (lean_obj_tag(v_auxDecl_x3f_3414_) == 0)
{
lean_object* v___x_3477_; lean_object* v___x_3479_; 
lean_inc(v_projs_3413_);
v___x_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3477_, 0, v_val_3466_);
lean_ctor_set(v___x_3477_, 1, v_projs_3413_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3477_);
v___x_3479_ = v___x_3468_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
v_auxDecl_x3f_3430_ = v___x_3479_;
goto v___jp_3429_;
}
}
else
{
lean_del_object(v___x_3468_);
lean_dec(v_val_3466_);
v_auxDecl_x3f_3430_ = v_auxDecl_x3f_3414_;
goto v___jp_3429_;
}
}
}
}
else
{
lean_dec(v___x_3465_);
v_auxDecl_x3f_3430_ = v_auxDecl_x3f_3414_;
goto v___jp_3429_;
}
v___jp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3425_ = l_Lean_LocalDecl_toExpr(v___y_3423_);
v___x_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
lean_ctor_set(v___x_3426_, 1, v___y_3424_);
v___x_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
v___x_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
return v___x_3428_;
}
v___jp_3429_:
{
if (lean_obj_tag(v_n_3412_) == 1)
{
lean_object* v_pre_3431_; lean_object* v_str_3432_; lean_object* v___x_3433_; 
v_pre_3431_ = lean_ctor_get(v_n_3412_, 0);
lean_inc(v_pre_3431_);
v_str_3432_ = lean_ctor_get(v_n_3412_, 1);
lean_inc_ref(v_str_3432_);
lean_dec_ref_known(v_n_3412_, 2);
v___x_3433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3433_, 0, v_str_3432_);
lean_ctor_set(v___x_3433_, 1, v_projs_3413_);
v_n_3412_ = v_pre_3431_;
v_projs_3413_ = v___x_3433_;
v_auxDecl_x3f_3414_ = v_auxDecl_x3f_3430_;
goto _start;
}
else
{
lean_dec(v_projs_3413_);
lean_dec(v_n_3412_);
lean_dec_ref(v_findLocalDecl_x3f_3411_);
if (lean_obj_tag(v_auxDecl_x3f_3430_) == 1)
{
lean_object* v_val_3435_; lean_object* v_fst_3436_; lean_object* v_snd_3437_; uint8_t v___x_3438_; 
v_val_3435_ = lean_ctor_get(v_auxDecl_x3f_3430_, 0);
lean_inc(v_val_3435_);
lean_dec_ref_known(v_auxDecl_x3f_3430_, 1);
v_fst_3436_ = lean_ctor_get(v_val_3435_, 0);
lean_inc(v_fst_3436_);
v_snd_3437_ = lean_ctor_get(v_val_3435_, 1);
lean_inc(v_snd_3437_);
lean_dec(v_val_3435_);
v___x_3438_ = l_List_isEmpty___redArg(v_snd_3437_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = l_Lean_MacroScopesView_review(v_view_3410_);
v___x_3440_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3439_, v___x_3438_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3450_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3450_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3450_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
uint8_t v___x_3445_; 
v___x_3445_ = l_List_any___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_snd_3437_, v_a_3441_);
lean_dec(v_a_3441_);
if (v___x_3445_ == 0)
{
lean_del_object(v___x_3443_);
v___y_3423_ = v_fst_3436_;
v___y_3424_ = v_snd_3437_;
goto v___jp_3422_;
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3448_; 
lean_dec(v_snd_3437_);
lean_dec(v_fst_3436_);
v___x_3446_ = lean_box(0);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3446_);
v___x_3448_ = v___x_3443_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec(v_snd_3437_);
lean_dec(v_fst_3436_);
v_a_3451_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3440_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3440_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
else
{
lean_dec_ref(v_view_3410_);
v___y_3423_ = v_fst_3436_;
v___y_3424_ = v_snd_3437_;
goto v___jp_3422_;
}
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
lean_dec(v_auxDecl_x3f_3430_);
lean_dec_ref(v_view_3410_);
v___x_3459_ = lean_box(0);
v___x_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
return v___x_3460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3482_, lean_object* v_findLocalDecl_x3f_3483_, lean_object* v_n_3484_, lean_object* v_projs_3485_, lean_object* v_auxDecl_x3f_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3482_, v_findLocalDecl_x3f_3483_, v_n_3484_, v_projs_3485_, v_auxDecl_x3f_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3495_, lean_object* v_givenName_3496_, lean_object* v_as_3497_, lean_object* v_i_3498_){
_start:
{
lean_object* v_zero_3499_; uint8_t v_isZero_3500_; 
v_zero_3499_ = lean_unsigned_to_nat(0u);
v_isZero_3500_ = lean_nat_dec_eq(v_i_3498_, v_zero_3499_);
if (v_isZero_3500_ == 1)
{
lean_object* v___x_3501_; 
lean_dec(v_i_3498_);
v___x_3501_ = lean_box(0);
return v___x_3501_;
}
else
{
lean_object* v_one_3502_; lean_object* v_n_3503_; lean_object* v___x_3504_; 
v_one_3502_ = lean_unsigned_to_nat(1u);
v_n_3503_ = lean_nat_sub(v_i_3498_, v_one_3502_);
lean_dec(v_i_3498_);
v___x_3504_ = lean_array_fget_borrowed(v_as_3497_, v_n_3503_);
if (lean_obj_tag(v___x_3504_) == 0)
{
v_i_3498_ = v_n_3503_;
goto _start;
}
else
{
lean_object* v_val_3506_; uint8_t v___x_3507_; 
v_val_3506_ = lean_ctor_get(v___x_3504_, 0);
v___x_3507_ = l_Lean_LocalDecl_isAuxDecl(v_val_3506_);
if (v___x_3507_ == 0)
{
if (lean_obj_tag(v_localDecl_x3f_3495_) == 0)
{
v_i_3498_ = v_n_3503_;
goto _start;
}
else
{
lean_dec(v_n_3503_);
lean_inc_ref(v_localDecl_x3f_3495_);
return v_localDecl_x3f_3495_;
}
}
else
{
lean_object* v___x_3509_; uint8_t v___x_3510_; 
v___x_3509_ = l_Lean_LocalDecl_userName(v_val_3506_);
v___x_3510_ = lean_name_eq(v___x_3509_, v_givenName_3496_);
lean_dec(v___x_3509_);
if (v___x_3510_ == 0)
{
v_i_3498_ = v_n_3503_;
goto _start;
}
else
{
lean_dec(v_n_3503_);
lean_inc_ref(v___x_3504_);
return v___x_3504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3512_, lean_object* v_givenName_3513_, lean_object* v_as_3514_, lean_object* v_i_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3512_, v_givenName_3513_, v_as_3514_, v_i_3515_);
lean_dec_ref(v_as_3514_);
lean_dec(v_givenName_3513_);
lean_dec(v_localDecl_x3f_3512_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3517_, lean_object* v_givenName_3518_, lean_object* v_as_3519_, lean_object* v_i_3520_){
_start:
{
lean_object* v_zero_3521_; uint8_t v_isZero_3522_; 
v_zero_3521_ = lean_unsigned_to_nat(0u);
v_isZero_3522_ = lean_nat_dec_eq(v_i_3520_, v_zero_3521_);
if (v_isZero_3522_ == 1)
{
lean_object* v___x_3523_; 
lean_dec(v_i_3520_);
v___x_3523_ = lean_box(0);
return v___x_3523_;
}
else
{
lean_object* v_one_3524_; lean_object* v_n_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v_one_3524_ = lean_unsigned_to_nat(1u);
v_n_3525_ = lean_nat_sub(v_i_3520_, v_one_3524_);
lean_dec(v_i_3520_);
v___x_3526_ = lean_array_fget_borrowed(v_as_3519_, v_n_3525_);
v___x_3527_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3517_, v_givenName_3518_, v___x_3526_);
if (lean_obj_tag(v___x_3527_) == 0)
{
v_i_3520_ = v_n_3525_;
goto _start;
}
else
{
lean_dec(v_n_3525_);
return v___x_3527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3529_, lean_object* v_givenName_3530_, lean_object* v_x_3531_){
_start:
{
if (lean_obj_tag(v_x_3531_) == 0)
{
lean_object* v_cs_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v_cs_3532_ = lean_ctor_get(v_x_3531_, 0);
v___x_3533_ = lean_array_get_size(v_cs_3532_);
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3529_, v_givenName_3530_, v_cs_3532_, v___x_3533_);
return v___x_3534_;
}
else
{
lean_object* v_vs_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v_vs_3535_ = lean_ctor_get(v_x_3531_, 0);
v___x_3536_ = lean_array_get_size(v_vs_3535_);
v___x_3537_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3529_, v_givenName_3530_, v_vs_3535_, v___x_3536_);
return v___x_3537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3538_, lean_object* v_givenName_3539_, lean_object* v_x_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3538_, v_givenName_3539_, v_x_3540_);
lean_dec_ref(v_x_3540_);
lean_dec(v_givenName_3539_);
lean_dec(v_localDecl_x3f_3538_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3542_, lean_object* v_givenName_3543_, lean_object* v_as_3544_, lean_object* v_i_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3542_, v_givenName_3543_, v_as_3544_, v_i_3545_);
lean_dec_ref(v_as_3544_);
lean_dec(v_givenName_3543_);
lean_dec(v_localDecl_x3f_3542_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3547_, lean_object* v_givenName_3548_, lean_object* v_t_3549_){
_start:
{
lean_object* v_root_3550_; lean_object* v_tail_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v_root_3550_ = lean_ctor_get(v_t_3549_, 0);
v_tail_3551_ = lean_ctor_get(v_t_3549_, 1);
v___x_3552_ = lean_array_get_size(v_tail_3551_);
v___x_3553_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3547_, v_givenName_3548_, v_tail_3551_, v___x_3552_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v___x_3554_; 
v___x_3554_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3547_, v_givenName_3548_, v_root_3550_);
return v___x_3554_;
}
else
{
return v___x_3553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3555_, lean_object* v_givenName_3556_, lean_object* v_t_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3555_, v_givenName_3556_, v_t_3557_);
lean_dec_ref(v_t_3557_);
lean_dec(v_givenName_3556_);
lean_dec(v_localDecl_x3f_3555_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3559_, lean_object* v_k_3560_){
_start:
{
if (lean_obj_tag(v_t_3559_) == 0)
{
lean_object* v_k_3561_; lean_object* v_v_3562_; lean_object* v_l_3563_; lean_object* v_r_3564_; uint8_t v___x_3565_; 
v_k_3561_ = lean_ctor_get(v_t_3559_, 1);
v_v_3562_ = lean_ctor_get(v_t_3559_, 2);
v_l_3563_ = lean_ctor_get(v_t_3559_, 3);
v_r_3564_ = lean_ctor_get(v_t_3559_, 4);
v___x_3565_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3560_, v_k_3561_);
switch(v___x_3565_)
{
case 0:
{
v_t_3559_ = v_l_3563_;
goto _start;
}
case 1:
{
lean_object* v___x_3567_; 
lean_inc(v_v_3562_);
v___x_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3567_, 0, v_v_3562_);
return v___x_3567_;
}
default: 
{
v_t_3559_ = v_r_3564_;
goto _start;
}
}
}
else
{
lean_object* v___x_3569_; 
v___x_3569_ = lean_box(0);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3570_, lean_object* v_k_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3570_, v_k_3571_);
lean_dec(v_k_3571_);
lean_dec(v_t_3570_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3573_, lean_object* v_givenName_3574_){
_start:
{
lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3575_ = l_Lean_LocalDecl_userName(v_localDecl_3573_);
v___x_3576_ = lean_name_eq(v___x_3575_, v_givenName_3574_);
lean_dec(v___x_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; 
lean_dec_ref(v_localDecl_3573_);
v___x_3577_ = lean_box(0);
return v___x_3577_;
}
else
{
lean_object* v___x_3578_; 
v___x_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3578_, 0, v_localDecl_3573_);
return v___x_3578_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3579_, lean_object* v_givenName_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3579_, v_givenName_3580_);
lean_dec(v_givenName_3580_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3582_, lean_object* v_auxDeclToFullName_3583_, lean_object* v___x_3584_, lean_object* v_givenNameView_3585_, lean_object* v_as_3586_, lean_object* v_i_3587_){
_start:
{
lean_object* v_zero_3588_; uint8_t v_isZero_3589_; 
v_zero_3588_ = lean_unsigned_to_nat(0u);
v_isZero_3589_ = lean_nat_dec_eq(v_i_3587_, v_zero_3588_);
if (v_isZero_3589_ == 1)
{
lean_object* v___x_3590_; 
lean_dec(v_i_3587_);
lean_dec_ref(v_givenNameView_3585_);
lean_dec(v___x_3584_);
v___x_3590_ = lean_box(0);
return v___x_3590_;
}
else
{
lean_object* v_one_3591_; lean_object* v_n_3592_; lean_object* v___y_3594_; lean_object* v___x_3596_; 
v_one_3591_ = lean_unsigned_to_nat(1u);
v_n_3592_ = lean_nat_sub(v_i_3587_, v_one_3591_);
lean_dec(v_i_3587_);
v___x_3596_ = lean_array_fget_borrowed(v_as_3586_, v_n_3592_);
if (lean_obj_tag(v___x_3596_) == 0)
{
v_i_3587_ = v_n_3592_;
goto _start;
}
else
{
lean_object* v_val_3598_; uint8_t v___x_3599_; 
v_val_3598_ = lean_ctor_get(v___x_3596_, 0);
v___x_3599_ = l_Lean_LocalDecl_isAuxDecl(v_val_3598_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; 
lean_inc(v_val_3598_);
v___x_3600_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3598_, v_givenName_3582_);
v___y_3594_ = v___x_3600_;
goto v___jp_3593_;
}
else
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = l_Lean_LocalDecl_fvarId(v_val_3598_);
v___x_3602_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3583_, v___x_3601_);
lean_dec(v___x_3601_);
if (lean_obj_tag(v___x_3602_) == 1)
{
lean_object* v_val_3603_; lean_object* v_fullDeclView_3604_; lean_object* v_name_3605_; lean_object* v_imported_3606_; lean_object* v_ctx_3607_; lean_object* v_scopes_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3628_; 
v_val_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_val_3603_);
lean_dec_ref_known(v___x_3602_, 1);
v_fullDeclView_3604_ = l_Lean_extractMacroScopes(v_val_3603_);
v_name_3605_ = lean_ctor_get(v_fullDeclView_3604_, 0);
v_imported_3606_ = lean_ctor_get(v_fullDeclView_3604_, 1);
v_ctx_3607_ = lean_ctor_get(v_fullDeclView_3604_, 2);
v_scopes_3608_ = lean_ctor_get(v_fullDeclView_3604_, 3);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_fullDeclView_3604_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3610_ = v_fullDeclView_3604_;
v_isShared_3611_ = v_isSharedCheck_3628_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_scopes_3608_);
lean_inc(v_ctx_3607_);
lean_inc(v_imported_3606_);
lean_inc(v_name_3605_);
lean_dec(v_fullDeclView_3604_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3628_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___y_3613_; lean_object* v___x_3626_; 
lean_inc(v_name_3605_);
v___x_3626_ = l_Lean_privateToUserName_x3f(v_name_3605_);
if (lean_obj_tag(v___x_3626_) == 0)
{
v___y_3613_ = v_name_3605_;
goto v___jp_3612_;
}
else
{
lean_object* v_val_3627_; 
lean_dec(v_name_3605_);
v_val_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_val_3627_);
lean_dec_ref_known(v___x_3626_, 1);
v___y_3613_ = v_val_3627_;
goto v___jp_3612_;
}
v___jp_3612_:
{
lean_object* v_fullDeclView_3615_; 
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___y_3613_);
v_fullDeclView_3615_ = v___x_3610_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___y_3613_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_imported_3606_);
lean_ctor_set(v_reuseFailAlloc_3625_, 2, v_ctx_3607_);
lean_ctor_set(v_reuseFailAlloc_3625_, 3, v_scopes_3608_);
v_fullDeclView_3615_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v_fullDeclName_3616_; uint8_t v___x_3617_; 
lean_inc_ref(v_fullDeclView_3615_);
v_fullDeclName_3616_ = l_Lean_MacroScopesView_review(v_fullDeclView_3615_);
v___x_3617_ = l_Lean_Name_isPrefixOf(v___x_3584_, v_fullDeclName_3616_);
if (v___x_3617_ == 0)
{
lean_object* v___x_3618_; 
lean_dec_ref(v_fullDeclView_3615_);
lean_inc(v___x_3584_);
lean_inc_ref(v_givenNameView_3585_);
lean_inc(v_val_3598_);
v___x_3618_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3598_, v_givenNameView_3585_, v_fullDeclName_3616_, v___x_3584_);
lean_dec(v_fullDeclName_3616_);
v___y_3594_ = v___x_3618_;
goto v___jp_3593_;
}
else
{
lean_object* v___x_3619_; lean_object* v_localDeclNameView_3620_; uint8_t v___x_3621_; 
lean_dec(v_fullDeclName_3616_);
v___x_3619_ = l_Lean_LocalDecl_userName(v_val_3598_);
v_localDeclNameView_3620_ = l_Lean_extractMacroScopes(v___x_3619_);
v___x_3621_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3620_, v_givenNameView_3585_);
lean_dec_ref(v_localDeclNameView_3620_);
if (v___x_3621_ == 0)
{
lean_dec_ref(v_fullDeclView_3615_);
v_i_3587_ = v_n_3592_;
goto _start;
}
else
{
uint8_t v___x_3623_; 
v___x_3623_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3585_, v_fullDeclView_3615_);
lean_dec_ref(v_fullDeclView_3615_);
if (v___x_3623_ == 0)
{
v_i_3587_ = v_n_3592_;
goto _start;
}
else
{
lean_dec(v_n_3592_);
lean_dec_ref(v_givenNameView_3585_);
lean_dec(v___x_3584_);
lean_inc_ref(v___x_3596_);
return v___x_3596_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3629_; 
lean_dec(v___x_3602_);
lean_inc(v_val_3598_);
v___x_3629_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3598_, v_givenName_3582_);
v___y_3594_ = v___x_3629_;
goto v___jp_3593_;
}
}
}
v___jp_3593_:
{
if (lean_obj_tag(v___y_3594_) == 0)
{
v_i_3587_ = v_n_3592_;
goto _start;
}
else
{
lean_dec(v_n_3592_);
lean_dec_ref(v_givenNameView_3585_);
lean_dec(v___x_3584_);
return v___y_3594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3630_, lean_object* v_auxDeclToFullName_3631_, lean_object* v___x_3632_, lean_object* v_givenNameView_3633_, lean_object* v_as_3634_, lean_object* v_i_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3630_, v_auxDeclToFullName_3631_, v___x_3632_, v_givenNameView_3633_, v_as_3634_, v_i_3635_);
lean_dec_ref(v_as_3634_);
lean_dec(v_auxDeclToFullName_3631_);
lean_dec(v_givenName_3630_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3637_, lean_object* v_auxDeclToFullName_3638_, lean_object* v___x_3639_, lean_object* v_givenNameView_3640_, lean_object* v_as_3641_, lean_object* v_i_3642_){
_start:
{
lean_object* v_zero_3643_; uint8_t v_isZero_3644_; 
v_zero_3643_ = lean_unsigned_to_nat(0u);
v_isZero_3644_ = lean_nat_dec_eq(v_i_3642_, v_zero_3643_);
if (v_isZero_3644_ == 1)
{
lean_object* v___x_3645_; 
lean_dec(v_i_3642_);
lean_dec_ref(v_givenNameView_3640_);
lean_dec(v___x_3639_);
v___x_3645_ = lean_box(0);
return v___x_3645_;
}
else
{
lean_object* v_one_3646_; lean_object* v_n_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v_one_3646_ = lean_unsigned_to_nat(1u);
v_n_3647_ = lean_nat_sub(v_i_3642_, v_one_3646_);
lean_dec(v_i_3642_);
v___x_3648_ = lean_array_fget_borrowed(v_as_3641_, v_n_3647_);
lean_inc_ref(v_givenNameView_3640_);
lean_inc(v___x_3639_);
v___x_3649_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3637_, v_auxDeclToFullName_3638_, v___x_3639_, v_givenNameView_3640_, v___x_3648_);
if (lean_obj_tag(v___x_3649_) == 0)
{
v_i_3642_ = v_n_3647_;
goto _start;
}
else
{
lean_dec(v_n_3647_);
lean_dec_ref(v_givenNameView_3640_);
lean_dec(v___x_3639_);
return v___x_3649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3651_, lean_object* v_auxDeclToFullName_3652_, lean_object* v___x_3653_, lean_object* v_givenNameView_3654_, lean_object* v_x_3655_){
_start:
{
if (lean_obj_tag(v_x_3655_) == 0)
{
lean_object* v_cs_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v_cs_3656_ = lean_ctor_get(v_x_3655_, 0);
v___x_3657_ = lean_array_get_size(v_cs_3656_);
v___x_3658_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3651_, v_auxDeclToFullName_3652_, v___x_3653_, v_givenNameView_3654_, v_cs_3656_, v___x_3657_);
return v___x_3658_;
}
else
{
lean_object* v_vs_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v_vs_3659_ = lean_ctor_get(v_x_3655_, 0);
v___x_3660_ = lean_array_get_size(v_vs_3659_);
v___x_3661_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3651_, v_auxDeclToFullName_3652_, v___x_3653_, v_givenNameView_3654_, v_vs_3659_, v___x_3660_);
return v___x_3661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3662_, lean_object* v_auxDeclToFullName_3663_, lean_object* v___x_3664_, lean_object* v_givenNameView_3665_, lean_object* v_x_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3662_, v_auxDeclToFullName_3663_, v___x_3664_, v_givenNameView_3665_, v_x_3666_);
lean_dec_ref(v_x_3666_);
lean_dec(v_auxDeclToFullName_3663_);
lean_dec(v_givenName_3662_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3668_, lean_object* v_auxDeclToFullName_3669_, lean_object* v___x_3670_, lean_object* v_givenNameView_3671_, lean_object* v_as_3672_, lean_object* v_i_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3668_, v_auxDeclToFullName_3669_, v___x_3670_, v_givenNameView_3671_, v_as_3672_, v_i_3673_);
lean_dec_ref(v_as_3672_);
lean_dec(v_auxDeclToFullName_3669_);
lean_dec(v_givenName_3668_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3675_, lean_object* v_auxDeclToFullName_3676_, lean_object* v___x_3677_, lean_object* v_givenNameView_3678_, lean_object* v_t_3679_){
_start:
{
lean_object* v_root_3680_; lean_object* v_tail_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v_root_3680_ = lean_ctor_get(v_t_3679_, 0);
v_tail_3681_ = lean_ctor_get(v_t_3679_, 1);
v___x_3682_ = lean_array_get_size(v_tail_3681_);
lean_inc_ref(v_givenNameView_3678_);
lean_inc(v___x_3677_);
v___x_3683_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3675_, v_auxDeclToFullName_3676_, v___x_3677_, v_givenNameView_3678_, v_tail_3681_, v___x_3682_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3675_, v_auxDeclToFullName_3676_, v___x_3677_, v_givenNameView_3678_, v_root_3680_);
return v___x_3684_;
}
else
{
lean_dec_ref(v_givenNameView_3678_);
lean_dec(v___x_3677_);
return v___x_3683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3685_, lean_object* v_auxDeclToFullName_3686_, lean_object* v___x_3687_, lean_object* v_givenNameView_3688_, lean_object* v_t_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3685_, v_auxDeclToFullName_3686_, v___x_3687_, v_givenNameView_3688_, v_t_3689_);
lean_dec_ref(v_t_3689_);
lean_dec(v_auxDeclToFullName_3686_);
lean_dec(v_givenName_3685_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3691_, lean_object* v_currNamespace_3692_, lean_object* v_decls_3693_, lean_object* v_givenNameView_3694_){
_start:
{
lean_object* v_givenName_3695_; lean_object* v_localDecl_x3f_3696_; 
lean_inc_ref(v_givenNameView_3694_);
v_givenName_3695_ = l_Lean_MacroScopesView_review(v_givenNameView_3694_);
v_localDecl_x3f_3696_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3695_, v_auxDeclToFullName_3691_, v_currNamespace_3692_, v_givenNameView_3694_, v_decls_3693_);
if (lean_obj_tag(v_localDecl_x3f_3696_) == 0)
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3696_, v_givenName_3695_, v_decls_3693_);
lean_dec(v_givenName_3695_);
return v___x_3697_;
}
else
{
lean_dec(v_givenName_3695_);
return v_localDecl_x3f_3696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3698_, lean_object* v_currNamespace_3699_, lean_object* v_decls_3700_, lean_object* v_givenNameView_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3698_, v_currNamespace_3699_, v_decls_3700_, v_givenNameView_3701_);
lean_dec_ref(v_decls_3700_);
lean_dec(v_auxDeclToFullName_3698_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_lctx_3711_; lean_object* v_toCold_3712_; lean_object* v_decls_3713_; lean_object* v_auxDeclToFullName_3714_; lean_object* v_currNamespace_3715_; lean_object* v_view_3716_; lean_object* v_name_3717_; lean_object* v_findLocalDecl_x3f_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v_lctx_3711_ = lean_ctor_get(v___y_3706_, 2);
v_toCold_3712_ = lean_ctor_get(v___y_3708_, 0);
v_decls_3713_ = lean_ctor_get(v_lctx_3711_, 1);
v_auxDeclToFullName_3714_ = lean_ctor_get(v_lctx_3711_, 2);
v_currNamespace_3715_ = lean_ctor_get(v_toCold_3712_, 4);
v_view_3716_ = l_Lean_extractMacroScopes(v_n_3703_);
v_name_3717_ = lean_ctor_get(v_view_3716_, 0);
lean_inc(v_name_3717_);
lean_inc_ref(v_decls_3713_);
lean_inc(v_currNamespace_3715_);
lean_inc(v_auxDeclToFullName_3714_);
v_findLocalDecl_x3f_3718_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 4, 3);
lean_closure_set(v_findLocalDecl_x3f_3718_, 0, v_auxDeclToFullName_3714_);
lean_closure_set(v_findLocalDecl_x3f_3718_, 1, v_currNamespace_3715_);
lean_closure_set(v_findLocalDecl_x3f_3718_, 2, v_decls_3713_);
v___x_3719_ = lean_box(0);
v___x_3720_ = lean_box(0);
v___x_3721_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3716_, v_findLocalDecl_x3f_3718_, v_name_3717_, v___x_3719_, v___x_3720_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3731_, lean_object* v_b_3732_){
_start:
{
if (lean_obj_tag(v_as_x27_3731_) == 0)
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3734_, 0, v_b_3732_);
return v___x_3734_;
}
else
{
lean_object* v_head_3735_; lean_object* v_tail_3736_; lean_object* v_config_3737_; lean_object* v_extensions_3738_; lean_object* v_extra_3739_; lean_object* v_extraInj_3740_; lean_object* v_extraFacts_3741_; lean_object* v_symPrios_3742_; lean_object* v_norm_3743_; lean_object* v_normProcs_3744_; lean_object* v_anchorRefs_x3f_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3754_; 
v_head_3735_ = lean_ctor_get(v_as_x27_3731_, 0);
v_tail_3736_ = lean_ctor_get(v_as_x27_3731_, 1);
v_config_3737_ = lean_ctor_get(v_b_3732_, 0);
v_extensions_3738_ = lean_ctor_get(v_b_3732_, 1);
v_extra_3739_ = lean_ctor_get(v_b_3732_, 2);
v_extraInj_3740_ = lean_ctor_get(v_b_3732_, 3);
v_extraFacts_3741_ = lean_ctor_get(v_b_3732_, 4);
v_symPrios_3742_ = lean_ctor_get(v_b_3732_, 5);
v_norm_3743_ = lean_ctor_get(v_b_3732_, 6);
v_normProcs_3744_ = lean_ctor_get(v_b_3732_, 7);
v_anchorRefs_x3f_3745_ = lean_ctor_get(v_b_3732_, 8);
v_isSharedCheck_3754_ = !lean_is_exclusive(v_b_3732_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3747_ = v_b_3732_;
v_isShared_3748_ = v_isSharedCheck_3754_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_anchorRefs_x3f_3745_);
lean_inc(v_normProcs_3744_);
lean_inc(v_norm_3743_);
lean_inc(v_symPrios_3742_);
lean_inc(v_extraFacts_3741_);
lean_inc(v_extraInj_3740_);
lean_inc(v_extra_3739_);
lean_inc(v_extensions_3738_);
lean_inc(v_config_3737_);
lean_dec(v_b_3732_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3754_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3749_; lean_object* v___x_3751_; 
lean_inc(v_head_3735_);
v___x_3749_ = l_Lean_PersistentArray_push___redArg(v_extra_3739_, v_head_3735_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 2, v___x_3749_);
v___x_3751_ = v___x_3747_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_config_3737_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_extensions_3738_);
lean_ctor_set(v_reuseFailAlloc_3753_, 2, v___x_3749_);
lean_ctor_set(v_reuseFailAlloc_3753_, 3, v_extraInj_3740_);
lean_ctor_set(v_reuseFailAlloc_3753_, 4, v_extraFacts_3741_);
lean_ctor_set(v_reuseFailAlloc_3753_, 5, v_symPrios_3742_);
lean_ctor_set(v_reuseFailAlloc_3753_, 6, v_norm_3743_);
lean_ctor_set(v_reuseFailAlloc_3753_, 7, v_normProcs_3744_);
lean_ctor_set(v_reuseFailAlloc_3753_, 8, v_anchorRefs_x3f_3745_);
v___x_3751_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
v_as_x27_3731_ = v_tail_3736_;
v_b_3732_ = v___x_3751_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3755_, lean_object* v_b_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3755_, v_b_3756_);
lean_dec(v_as_x27_3755_);
return v_res_3758_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3761_ = l_Lean_stringToMessageData(v___x_3760_);
return v___x_3761_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3764_ = l_Lean_stringToMessageData(v___x_3763_);
return v___x_3764_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3767_ = l_Lean_stringToMessageData(v___x_3766_);
return v___x_3767_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3769_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3770_ = l_Lean_stringToMessageData(v___x_3769_);
return v___x_3770_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3773_ = l_Lean_stringToMessageData(v___x_3772_);
return v___x_3773_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3776_ = l_Lean_stringToMessageData(v___x_3775_);
return v___x_3776_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3779_ = l_Lean_stringToMessageData(v___x_3778_);
return v___x_3779_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3782_ = l_Lean_stringToMessageData(v___x_3781_);
return v___x_3782_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3784_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3785_ = l_Lean_stringToMessageData(v___x_3784_);
return v___x_3785_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3787_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3788_ = l_Lean_stringToMessageData(v___x_3787_);
return v___x_3788_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3790_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3791_ = l_Lean_stringToMessageData(v___x_3790_);
return v___x_3791_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23(void){
_start:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3793_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22));
v___x_3794_ = l_Lean_stringToMessageData(v___x_3793_);
return v___x_3794_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24));
v___x_3797_ = l_Lean_stringToMessageData(v___x_3796_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3798_, lean_object* v_p_3799_, lean_object* v_mod_x3f_3800_, lean_object* v_id_3801_, uint8_t v_minIndexable_3802_, uint8_t v_only_3803_, uint8_t v_incremental_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_){
_start:
{
lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3823_; uint8_t v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; uint8_t v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v_a_3991_; lean_object* v___y_4213_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4224_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4225_ = lean_box(0);
lean_inc(v_id_3801_);
v___x_4226_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3801_, v___x_4225_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
lean_dec_ref_known(v___x_4226_, 1);
v_a_3991_ = v_a_4227_;
goto v___jp_3990_;
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4303_; 
v_a_4228_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4230_ = v___x_4226_;
v_isShared_4231_ = v_isSharedCheck_4303_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4226_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4303_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
uint8_t v___x_4232_; 
v___x_4232_ = l_Lean_Exception_isInterrupt(v_a_4228_);
if (v___x_4232_ == 0)
{
uint8_t v___x_4233_; 
lean_inc(v_a_4228_);
v___x_4233_ = l_Lean_Exception_isRuntime(v_a_4228_);
if (v___x_4233_ == 0)
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
lean_del_object(v___x_4230_);
v___x_4234_ = l_Lean_TSyntax_getId(v_id_3801_);
lean_inc(v___x_4234_);
v___x_4235_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4234_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v___x_4235_, 1);
if (lean_obj_tag(v_a_4236_) == 0)
{
lean_object* v___x_4237_; 
v___x_4237_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_4234_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4266_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4240_ = v___x_4237_;
v_isShared_4241_ = v_isSharedCheck_4266_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4266_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
if (lean_obj_tag(v_a_4238_) == 1)
{
lean_del_object(v___x_4240_);
lean_dec(v_a_4228_);
if (lean_obj_tag(v_mod_x3f_3800_) == 1)
{
lean_object* v_val_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_dec_ref_known(v_a_4238_, 1);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_val_4242_ = lean_ctor_get(v_mod_x3f_3800_, 0);
lean_inc(v_val_4242_);
lean_dec_ref_known(v_mod_x3f_3800_, 1);
v___x_4243_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4244_ = l_Lean_MessageData_ofName(v___x_4234_);
v___x_4245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4243_);
lean_ctor_set(v___x_4245_, 1, v___x_4244_);
v___x_4246_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4245_);
lean_ctor_set(v___x_4247_, 1, v___x_4246_);
v___x_4248_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4242_, v___x_4247_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
lean_dec(v_val_4242_);
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4248_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4248_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
else
{
lean_object* v_val_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
lean_dec(v___x_4234_);
v_val_4257_ = lean_ctor_get(v_a_4238_, 0);
lean_inc(v_val_4257_);
lean_dec_ref_known(v_a_4238_, 1);
v___x_4258_ = lean_box(0);
lean_inc_ref(v_params_3798_);
v___x_4259_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3798_, v_val_4257_, v___x_4224_, v___x_4233_, v___x_4258_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
lean_dec(v_val_4257_);
v___y_4213_ = v___x_4259_;
goto v___jp_4212_;
}
}
else
{
lean_object* v___x_4260_; uint8_t v___x_4261_; 
lean_dec(v_a_4238_);
v___x_4260_ = l_Lean_Name_getPrefix(v___x_4234_);
lean_dec(v___x_4234_);
v___x_4261_ = l_Lean_Name_isAnonymous(v___x_4260_);
lean_dec(v___x_4260_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; 
lean_del_object(v___x_4240_);
lean_dec(v_a_4228_);
v___x_4262_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3798_, v_p_3799_, v_mod_x3f_3800_, v_id_3801_, v_minIndexable_3802_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
return v___x_4262_;
}
else
{
lean_object* v___x_4264_; 
lean_dec(v_id_3801_);
lean_dec(v_mod_x3f_3800_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
if (v_isShared_4241_ == 0)
{
lean_ctor_set_tag(v___x_4240_, 1);
lean_ctor_set(v___x_4240_, 0, v_a_4228_);
v___x_4264_ = v___x_4240_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4228_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
}
else
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
lean_dec(v___x_4234_);
lean_dec(v_a_4228_);
lean_dec(v_id_3801_);
lean_dec(v_mod_x3f_3800_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_a_4267_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4237_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4237_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
else
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec_ref_known(v_a_4236_, 1);
lean_dec(v___x_4234_);
lean_dec(v_a_4228_);
lean_dec(v_mod_x3f_3800_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v___x_4275_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23);
lean_inc(v_id_3801_);
v___x_4276_ = l_Lean_MessageData_ofSyntax(v_id_3801_);
v___x_4277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4275_);
lean_ctor_set(v___x_4277_, 1, v___x_4276_);
v___x_4278_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25);
v___x_4279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4277_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3801_, v___x_4279_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
lean_dec(v_id_3801_);
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4280_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4280_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec(v___x_4234_);
lean_dec(v_a_4228_);
lean_dec(v_id_3801_);
lean_dec(v_mod_x3f_3800_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_a_4289_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4235_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4235_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
else
{
lean_object* v___x_4298_; 
lean_dec(v_id_3801_);
lean_dec(v_mod_x3f_3800_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
if (v_isShared_4231_ == 0)
{
v___x_4298_ = v___x_4230_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4228_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
else
{
lean_object* v___x_4301_; 
lean_dec(v_id_3801_);
lean_dec(v_mod_x3f_3800_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
if (v_isShared_4231_ == 0)
{
v___x_4301_ = v___x_4230_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4228_);
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
v___jp_3812_:
{
lean_object* v_ctors_3820_; lean_object* v___x_3821_; 
v_ctors_3820_ = lean_ctor_get(v___y_3813_, 4);
lean_inc(v_ctors_3820_);
lean_dec_ref(v___y_3813_);
v___x_3821_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3799_, v_id_3801_, v_minIndexable_3802_, v_ctors_3820_, v_params_3798_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec(v_ctors_3820_);
lean_dec(v_p_3799_);
return v___x_3821_;
}
v___jp_3822_:
{
lean_object* v___x_3829_; 
v___x_3829_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3802_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_toCold_3830_; lean_object* v_currRecDepth_3831_; lean_object* v_ref_3832_; uint16_t v_optionFlags_3833_; uint8_t v_suppressElabErrors_3834_; uint8_t v_checkDeprecated_3835_; uint8_t v_isRecordingDeps_3836_; lean_object* v_ref_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
lean_dec_ref_known(v___x_3829_, 1);
v_toCold_3830_ = lean_ctor_get(v___y_3827_, 0);
v_currRecDepth_3831_ = lean_ctor_get(v___y_3827_, 1);
v_ref_3832_ = lean_ctor_get(v___y_3827_, 2);
v_optionFlags_3833_ = lean_ctor_get_uint16(v___y_3827_, sizeof(void*)*3);
v_suppressElabErrors_3834_ = lean_ctor_get_uint8(v___y_3827_, sizeof(void*)*3 + 2);
v_checkDeprecated_3835_ = lean_ctor_get_uint8(v___y_3827_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3836_ = lean_ctor_get_uint8(v___y_3827_, sizeof(void*)*3 + 4);
v_ref_3837_ = l_Lean_replaceRef(v_p_3799_, v_ref_3832_);
lean_dec(v_p_3799_);
lean_inc(v_currRecDepth_3831_);
lean_inc_ref(v_toCold_3830_);
v___x_3838_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3838_, 0, v_toCold_3830_);
lean_ctor_set(v___x_3838_, 1, v_currRecDepth_3831_);
lean_ctor_set(v___x_3838_, 2, v_ref_3837_);
lean_ctor_set_uint16(v___x_3838_, sizeof(void*)*3, v_optionFlags_3833_);
lean_ctor_set_uint8(v___x_3838_, sizeof(void*)*3 + 2, v_suppressElabErrors_3834_);
lean_ctor_set_uint8(v___x_3838_, sizeof(void*)*3 + 3, v_checkDeprecated_3835_);
lean_ctor_set_uint8(v___x_3838_, sizeof(void*)*3 + 4, v_isRecordingDeps_3836_);
lean_inc(v___y_3823_);
v___x_3839_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3823_, v___y_3824_, v___x_3838_, v___y_3828_);
lean_dec_ref_known(v___x_3838_, 3);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3847_; 
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3847_ == 0)
{
lean_object* v_unused_3848_; 
v_unused_3848_ = lean_ctor_get(v___x_3839_, 0);
lean_dec(v_unused_3848_);
v___x_3841_ = v___x_3839_;
v_isShared_3842_ = v_isSharedCheck_3847_;
goto v_resetjp_3840_;
}
else
{
lean_dec(v___x_3839_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3847_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3843_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3798_, v___y_3823_, v___y_3824_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 0, v___x_3843_);
v___x_3845_ = v___x_3841_;
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
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec(v___y_3823_);
lean_dec_ref(v_params_3798_);
v_a_3849_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3839_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3839_);
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
lean_dec(v___y_3823_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_a_3857_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3829_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3829_);
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
v___jp_3865_:
{
lean_object* v___x_3874_; 
v___x_3874_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3802_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
lean_dec_ref_known(v___x_3874_, 1);
v___x_3875_ = l_Lean_Meta_Grind_grindExt;
v___x_3876_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3875_, v___y_3873_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; uint8_t v___x_3882_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
lean_inc(v___y_3867_);
v___x_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3878_, 0, v___y_3867_);
v___x_3879_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3877_, v___x_3878_);
lean_dec_ref_known(v___x_3878_, 1);
lean_dec(v_a_3877_);
v___x_3880_ = lean_box(0);
v___x_3881_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3866_, v___x_3879_, v___x_3880_);
lean_dec(v___y_3866_);
v___x_3882_ = l_List_isEmpty___redArg(v___x_3881_);
if (v___x_3882_ == 0)
{
lean_object* v___x_3883_; 
lean_dec(v___y_3867_);
lean_dec(v_p_3799_);
v___x_3883_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3881_, v_params_3798_);
lean_dec(v___x_3881_);
return v___x_3883_;
}
else
{
lean_object* v___x_3884_; uint8_t v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec(v___x_3881_);
lean_dec_ref(v_params_3798_);
v___x_3884_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3885_ = 0;
v___x_3886_ = l_Lean_MessageData_ofConstName(v___y_3867_, v___x_3885_);
v___x_3887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3884_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
v___x_3888_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3887_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
v___x_3890_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3799_, v___x_3889_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v_p_3799_);
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3890_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3890_);
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
lean_dec(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_a_3899_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3876_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3876_);
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
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_a_3907_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3874_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3874_);
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
v___jp_3915_:
{
uint8_t v___x_3924_; lean_object* v___x_3925_; 
v___x_3924_ = 0;
lean_inc(v___y_3917_);
v___x_3925_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3917_, v___x_3924_, v___y_3922_, v___y_3923_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref_known(v___x_3925_, 1);
if (lean_obj_tag(v_a_3926_) == 1)
{
lean_object* v_val_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
lean_dec(v___y_3917_);
v_val_3927_ = lean_ctor_get(v_a_3926_, 0);
lean_inc_n(v_val_3927_, 2);
lean_dec_ref_known(v_a_3926_, 1);
v___x_3928_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3798_, v_val_3927_, v___x_3924_);
v___x_3929_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3927_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3940_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3932_ = v___x_3929_;
v_isShared_3933_ = v_isSharedCheck_3940_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3929_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3940_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
if (lean_obj_tag(v_a_3930_) == 1)
{
lean_object* v_val_3934_; lean_object* v_ctors_3935_; lean_object* v___x_3936_; 
lean_del_object(v___x_3932_);
v_val_3934_ = lean_ctor_get(v_a_3930_, 0);
lean_inc(v_val_3934_);
lean_dec_ref_known(v_a_3930_, 1);
v_ctors_3935_ = lean_ctor_get(v_val_3934_, 4);
lean_inc(v_ctors_3935_);
lean_dec(v_val_3934_);
v___x_3936_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3799_, v_id_3801_, v_minIndexable_3802_, v_ctors_3935_, v___x_3928_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec(v_ctors_3935_);
lean_dec(v_p_3799_);
return v___x_3936_;
}
else
{
lean_object* v___x_3938_; 
lean_dec(v_a_3930_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 0, v___x_3928_);
v___x_3938_ = v___x_3932_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3928_);
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
lean_dec_ref(v___x_3928_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
v_a_3941_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3929_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3929_);
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
lean_object* v_symPrios_3949_; lean_object* v___x_3950_; 
lean_dec(v_a_3926_);
v_symPrios_3949_ = lean_ctor_get(v_params_3798_, 5);
lean_inc_ref(v_symPrios_3949_);
lean_inc(v___y_3917_);
v___x_3950_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(v___y_3917_, v_symPrios_3949_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; uint8_t v___x_3952_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref_known(v___x_3950_, 1);
v___x_3952_ = lean_unbox(v_a_3951_);
lean_dec(v_a_3951_);
if (v___x_3952_ == 0)
{
lean_object* v_toCold_3953_; lean_object* v_currRecDepth_3954_; lean_object* v_ref_3955_; uint16_t v_optionFlags_3956_; uint8_t v_suppressElabErrors_3957_; uint8_t v_checkDeprecated_3958_; uint8_t v_isRecordingDeps_3959_; lean_object* v___x_3960_; lean_object* v_ref_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_toCold_3953_ = lean_ctor_get(v___y_3922_, 0);
v_currRecDepth_3954_ = lean_ctor_get(v___y_3922_, 1);
v_ref_3955_ = lean_ctor_get(v___y_3922_, 2);
v_optionFlags_3956_ = lean_ctor_get_uint16(v___y_3922_, sizeof(void*)*3);
v_suppressElabErrors_3957_ = lean_ctor_get_uint8(v___y_3922_, sizeof(void*)*3 + 2);
v_checkDeprecated_3958_ = lean_ctor_get_uint8(v___y_3922_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3959_ = lean_ctor_get_uint8(v___y_3922_, sizeof(void*)*3 + 4);
v___x_3960_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_ref_3961_ = l_Lean_replaceRef(v_p_3799_, v_ref_3955_);
lean_dec(v_p_3799_);
lean_inc(v_currRecDepth_3954_);
lean_inc_ref(v_toCold_3953_);
v___x_3962_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3962_, 0, v_toCold_3953_);
lean_ctor_set(v___x_3962_, 1, v_currRecDepth_3954_);
lean_ctor_set(v___x_3962_, 2, v_ref_3961_);
lean_ctor_set_uint16(v___x_3962_, sizeof(void*)*3, v_optionFlags_3956_);
lean_ctor_set_uint8(v___x_3962_, sizeof(void*)*3 + 2, v_suppressElabErrors_3957_);
lean_ctor_set_uint8(v___x_3962_, sizeof(void*)*3 + 3, v_checkDeprecated_3958_);
lean_ctor_set_uint8(v___x_3962_, sizeof(void*)*3 + 4, v_isRecordingDeps_3959_);
v___x_3963_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3798_, v_id_3801_, v___y_3917_, v___x_3960_, v_minIndexable_3802_, v___y_3916_, v___y_3916_, v___y_3920_, v___y_3921_, v___x_3962_, v___y_3923_);
lean_dec_ref_known(v___x_3962_, 3);
return v___x_3963_;
}
else
{
lean_object* v_toCold_3964_; lean_object* v_currRecDepth_3965_; lean_object* v_ref_3966_; uint16_t v_optionFlags_3967_; uint8_t v_suppressElabErrors_3968_; uint8_t v_checkDeprecated_3969_; uint8_t v_isRecordingDeps_3970_; lean_object* v_ref_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
lean_dec(v_id_3801_);
v_toCold_3964_ = lean_ctor_get(v___y_3922_, 0);
v_currRecDepth_3965_ = lean_ctor_get(v___y_3922_, 1);
v_ref_3966_ = lean_ctor_get(v___y_3922_, 2);
v_optionFlags_3967_ = lean_ctor_get_uint16(v___y_3922_, sizeof(void*)*3);
v_suppressElabErrors_3968_ = lean_ctor_get_uint8(v___y_3922_, sizeof(void*)*3 + 2);
v_checkDeprecated_3969_ = lean_ctor_get_uint8(v___y_3922_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3970_ = lean_ctor_get_uint8(v___y_3922_, sizeof(void*)*3 + 4);
v_ref_3971_ = l_Lean_replaceRef(v_p_3799_, v_ref_3966_);
lean_dec(v_p_3799_);
lean_inc(v_currRecDepth_3965_);
lean_inc_ref(v_toCold_3964_);
v___x_3972_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3972_, 0, v_toCold_3964_);
lean_ctor_set(v___x_3972_, 1, v_currRecDepth_3965_);
lean_ctor_set(v___x_3972_, 2, v_ref_3971_);
lean_ctor_set_uint16(v___x_3972_, sizeof(void*)*3, v_optionFlags_3967_);
lean_ctor_set_uint8(v___x_3972_, sizeof(void*)*3 + 2, v_suppressElabErrors_3968_);
lean_ctor_set_uint8(v___x_3972_, sizeof(void*)*3 + 3, v_checkDeprecated_3969_);
lean_ctor_set_uint8(v___x_3972_, sizeof(void*)*3 + 4, v_isRecordingDeps_3970_);
v___x_3973_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(v_params_3798_, v___y_3917_, v_minIndexable_3802_, v___y_3920_, v___y_3921_, v___x_3972_, v___y_3923_);
lean_dec_ref_known(v___x_3972_, 3);
return v___x_3973_;
}
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
lean_dec(v___y_3917_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_a_3974_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3950_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3950_);
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
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec(v___y_3917_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_a_3982_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3925_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3925_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
v___jp_3990_:
{
lean_object* v_toCold_3992_; lean_object* v_currRecDepth_3993_; lean_object* v_ref_3994_; uint16_t v_optionFlags_3995_; uint8_t v_suppressElabErrors_3996_; uint8_t v_checkDeprecated_3997_; uint8_t v_isRecordingDeps_3998_; uint8_t v___x_3999_; lean_object* v_ref_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v_toCold_3992_ = lean_ctor_get(v_a_3809_, 0);
v_currRecDepth_3993_ = lean_ctor_get(v_a_3809_, 1);
v_ref_3994_ = lean_ctor_get(v_a_3809_, 2);
v_optionFlags_3995_ = lean_ctor_get_uint16(v_a_3809_, sizeof(void*)*3);
v_suppressElabErrors_3996_ = lean_ctor_get_uint8(v_a_3809_, sizeof(void*)*3 + 2);
v_checkDeprecated_3997_ = lean_ctor_get_uint8(v_a_3809_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3998_ = lean_ctor_get_uint8(v_a_3809_, sizeof(void*)*3 + 4);
v___x_3999_ = 1;
v_ref_4000_ = l_Lean_replaceRef(v_id_3801_, v_ref_3994_);
lean_inc(v_currRecDepth_3993_);
lean_inc_ref(v_toCold_3992_);
v___x_4001_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4001_, 0, v_toCold_3992_);
lean_ctor_set(v___x_4001_, 1, v_currRecDepth_3993_);
lean_ctor_set(v___x_4001_, 2, v_ref_4000_);
lean_ctor_set_uint16(v___x_4001_, sizeof(void*)*3, v_optionFlags_3995_);
lean_ctor_set_uint8(v___x_4001_, sizeof(void*)*3 + 2, v_suppressElabErrors_3996_);
lean_ctor_set_uint8(v___x_4001_, sizeof(void*)*3 + 3, v_checkDeprecated_3997_);
lean_ctor_set_uint8(v___x_4001_, sizeof(void*)*3 + 4, v_isRecordingDeps_3998_);
lean_inc(v_a_3991_);
v___x_4002_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_3991_, v___x_3999_, v_a_3807_, v_a_3808_, v___x_4001_, v_a_3810_);
lean_dec_ref_known(v___x_4001_, 3);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_dec_ref_known(v___x_4002_, 1);
if (lean_obj_tag(v_mod_x3f_3800_) == 1)
{
lean_object* v_val_4003_; lean_object* v___x_4004_; 
v_val_4003_ = lean_ctor_get(v_mod_x3f_3800_, 0);
lean_inc(v_val_4003_);
lean_dec_ref_known(v_mod_x3f_3800_, 1);
v___x_4004_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_4003_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4195_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4007_ = v___x_4004_;
v_isShared_4008_ = v_isSharedCheck_4195_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_4004_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4195_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
switch(lean_obj_tag(v_a_4005_))
{
case 0:
{
lean_object* v_k_4009_; 
lean_del_object(v___x_4007_);
v_k_4009_ = lean_ctor_get(v_a_4005_, 0);
lean_inc(v_k_4009_);
lean_dec_ref_known(v_a_4005_, 1);
if (lean_obj_tag(v_k_4009_) == 9)
{
lean_dec(v_id_3801_);
if (v_only_3803_ == 0)
{
lean_object* v_ref_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v_ref_4010_ = l_Lean_replaceRef(v_p_3799_, v_ref_3994_);
lean_inc(v_currRecDepth_3993_);
lean_inc_ref(v_toCold_3992_);
v___x_4011_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4011_, 0, v_toCold_3992_);
lean_ctor_set(v___x_4011_, 1, v_currRecDepth_3993_);
lean_ctor_set(v___x_4011_, 2, v_ref_4010_);
lean_ctor_set_uint16(v___x_4011_, sizeof(void*)*3, v_optionFlags_3995_);
lean_ctor_set_uint8(v___x_4011_, sizeof(void*)*3 + 2, v_suppressElabErrors_3996_);
lean_ctor_set_uint8(v___x_4011_, sizeof(void*)*3 + 3, v_checkDeprecated_3997_);
lean_ctor_set_uint8(v___x_4011_, sizeof(void*)*3 + 4, v_isRecordingDeps_3998_);
v___x_4012_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_4011_, v_a_3810_);
lean_dec_ref_known(v___x_4011_, 3);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_dec_ref_known(v___x_4012_, 1);
v___y_3866_ = v_k_4009_;
v___y_3867_ = v_a_3991_;
v___y_3868_ = v_a_3805_;
v___y_3869_ = v_a_3806_;
v___y_3870_ = v_a_3807_;
v___y_3871_ = v_a_3808_;
v___y_3872_ = v_a_3809_;
v___y_3873_ = v_a_3810_;
goto v___jp_3865_;
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_dec(v_a_3991_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_4012_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4012_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
else
{
v___y_3866_ = v_k_4009_;
v___y_3867_ = v_a_3991_;
v___y_3868_ = v_a_3805_;
v___y_3869_ = v_a_3806_;
v___y_3870_ = v_a_3807_;
v___y_3871_ = v_a_3808_;
v___y_3872_ = v_a_3809_;
v___y_3873_ = v_a_3810_;
goto v___jp_3865_;
}
}
else
{
uint8_t v___x_4021_; lean_object* v_ref_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4021_ = 0;
v_ref_4022_ = l_Lean_replaceRef(v_p_3799_, v_ref_3994_);
lean_dec(v_p_3799_);
lean_inc(v_currRecDepth_3993_);
lean_inc_ref(v_toCold_3992_);
v___x_4023_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4023_, 0, v_toCold_3992_);
lean_ctor_set(v___x_4023_, 1, v_currRecDepth_3993_);
lean_ctor_set(v___x_4023_, 2, v_ref_4022_);
lean_ctor_set_uint16(v___x_4023_, sizeof(void*)*3, v_optionFlags_3995_);
lean_ctor_set_uint8(v___x_4023_, sizeof(void*)*3 + 2, v_suppressElabErrors_3996_);
lean_ctor_set_uint8(v___x_4023_, sizeof(void*)*3 + 3, v_checkDeprecated_3997_);
lean_ctor_set_uint8(v___x_4023_, sizeof(void*)*3 + 4, v_isRecordingDeps_3998_);
v___x_4024_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3798_, v_id_3801_, v_a_3991_, v_k_4009_, v_minIndexable_3802_, v___x_4021_, v___x_3999_, v_a_3807_, v_a_3808_, v___x_4023_, v_a_3810_);
lean_dec_ref_known(v___x_4023_, 3);
return v___x_4024_;
}
}
case 1:
{
lean_del_object(v___x_4007_);
lean_dec(v_id_3801_);
if (v_incremental_3804_ == 0)
{
uint8_t v_eager_4025_; 
v_eager_4025_ = lean_ctor_get_uint8(v_a_4005_, 0);
lean_dec_ref_known(v_a_4005_, 0);
v___y_3823_ = v_a_3991_;
v___y_3824_ = v_eager_4025_;
v___y_3825_ = v_a_3807_;
v___y_3826_ = v_a_3808_;
v___y_3827_ = v_a_3809_;
v___y_3828_ = v_a_3810_;
goto v___jp_3822_;
}
else
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec_ref_known(v_a_4005_, 0);
lean_dec(v_a_3991_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v___x_4026_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_4027_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4026_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
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
case 2:
{
uint8_t v___x_4036_; lean_object* v___x_4037_; 
lean_del_object(v___x_4007_);
v___x_4036_ = 0;
lean_inc(v_a_3991_);
v___x_4037_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3991_, v___x_4036_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4037_, 1);
if (lean_obj_tag(v_a_4038_) == 1)
{
lean_dec(v_a_3991_);
if (v_incremental_3804_ == 0)
{
lean_object* v_val_4039_; 
v_val_4039_ = lean_ctor_get(v_a_4038_, 0);
lean_inc(v_val_4039_);
lean_dec_ref_known(v_a_4038_, 1);
v___y_3813_ = v_val_4039_;
v___y_3814_ = v_a_3805_;
v___y_3815_ = v_a_3806_;
v___y_3816_ = v_a_3807_;
v___y_3817_ = v_a_3808_;
v___y_3818_ = v_a_3809_;
v___y_3819_ = v_a_3810_;
goto v___jp_3812_;
}
else
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_dec_ref_known(v_a_4038_, 1);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v___x_4040_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_4041_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4040_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
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
}
else
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec(v_a_4038_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v___x_4050_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_4051_ = l_Lean_MessageData_ofConstName(v_a_3991_, v___x_4036_);
v___x_4052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4050_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
v___x_4053_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_4054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4052_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
v___x_4055_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4054_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
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
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec(v_a_3991_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_a_4064_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4037_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4037_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
case 3:
{
lean_del_object(v___x_4007_);
v___y_3916_ = v___x_3999_;
v___y_3917_ = v_a_3991_;
v___y_3918_ = v_a_3805_;
v___y_3919_ = v_a_3806_;
v___y_3920_ = v_a_3807_;
v___y_3921_ = v_a_3808_;
v___y_3922_ = v_a_3809_;
v___y_3923_ = v_a_3810_;
goto v___jp_3915_;
}
case 4:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_del_object(v___x_4007_);
lean_dec(v_a_3991_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v___x_4072_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_4073_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4072_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4073_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4073_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
case 5:
{
lean_object* v_prio_4082_; lean_object* v___x_4083_; 
lean_del_object(v___x_4007_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
v_prio_4082_ = lean_ctor_get(v_a_4005_, 0);
lean_inc(v_prio_4082_);
lean_dec_ref_known(v_a_4005_, 1);
v___x_4083_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3802_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4107_; 
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4107_ == 0)
{
lean_object* v_unused_4108_; 
v_unused_4108_ = lean_ctor_get(v___x_4083_, 0);
lean_dec(v_unused_4108_);
v___x_4085_ = v___x_4083_;
v_isShared_4086_ = v_isSharedCheck_4107_;
goto v_resetjp_4084_;
}
else
{
lean_dec(v___x_4083_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4107_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v_config_4087_; lean_object* v_extensions_4088_; lean_object* v_extra_4089_; lean_object* v_extraInj_4090_; lean_object* v_extraFacts_4091_; lean_object* v_symPrios_4092_; lean_object* v_norm_4093_; lean_object* v_normProcs_4094_; lean_object* v_anchorRefs_x3f_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4106_; 
v_config_4087_ = lean_ctor_get(v_params_3798_, 0);
v_extensions_4088_ = lean_ctor_get(v_params_3798_, 1);
v_extra_4089_ = lean_ctor_get(v_params_3798_, 2);
v_extraInj_4090_ = lean_ctor_get(v_params_3798_, 3);
v_extraFacts_4091_ = lean_ctor_get(v_params_3798_, 4);
v_symPrios_4092_ = lean_ctor_get(v_params_3798_, 5);
v_norm_4093_ = lean_ctor_get(v_params_3798_, 6);
v_normProcs_4094_ = lean_ctor_get(v_params_3798_, 7);
v_anchorRefs_x3f_4095_ = lean_ctor_get(v_params_3798_, 8);
v_isSharedCheck_4106_ = !lean_is_exclusive(v_params_3798_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4097_ = v_params_3798_;
v_isShared_4098_ = v_isSharedCheck_4106_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_anchorRefs_x3f_4095_);
lean_inc(v_normProcs_4094_);
lean_inc(v_norm_4093_);
lean_inc(v_symPrios_4092_);
lean_inc(v_extraFacts_4091_);
lean_inc(v_extraInj_4090_);
lean_inc(v_extra_4089_);
lean_inc(v_extensions_4088_);
lean_inc(v_config_4087_);
lean_dec(v_params_3798_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4106_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; lean_object* v___x_4101_; 
v___x_4099_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_4092_, v_a_3991_, v_prio_4082_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 5, v___x_4099_);
v___x_4101_ = v___x_4097_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_config_4087_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v_extensions_4088_);
lean_ctor_set(v_reuseFailAlloc_4105_, 2, v_extra_4089_);
lean_ctor_set(v_reuseFailAlloc_4105_, 3, v_extraInj_4090_);
lean_ctor_set(v_reuseFailAlloc_4105_, 4, v_extraFacts_4091_);
lean_ctor_set(v_reuseFailAlloc_4105_, 5, v___x_4099_);
lean_ctor_set(v_reuseFailAlloc_4105_, 6, v_norm_4093_);
lean_ctor_set(v_reuseFailAlloc_4105_, 7, v_normProcs_4094_);
lean_ctor_set(v_reuseFailAlloc_4105_, 8, v_anchorRefs_x3f_4095_);
v___x_4101_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
lean_object* v___x_4103_; 
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 0, v___x_4101_);
v___x_4103_ = v___x_4085_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v___x_4101_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
lean_dec(v_prio_4082_);
lean_dec(v_a_3991_);
lean_dec_ref(v_params_3798_);
v_a_4109_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4083_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4083_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
case 6:
{
lean_object* v___x_4117_; 
lean_del_object(v___x_4007_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
v___x_4117_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3991_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4142_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4120_ = v___x_4117_;
v_isShared_4121_ = v_isSharedCheck_4142_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4142_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v_config_4122_; lean_object* v_extensions_4123_; lean_object* v_extra_4124_; lean_object* v_extraInj_4125_; lean_object* v_extraFacts_4126_; lean_object* v_symPrios_4127_; lean_object* v_norm_4128_; lean_object* v_normProcs_4129_; lean_object* v_anchorRefs_x3f_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4141_; 
v_config_4122_ = lean_ctor_get(v_params_3798_, 0);
v_extensions_4123_ = lean_ctor_get(v_params_3798_, 1);
v_extra_4124_ = lean_ctor_get(v_params_3798_, 2);
v_extraInj_4125_ = lean_ctor_get(v_params_3798_, 3);
v_extraFacts_4126_ = lean_ctor_get(v_params_3798_, 4);
v_symPrios_4127_ = lean_ctor_get(v_params_3798_, 5);
v_norm_4128_ = lean_ctor_get(v_params_3798_, 6);
v_normProcs_4129_ = lean_ctor_get(v_params_3798_, 7);
v_anchorRefs_x3f_4130_ = lean_ctor_get(v_params_3798_, 8);
v_isSharedCheck_4141_ = !lean_is_exclusive(v_params_3798_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4132_ = v_params_3798_;
v_isShared_4133_ = v_isSharedCheck_4141_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_anchorRefs_x3f_4130_);
lean_inc(v_normProcs_4129_);
lean_inc(v_norm_4128_);
lean_inc(v_symPrios_4127_);
lean_inc(v_extraFacts_4126_);
lean_inc(v_extraInj_4125_);
lean_inc(v_extra_4124_);
lean_inc(v_extensions_4123_);
lean_inc(v_config_4122_);
lean_dec(v_params_3798_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4141_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4134_; lean_object* v___x_4136_; 
v___x_4134_ = l_Lean_PersistentArray_push___redArg(v_extraInj_4125_, v_a_4118_);
if (v_isShared_4133_ == 0)
{
lean_ctor_set(v___x_4132_, 3, v___x_4134_);
v___x_4136_ = v___x_4132_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_config_4122_);
lean_ctor_set(v_reuseFailAlloc_4140_, 1, v_extensions_4123_);
lean_ctor_set(v_reuseFailAlloc_4140_, 2, v_extra_4124_);
lean_ctor_set(v_reuseFailAlloc_4140_, 3, v___x_4134_);
lean_ctor_set(v_reuseFailAlloc_4140_, 4, v_extraFacts_4126_);
lean_ctor_set(v_reuseFailAlloc_4140_, 5, v_symPrios_4127_);
lean_ctor_set(v_reuseFailAlloc_4140_, 6, v_norm_4128_);
lean_ctor_set(v_reuseFailAlloc_4140_, 7, v_normProcs_4129_);
lean_ctor_set(v_reuseFailAlloc_4140_, 8, v_anchorRefs_x3f_4130_);
v___x_4136_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4138_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v___x_4136_);
v___x_4138_ = v___x_4120_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
lean_dec_ref(v_params_3798_);
v_a_4143_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4117_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4117_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
case 7:
{
lean_object* v___x_4151_; lean_object* v___x_4153_; 
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
v___x_4151_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3798_, v_a_3991_);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v___x_4151_);
v___x_4153_ = v___x_4007_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4151_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
case 8:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec_ref_known(v_a_4005_, 0);
lean_del_object(v___x_4007_);
lean_dec(v_a_3991_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v___x_4155_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_4156_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4155_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4156_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4156_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
case 9:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
lean_del_object(v___x_4007_);
lean_dec(v_a_3991_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v___x_4165_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_4166_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4165_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4166_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4166_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
case 10:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_dec_ref_known(v_a_4005_, 0);
lean_del_object(v___x_4007_);
lean_dec(v_a_3991_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v___x_4175_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_4176_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4175_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4176_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4176_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
default: 
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_del_object(v___x_4007_);
lean_dec(v_a_3991_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v___x_4185_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
v___x_4186_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4185_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4186_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4186_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
}
}
else
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4203_; 
lean_dec(v_a_3991_);
lean_dec(v_id_3801_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_a_4196_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4198_ = v___x_4004_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4004_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_3800_);
v___y_3916_ = v___x_3999_;
v___y_3917_ = v_a_3991_;
v___y_3918_ = v_a_3805_;
v___y_3919_ = v_a_3806_;
v___y_3920_ = v_a_3807_;
v___y_3921_ = v_a_3808_;
v___y_3922_ = v_a_3809_;
v___y_3923_ = v_a_3810_;
goto v___jp_3915_;
}
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
lean_dec(v_a_3991_);
lean_dec(v_id_3801_);
lean_dec(v_mod_x3f_3800_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_a_4204_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___x_4002_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4002_);
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
}
v___jp_4212_:
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4223_; 
v_a_4214_ = lean_ctor_get(v___y_4213_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___y_4213_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4216_ = v___y_4213_;
v_isShared_4217_ = v_isSharedCheck_4223_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___y_4213_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4223_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
if (lean_obj_tag(v_a_4214_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4220_; 
lean_dec(v_id_3801_);
lean_dec(v_mod_x3f_3800_);
lean_dec(v_p_3799_);
lean_dec_ref(v_params_3798_);
v_a_4218_ = lean_ctor_get(v_a_4214_, 0);
lean_inc(v_a_4218_);
lean_dec_ref_known(v_a_4214_, 1);
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 0, v_a_4218_);
v___x_4220_ = v___x_4216_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4218_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
else
{
lean_object* v_a_4222_; 
lean_del_object(v___x_4216_);
v_a_4222_ = lean_ctor_get(v_a_4214_, 0);
lean_inc(v_a_4222_);
lean_dec_ref_known(v_a_4214_, 1);
v_a_3991_ = v_a_4222_;
goto v___jp_3990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4304_, lean_object* v_p_4305_, lean_object* v_mod_x3f_4306_, lean_object* v_id_4307_, lean_object* v_minIndexable_4308_, lean_object* v_only_4309_, lean_object* v_incremental_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_){
_start:
{
uint8_t v_minIndexable_boxed_4318_; uint8_t v_only_boxed_4319_; uint8_t v_incremental_boxed_4320_; lean_object* v_res_4321_; 
v_minIndexable_boxed_4318_ = lean_unbox(v_minIndexable_4308_);
v_only_boxed_4319_ = lean_unbox(v_only_4309_);
v_incremental_boxed_4320_ = lean_unbox(v_incremental_4310_);
v_res_4321_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4304_, v_p_4305_, v_mod_x3f_4306_, v_id_4307_, v_minIndexable_boxed_4318_, v_only_boxed_4319_, v_incremental_boxed_4320_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
lean_dec(v_a_4314_);
lean_dec_ref(v_a_4313_);
lean_dec(v_a_4312_);
lean_dec_ref(v_a_4311_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4322_, lean_object* v_id_4323_, uint8_t v_minIndexable_4324_, lean_object* v_as_4325_, lean_object* v_as_x27_4326_, lean_object* v_b_4327_, lean_object* v_a_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4322_, v_id_4323_, v_minIndexable_4324_, v_as_x27_4326_, v_b_4327_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4337_, lean_object* v_id_4338_, lean_object* v_minIndexable_4339_, lean_object* v_as_4340_, lean_object* v_as_x27_4341_, lean_object* v_b_4342_, lean_object* v_a_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
uint8_t v_minIndexable_boxed_4351_; lean_object* v_res_4352_; 
v_minIndexable_boxed_4351_ = lean_unbox(v_minIndexable_4339_);
v_res_4352_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4337_, v_id_4338_, v_minIndexable_boxed_4351_, v_as_4340_, v_as_x27_4341_, v_b_4342_, v_a_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec(v_as_x27_4341_);
lean_dec(v_as_4340_);
lean_dec(v_p_4337_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4353_, lean_object* v_as_x27_4354_, lean_object* v_b_4355_, lean_object* v_a_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4354_, v_b_4355_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4365_, lean_object* v_as_x27_4366_, lean_object* v_b_4367_, lean_object* v_a_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4365_, v_as_x27_4366_, v_b_4367_, v_a_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v_as_x27_4366_);
lean_dec(v_as_4365_);
return v_res_4376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4377_, lean_object* v_ref_4378_, lean_object* v_msg_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v___x_4387_; 
v___x_4387_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4378_, v_msg_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4388_, lean_object* v_ref_4389_, lean_object* v_msg_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4388_, v_ref_4389_, v_msg_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec(v_ref_4389_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4399_, lean_object* v_id_4400_, uint8_t v_minIndexable_4401_, lean_object* v_as_4402_, lean_object* v_as_x27_4403_, lean_object* v_b_4404_, lean_object* v_a_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v___x_4413_; 
v___x_4413_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4399_, v_id_4400_, v_minIndexable_4401_, v_as_x27_4403_, v_b_4404_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4414_, lean_object* v_id_4415_, lean_object* v_minIndexable_4416_, lean_object* v_as_4417_, lean_object* v_as_x27_4418_, lean_object* v_b_4419_, lean_object* v_a_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
uint8_t v_minIndexable_boxed_4428_; lean_object* v_res_4429_; 
v_minIndexable_boxed_4428_ = lean_unbox(v_minIndexable_4416_);
v_res_4429_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4414_, v_id_4415_, v_minIndexable_boxed_4428_, v_as_4417_, v_as_x27_4418_, v_b_4419_, v_a_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec(v_as_x27_4418_);
lean_dec(v_as_4417_);
lean_dec(v_p_4414_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4430_, lean_object* v_t_4431_, lean_object* v_k_4432_){
_start:
{
lean_object* v___x_4433_; 
v___x_4433_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4431_, v_k_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4434_, lean_object* v_t_4435_, lean_object* v_k_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4434_, v_t_4435_, v_k_4436_);
lean_dec(v_k_4436_);
lean_dec(v_t_4435_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4438_, lean_object* v_auxDeclToFullName_4439_, lean_object* v___x_4440_, lean_object* v_givenNameView_4441_, lean_object* v_as_4442_, lean_object* v_i_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v___x_4445_; 
v___x_4445_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4438_, v_auxDeclToFullName_4439_, v___x_4440_, v_givenNameView_4441_, v_as_4442_, v_i_4443_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4446_, lean_object* v_auxDeclToFullName_4447_, lean_object* v___x_4448_, lean_object* v_givenNameView_4449_, lean_object* v_as_4450_, lean_object* v_i_4451_, lean_object* v_a_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4446_, v_auxDeclToFullName_4447_, v___x_4448_, v_givenNameView_4449_, v_as_4450_, v_i_4451_, v_a_4452_);
lean_dec_ref(v_as_4450_);
lean_dec(v_auxDeclToFullName_4447_);
lean_dec(v_givenName_4446_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4454_, lean_object* v_givenName_4455_, lean_object* v_as_4456_, lean_object* v_i_4457_, lean_object* v_a_4458_){
_start:
{
lean_object* v___x_4459_; 
v___x_4459_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4454_, v_givenName_4455_, v_as_4456_, v_i_4457_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4460_, lean_object* v_givenName_4461_, lean_object* v_as_4462_, lean_object* v_i_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4460_, v_givenName_4461_, v_as_4462_, v_i_4463_, v_a_4464_);
lean_dec_ref(v_as_4462_);
lean_dec(v_givenName_4461_);
lean_dec(v_localDecl_x3f_4460_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4466_, lean_object* v_auxDeclToFullName_4467_, lean_object* v___x_4468_, lean_object* v_givenNameView_4469_, lean_object* v_as_4470_, lean_object* v_i_4471_, lean_object* v_a_4472_){
_start:
{
lean_object* v___x_4473_; 
v___x_4473_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4466_, v_auxDeclToFullName_4467_, v___x_4468_, v_givenNameView_4469_, v_as_4470_, v_i_4471_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4474_, lean_object* v_auxDeclToFullName_4475_, lean_object* v___x_4476_, lean_object* v_givenNameView_4477_, lean_object* v_as_4478_, lean_object* v_i_4479_, lean_object* v_a_4480_){
_start:
{
lean_object* v_res_4481_; 
v_res_4481_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4474_, v_auxDeclToFullName_4475_, v___x_4476_, v_givenNameView_4477_, v_as_4478_, v_i_4479_, v_a_4480_);
lean_dec_ref(v_as_4478_);
lean_dec(v_auxDeclToFullName_4475_);
lean_dec(v_givenName_4474_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4482_, lean_object* v_givenName_4483_, lean_object* v_as_4484_, lean_object* v_i_4485_, lean_object* v_a_4486_){
_start:
{
lean_object* v___x_4487_; 
v___x_4487_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4482_, v_givenName_4483_, v_as_4484_, v_i_4485_);
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4488_, lean_object* v_givenName_4489_, lean_object* v_as_4490_, lean_object* v_i_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4488_, v_givenName_4489_, v_as_4490_, v_i_4491_, v_a_4492_);
lean_dec_ref(v_as_4490_);
lean_dec(v_givenName_4489_);
lean_dec(v_localDecl_x3f_4488_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v___x_4502_; 
v___x_4502_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4494_, v___y_4499_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec_ref(v_opt_4503_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4512_, lean_object* v_msgData_4513_, uint8_t v_severity_4514_, uint8_t v_isSilent_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4512_, v_msgData_4513_, v_severity_4514_, v_isSilent_4515_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4524_, lean_object* v_msgData_4525_, lean_object* v_severity_4526_, lean_object* v_isSilent_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
uint8_t v_severity_boxed_4535_; uint8_t v_isSilent_boxed_4536_; lean_object* v_res_4537_; 
v_severity_boxed_4535_ = lean_unbox(v_severity_4526_);
v_isSilent_boxed_4536_ = lean_unbox(v_isSilent_4527_);
v_res_4537_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4524_, v_msgData_4525_, v_severity_boxed_4535_, v_isSilent_boxed_4536_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec(v_ref_4524_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4538_, uint8_t v___x_4539_, lean_object* v_b_4540_, lean_object* v_____r_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4549_ = lean_box(0);
lean_inc(v___x_4538_);
v___x_4550_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4538_, v___x_4549_, v___y_4546_, v___y_4547_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; lean_object* v_toCold_4552_; lean_object* v_currRecDepth_4553_; lean_object* v_ref_4554_; uint16_t v_optionFlags_4555_; uint8_t v_suppressElabErrors_4556_; uint8_t v_checkDeprecated_4557_; uint8_t v_isRecordingDeps_4558_; lean_object* v_ref_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc_n(v_a_4551_, 2);
lean_dec_ref_known(v___x_4550_, 1);
v_toCold_4552_ = lean_ctor_get(v___y_4546_, 0);
v_currRecDepth_4553_ = lean_ctor_get(v___y_4546_, 1);
v_ref_4554_ = lean_ctor_get(v___y_4546_, 2);
v_optionFlags_4555_ = lean_ctor_get_uint16(v___y_4546_, sizeof(void*)*3);
v_suppressElabErrors_4556_ = lean_ctor_get_uint8(v___y_4546_, sizeof(void*)*3 + 2);
v_checkDeprecated_4557_ = lean_ctor_get_uint8(v___y_4546_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4558_ = lean_ctor_get_uint8(v___y_4546_, sizeof(void*)*3 + 4);
v_ref_4559_ = l_Lean_replaceRef(v___x_4538_, v_ref_4554_);
lean_dec(v___x_4538_);
lean_inc(v_currRecDepth_4553_);
lean_inc_ref(v_toCold_4552_);
v___x_4560_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4560_, 0, v_toCold_4552_);
lean_ctor_set(v___x_4560_, 1, v_currRecDepth_4553_);
lean_ctor_set(v___x_4560_, 2, v_ref_4559_);
lean_ctor_set_uint16(v___x_4560_, sizeof(void*)*3, v_optionFlags_4555_);
lean_ctor_set_uint8(v___x_4560_, sizeof(void*)*3 + 2, v_suppressElabErrors_4556_);
lean_ctor_set_uint8(v___x_4560_, sizeof(void*)*3 + 3, v_checkDeprecated_4557_);
lean_ctor_set_uint8(v___x_4560_, sizeof(void*)*3 + 4, v_isRecordingDeps_4558_);
v___x_4561_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4551_, v___x_4539_, v___y_4544_, v___y_4545_, v___x_4560_, v___y_4547_);
lean_dec_ref_known(v___x_4560_, 3);
if (lean_obj_tag(v___x_4561_) == 0)
{
uint8_t v___x_4562_; lean_object* v___x_4563_; 
lean_dec_ref_known(v___x_4561_, 1);
v___x_4562_ = 0;
lean_inc(v_a_4551_);
v___x_4563_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4551_, v___x_4562_, v___y_4546_, v___y_4547_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4623_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4566_ = v___x_4563_;
v_isShared_4567_ = v_isSharedCheck_4623_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4563_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4623_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
if (lean_obj_tag(v_a_4564_) == 1)
{
lean_object* v_val_4568_; lean_object* v___x_4569_; 
lean_del_object(v___x_4566_);
lean_dec(v_a_4551_);
v_val_4568_ = lean_ctor_get(v_a_4564_, 0);
lean_inc_n(v_val_4568_, 2);
lean_dec_ref_known(v_a_4564_, 1);
v___x_4569_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4568_, v___y_4546_, v___y_4547_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v___x_4570_; 
lean_dec_ref_known(v___x_4569_, 1);
v___x_4570_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4540_, v_val_4568_, v___y_4546_, v___y_4547_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4580_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4573_ = v___x_4570_;
v_isShared_4574_ = v_isSharedCheck_4580_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4570_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4580_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4578_; 
v___x_4575_ = lean_box(0);
v___x_4576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4575_);
lean_ctor_set(v___x_4576_, 1, v_a_4571_);
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 0, v___x_4576_);
v___x_4578_ = v___x_4573_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v___x_4576_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
else
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4588_; 
v_a_4581_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4583_ = v___x_4570_;
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v___x_4570_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4586_; 
if (v_isShared_4584_ == 0)
{
v___x_4586_ = v___x_4583_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_a_4581_);
v___x_4586_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
return v___x_4586_;
}
}
}
}
else
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
lean_dec(v_val_4568_);
lean_dec_ref(v_b_4540_);
v_a_4589_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4591_ = v___x_4569_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___x_4569_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_a_4589_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
else
{
uint8_t v___x_4597_; 
lean_dec(v_a_4564_);
lean_inc(v_a_4551_);
v___x_4597_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4540_, v_a_4551_);
if (v___x_4597_ == 0)
{
lean_object* v___x_4598_; 
lean_del_object(v___x_4566_);
v___x_4598_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4540_, v_a_4551_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4608_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4601_ = v___x_4598_;
v_isShared_4602_ = v_isSharedCheck_4608_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4598_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4608_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4606_; 
v___x_4603_ = lean_box(0);
v___x_4604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4604_, 0, v___x_4603_);
lean_ctor_set(v___x_4604_, 1, v_a_4599_);
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v___x_4604_);
v___x_4606_ = v___x_4601_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4604_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
else
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4616_; 
v_a_4609_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4611_ = v___x_4598_;
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4598_);
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
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4621_; 
v___x_4617_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4540_, v_a_4551_);
v___x_4618_ = lean_box(0);
v___x_4619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4618_);
lean_ctor_set(v___x_4619_, 1, v___x_4617_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 0, v___x_4619_);
v___x_4621_ = v___x_4566_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4619_);
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
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
lean_dec(v_a_4551_);
lean_dec_ref(v_b_4540_);
v_a_4624_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4563_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4563_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
else
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
lean_dec(v_a_4551_);
lean_dec_ref(v_b_4540_);
v_a_4632_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4634_ = v___x_4561_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4561_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4632_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
}
else
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4647_; 
lean_dec_ref(v_b_4540_);
lean_dec(v___x_4538_);
v_a_4640_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4642_ = v___x_4550_;
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4550_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4645_; 
if (v_isShared_4643_ == 0)
{
v___x_4645_ = v___x_4642_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4640_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4648_, lean_object* v___x_4649_, lean_object* v_b_4650_, lean_object* v_____r_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
uint8_t v___x_18543__boxed_4659_; lean_object* v_res_4660_; 
v___x_18543__boxed_4659_ = lean_unbox(v___x_4649_);
v_res_4660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4648_, v___x_18543__boxed_4659_, v_b_4650_, v_____r_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4664_, lean_object* v_b_4665_, lean_object* v_a_4666_, uint8_t v___x_4667_, uint8_t v_only_4668_, uint8_t v_incremental_4669_, lean_object* v_x_4670_, lean_object* v_mod_x3f_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_){
_start:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___y_4682_; lean_object* v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___x_4707_; uint8_t v___x_4708_; 
v___x_4679_ = lean_unsigned_to_nat(1u);
v___x_4680_ = l_Lean_Syntax_getArg(v___x_4664_, v___x_4679_);
v___x_4707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4680_);
v___x_4708_ = l_Lean_Syntax_isOfKind(v___x_4680_, v___x_4707_);
if (v___x_4708_ == 0)
{
lean_object* v___x_4709_; 
v___x_4709_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4665_, v_a_4666_, v_mod_x3f_4671_, v___x_4680_, v___x_4667_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4719_; 
v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4712_ = v___x_4709_;
v_isShared_4713_ = v_isSharedCheck_4719_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4709_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4719_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4717_; 
v___x_4714_ = lean_box(0);
v___x_4715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
lean_ctor_set(v___x_4715_, 1, v_a_4710_);
if (v_isShared_4713_ == 0)
{
lean_ctor_set(v___x_4712_, 0, v___x_4715_);
v___x_4717_ = v___x_4712_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v___x_4715_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
return v___x_4717_;
}
}
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
v_a_4720_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4709_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4709_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
else
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4728_ = l_Lean_TSyntax_getId(v___x_4680_);
v___x_4729_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4728_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
lean_inc(v_a_4730_);
lean_dec_ref_known(v___x_4729_, 1);
if (lean_obj_tag(v_a_4730_) == 1)
{
lean_object* v_val_4731_; lean_object* v_snd_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4757_; 
v_val_4731_ = lean_ctor_get(v_a_4730_, 0);
lean_inc(v_val_4731_);
lean_dec_ref_known(v_a_4730_, 1);
v_snd_4732_ = lean_ctor_get(v_val_4731_, 1);
v_isSharedCheck_4757_ = !lean_is_exclusive(v_val_4731_);
if (v_isSharedCheck_4757_ == 0)
{
lean_object* v_unused_4758_; 
v_unused_4758_ = lean_ctor_get(v_val_4731_, 0);
lean_dec(v_unused_4758_);
v___x_4734_ = v_val_4731_;
v_isShared_4735_ = v_isSharedCheck_4757_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_snd_4732_);
lean_dec(v_val_4731_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4757_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
if (lean_obj_tag(v_snd_4732_) == 1)
{
lean_object* v___x_4736_; 
lean_dec_ref_known(v_snd_4732_, 2);
v___x_4736_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4665_, v_a_4666_, v_mod_x3f_4671_, v___x_4680_, v___x_4667_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4748_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4739_ = v___x_4736_;
v_isShared_4740_ = v_isSharedCheck_4748_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4736_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4748_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4741_; lean_object* v___x_4743_; 
v___x_4741_ = lean_box(0);
if (v_isShared_4735_ == 0)
{
lean_ctor_set(v___x_4734_, 1, v_a_4737_);
lean_ctor_set(v___x_4734_, 0, v___x_4741_);
v___x_4743_ = v___x_4734_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v___x_4741_);
lean_ctor_set(v_reuseFailAlloc_4747_, 1, v_a_4737_);
v___x_4743_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
lean_object* v___x_4745_; 
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v___x_4743_);
v___x_4745_ = v___x_4739_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v___x_4743_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
}
else
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4756_; 
lean_del_object(v___x_4734_);
v_a_4749_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4751_ = v___x_4736_;
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4736_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4749_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
}
else
{
lean_del_object(v___x_4734_);
lean_dec(v_snd_4732_);
v___y_4682_ = v___y_4672_;
v___y_4683_ = v___y_4673_;
v___y_4684_ = v___y_4674_;
v___y_4685_ = v___y_4675_;
v___y_4686_ = v___y_4676_;
v___y_4687_ = v___y_4677_;
goto v___jp_4681_;
}
}
}
else
{
lean_dec(v_a_4730_);
v___y_4682_ = v___y_4672_;
v___y_4683_ = v___y_4673_;
v___y_4684_ = v___y_4674_;
v___y_4685_ = v___y_4675_;
v___y_4686_ = v___y_4676_;
v___y_4687_ = v___y_4677_;
goto v___jp_4681_;
}
}
else
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4766_; 
lean_dec(v___x_4680_);
lean_dec(v_mod_x3f_4671_);
lean_dec(v_a_4666_);
lean_dec_ref(v_b_4665_);
v_a_4759_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4761_ = v___x_4729_;
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4729_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
v___jp_4681_:
{
lean_object* v___x_4688_; 
v___x_4688_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4665_, v_a_4666_, v_mod_x3f_4671_, v___x_4680_, v___x_4667_, v_only_4668_, v_incremental_4669_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4698_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4691_ = v___x_4688_;
v_isShared_4692_ = v_isSharedCheck_4698_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4688_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4698_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4696_; 
v___x_4693_ = lean_box(0);
v___x_4694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4694_, 0, v___x_4693_);
lean_ctor_set(v___x_4694_, 1, v_a_4689_);
if (v_isShared_4692_ == 0)
{
lean_ctor_set(v___x_4691_, 0, v___x_4694_);
v___x_4696_ = v___x_4691_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4694_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
return v___x_4696_;
}
}
}
else
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4706_; 
v_a_4699_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4701_ = v___x_4688_;
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4688_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4704_; 
if (v_isShared_4702_ == 0)
{
v___x_4704_ = v___x_4701_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4699_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4767_, lean_object* v_b_4768_, lean_object* v_a_4769_, lean_object* v___x_4770_, lean_object* v_only_4771_, lean_object* v_incremental_4772_, lean_object* v_x_4773_, lean_object* v_mod_x3f_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
uint8_t v___x_18763__boxed_4782_; uint8_t v_only_boxed_4783_; uint8_t v_incremental_boxed_4784_; lean_object* v_res_4785_; 
v___x_18763__boxed_4782_ = lean_unbox(v___x_4770_);
v_only_boxed_4783_ = lean_unbox(v_only_4771_);
v_incremental_boxed_4784_ = lean_unbox(v_incremental_4772_);
v_res_4785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4767_, v_b_4768_, v_a_4769_, v___x_18763__boxed_4782_, v_only_boxed_4783_, v_incremental_boxed_4784_, v_x_4773_, v_mod_x3f_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v___x_4767_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4786_, lean_object* v___x_4787_, lean_object* v_____r_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_){
_start:
{
lean_object* v___x_4796_; 
v___x_4796_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4786_, v___x_4787_, v___y_4793_, v___y_4794_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4815_, lean_object* v___x_4816_, lean_object* v_____r_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4815_, v___x_4816_, v_____r_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
lean_dec(v___y_4821_);
lean_dec_ref(v___y_4820_);
lean_dec(v___y_4819_);
lean_dec_ref(v___y_4818_);
lean_dec(v___x_4816_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4826_, lean_object* v_b_4827_, lean_object* v_a_4828_, uint8_t v___x_4829_, uint8_t v_only_4830_, uint8_t v_incremental_4831_, lean_object* v_x_4832_, lean_object* v_mod_x3f_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___y_4844_; lean_object* v___y_4845_; lean_object* v___y_4846_; lean_object* v___y_4847_; lean_object* v___y_4848_; lean_object* v___y_4849_; lean_object* v___x_4869_; uint8_t v___x_4870_; 
v___x_4841_ = lean_unsigned_to_nat(2u);
v___x_4842_ = l_Lean_Syntax_getArg(v___x_4826_, v___x_4841_);
v___x_4869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4842_);
v___x_4870_ = l_Lean_Syntax_isOfKind(v___x_4842_, v___x_4869_);
if (v___x_4870_ == 0)
{
lean_object* v___x_4871_; 
v___x_4871_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4827_, v_a_4828_, v_mod_x3f_4833_, v___x_4842_, v___x_4829_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4881_; 
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4874_ = v___x_4871_;
v_isShared_4875_ = v_isSharedCheck_4881_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4871_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4881_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4879_; 
v___x_4876_ = lean_box(0);
v___x_4877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4876_);
lean_ctor_set(v___x_4877_, 1, v_a_4872_);
if (v_isShared_4875_ == 0)
{
lean_ctor_set(v___x_4874_, 0, v___x_4877_);
v___x_4879_ = v___x_4874_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4877_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
else
{
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4889_; 
v_a_4882_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4884_ = v___x_4871_;
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4871_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4887_; 
if (v_isShared_4885_ == 0)
{
v___x_4887_ = v___x_4884_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
else
{
lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4890_ = l_Lean_TSyntax_getId(v___x_4842_);
v___x_4891_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4890_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4891_) == 0)
{
lean_object* v_a_4892_; 
v_a_4892_ = lean_ctor_get(v___x_4891_, 0);
lean_inc(v_a_4892_);
lean_dec_ref_known(v___x_4891_, 1);
if (lean_obj_tag(v_a_4892_) == 1)
{
lean_object* v_val_4893_; lean_object* v_snd_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4919_; 
v_val_4893_ = lean_ctor_get(v_a_4892_, 0);
lean_inc(v_val_4893_);
lean_dec_ref_known(v_a_4892_, 1);
v_snd_4894_ = lean_ctor_get(v_val_4893_, 1);
v_isSharedCheck_4919_ = !lean_is_exclusive(v_val_4893_);
if (v_isSharedCheck_4919_ == 0)
{
lean_object* v_unused_4920_; 
v_unused_4920_ = lean_ctor_get(v_val_4893_, 0);
lean_dec(v_unused_4920_);
v___x_4896_ = v_val_4893_;
v_isShared_4897_ = v_isSharedCheck_4919_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_snd_4894_);
lean_dec(v_val_4893_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4919_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
if (lean_obj_tag(v_snd_4894_) == 1)
{
lean_object* v___x_4898_; 
lean_dec_ref_known(v_snd_4894_, 2);
v___x_4898_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4827_, v_a_4828_, v_mod_x3f_4833_, v___x_4842_, v___x_4829_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4910_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4901_ = v___x_4898_;
v_isShared_4902_ = v_isSharedCheck_4910_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4898_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4910_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4903_; lean_object* v___x_4905_; 
v___x_4903_ = lean_box(0);
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 1, v_a_4899_);
lean_ctor_set(v___x_4896_, 0, v___x_4903_);
v___x_4905_ = v___x_4896_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4903_);
lean_ctor_set(v_reuseFailAlloc_4909_, 1, v_a_4899_);
v___x_4905_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
lean_object* v___x_4907_; 
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v___x_4905_);
v___x_4907_ = v___x_4901_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4905_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
else
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4918_; 
lean_del_object(v___x_4896_);
v_a_4911_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4913_ = v___x_4898_;
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___x_4898_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4916_; 
if (v_isShared_4914_ == 0)
{
v___x_4916_ = v___x_4913_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4911_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
}
}
else
{
lean_del_object(v___x_4896_);
lean_dec(v_snd_4894_);
v___y_4844_ = v___y_4834_;
v___y_4845_ = v___y_4835_;
v___y_4846_ = v___y_4836_;
v___y_4847_ = v___y_4837_;
v___y_4848_ = v___y_4838_;
v___y_4849_ = v___y_4839_;
goto v___jp_4843_;
}
}
}
else
{
lean_dec(v_a_4892_);
v___y_4844_ = v___y_4834_;
v___y_4845_ = v___y_4835_;
v___y_4846_ = v___y_4836_;
v___y_4847_ = v___y_4837_;
v___y_4848_ = v___y_4838_;
v___y_4849_ = v___y_4839_;
goto v___jp_4843_;
}
}
else
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4928_; 
lean_dec(v___x_4842_);
lean_dec(v_mod_x3f_4833_);
lean_dec(v_a_4828_);
lean_dec_ref(v_b_4827_);
v_a_4921_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4923_ = v___x_4891_;
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4891_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4926_; 
if (v_isShared_4924_ == 0)
{
v___x_4926_ = v___x_4923_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
v___jp_4843_:
{
lean_object* v___x_4850_; 
v___x_4850_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4827_, v_a_4828_, v_mod_x3f_4833_, v___x_4842_, v___x_4829_, v_only_4830_, v_incremental_4831_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4860_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4853_ = v___x_4850_;
v_isShared_4854_ = v_isSharedCheck_4860_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_a_4851_);
lean_dec(v___x_4850_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4860_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4858_; 
v___x_4855_ = lean_box(0);
v___x_4856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
lean_ctor_set(v___x_4856_, 1, v_a_4851_);
if (v_isShared_4854_ == 0)
{
lean_ctor_set(v___x_4853_, 0, v___x_4856_);
v___x_4858_ = v___x_4853_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4856_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
else
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
v_a_4861_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4863_ = v___x_4850_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4850_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4929_, lean_object* v_b_4930_, lean_object* v_a_4931_, lean_object* v___x_4932_, lean_object* v_only_4933_, lean_object* v_incremental_4934_, lean_object* v_x_4935_, lean_object* v_mod_x3f_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_){
_start:
{
uint8_t v___x_19042__boxed_4944_; uint8_t v_only_boxed_4945_; uint8_t v_incremental_boxed_4946_; lean_object* v_res_4947_; 
v___x_19042__boxed_4944_ = lean_unbox(v___x_4932_);
v_only_boxed_4945_ = lean_unbox(v_only_4933_);
v_incremental_boxed_4946_ = lean_unbox(v_incremental_4934_);
v_res_4947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4929_, v_b_4930_, v_a_4931_, v___x_19042__boxed_4944_, v_only_boxed_4945_, v_incremental_boxed_4946_, v_x_4935_, v_mod_x3f_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
lean_dec(v___y_4942_);
lean_dec_ref(v___y_4941_);
lean_dec(v___y_4940_);
lean_dec_ref(v___y_4939_);
lean_dec(v___y_4938_);
lean_dec_ref(v___y_4937_);
lean_dec(v___x_4929_);
return v_res_4947_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___x_4955_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4956_ = l_Lean_stringToMessageData(v___x_4955_);
return v___x_4956_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15(void){
_start:
{
lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14));
v___x_4986_ = l_Lean_stringToMessageData(v___x_4985_);
return v___x_4986_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4989_ = l_Lean_stringToMessageData(v___x_4988_);
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4990_, uint8_t v_only_4991_, uint8_t v_incremental_4992_, lean_object* v_as_4993_, size_t v_sz_4994_, size_t v_i_4995_, lean_object* v_b_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_){
_start:
{
lean_object* v_snd_5005_; lean_object* v_a_5010_; lean_object* v___y_5017_; uint8_t v___x_5021_; 
v___x_5021_ = lean_usize_dec_lt(v_i_4995_, v_sz_4994_);
if (v___x_5021_ == 0)
{
lean_object* v___x_5022_; 
v___x_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5022_, 0, v_b_4996_);
return v___x_5022_;
}
else
{
lean_object* v_a_5023_; lean_object* v___x_5024_; uint8_t v___x_5025_; 
v_a_5023_ = lean_array_uget_borrowed(v_as_4993_, v_i_4995_);
v___x_5024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_5023_);
v___x_5025_ = l_Lean_Syntax_isOfKind(v_a_5023_, v___x_5024_);
if (v___x_5025_ == 0)
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5026_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5023_);
v___x_5027_ = l_Lean_MessageData_ofSyntax(v_a_5023_);
v___x_5028_ = l_Lean_indentD(v___x_5027_);
v___x_5029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5029_, 0, v___x_5026_);
lean_ctor_set(v___x_5029_, 1, v___x_5028_);
v___x_5030_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5029_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_dec_ref_known(v___x_5030_, 1);
v_snd_5005_ = v_b_4996_;
goto v___jp_5004_;
}
else
{
lean_object* v_a_5031_; 
v_a_5031_ = lean_ctor_get(v___x_5030_, 0);
lean_inc(v_a_5031_);
lean_dec_ref_known(v___x_5030_, 1);
v_a_5010_ = v_a_5031_;
goto v___jp_5009_;
}
}
else
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; uint8_t v___x_5035_; 
v___x_5032_ = lean_unsigned_to_nat(0u);
v___x_5033_ = l_Lean_Syntax_getArg(v_a_5023_, v___x_5032_);
v___x_5034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_5033_);
v___x_5035_ = l_Lean_Syntax_isOfKind(v___x_5033_, v___x_5034_);
if (v___x_5035_ == 0)
{
lean_object* v___x_5036_; uint8_t v___x_5037_; 
v___x_5036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_5033_);
v___x_5037_ = l_Lean_Syntax_isOfKind(v___x_5033_, v___x_5036_);
if (v___x_5037_ == 0)
{
lean_object* v___x_5038_; uint8_t v___x_5039_; 
v___x_5038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_5033_);
v___x_5039_ = l_Lean_Syntax_isOfKind(v___x_5033_, v___x_5038_);
if (v___x_5039_ == 0)
{
lean_object* v___x_5040_; uint8_t v___x_5041_; 
v___x_5040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_5033_);
v___x_5041_ = l_Lean_Syntax_isOfKind(v___x_5033_, v___x_5040_);
if (v___x_5041_ == 0)
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
lean_dec(v___x_5033_);
v___x_5042_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5023_);
v___x_5043_ = l_Lean_MessageData_ofSyntax(v_a_5023_);
v___x_5044_ = l_Lean_indentD(v___x_5043_);
v___x_5045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5045_, 0, v___x_5042_);
lean_ctor_set(v___x_5045_, 1, v___x_5044_);
v___x_5046_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5045_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5046_) == 0)
{
lean_dec_ref_known(v___x_5046_, 1);
v_snd_5005_ = v_b_4996_;
goto v___jp_5004_;
}
else
{
lean_object* v_a_5047_; 
v_a_5047_ = lean_ctor_get(v___x_5046_, 0);
lean_inc(v_a_5047_);
lean_dec_ref_known(v___x_5046_, 1);
v_a_5010_ = v_a_5047_;
goto v___jp_5009_;
}
}
else
{
lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; uint8_t v___x_5051_; 
v___x_5048_ = lean_unsigned_to_nat(1u);
v___x_5049_ = l_Lean_Syntax_getArg(v___x_5033_, v___x_5048_);
lean_dec(v___x_5033_);
v___x_5050_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13));
lean_inc(v___x_5049_);
v___x_5051_ = l_Lean_Syntax_isOfKind(v___x_5049_, v___x_5050_);
if (v___x_5051_ == 0)
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
lean_dec(v___x_5049_);
v___x_5052_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5023_);
v___x_5053_ = l_Lean_MessageData_ofSyntax(v_a_5023_);
v___x_5054_ = l_Lean_indentD(v___x_5053_);
v___x_5055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5055_, 0, v___x_5052_);
lean_ctor_set(v___x_5055_, 1, v___x_5054_);
v___x_5056_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5055_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5056_) == 0)
{
lean_dec_ref_known(v___x_5056_, 1);
v_snd_5005_ = v_b_4996_;
goto v___jp_5004_;
}
else
{
lean_object* v_a_5057_; 
v_a_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc(v_a_5057_);
lean_dec_ref_known(v___x_5056_, 1);
v_a_5010_ = v_a_5057_;
goto v___jp_5009_;
}
}
else
{
if (v_only_4991_ == 0)
{
lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5058_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15);
v___x_5059_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_5049_, v___x_5058_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5059_) == 0)
{
lean_object* v_a_5060_; lean_object* v___x_5061_; 
v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
lean_inc(v_a_5060_);
lean_dec_ref_known(v___x_5059_, 1);
lean_inc_ref(v_b_4996_);
v___x_5061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4996_, v___x_5049_, v_a_5060_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec(v___x_5049_);
v___y_5017_ = v___x_5061_;
goto v___jp_5016_;
}
else
{
lean_object* v_a_5062_; 
lean_dec(v___x_5049_);
v_a_5062_ = lean_ctor_get(v___x_5059_, 0);
lean_inc(v_a_5062_);
lean_dec_ref_known(v___x_5059_, 1);
v_a_5010_ = v_a_5062_;
goto v___jp_5009_;
}
}
else
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = lean_box(0);
lean_inc_ref(v_b_4996_);
v___x_5064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4996_, v___x_5049_, v___x_5063_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec(v___x_5049_);
v___y_5017_ = v___x_5064_;
goto v___jp_5016_;
}
}
}
}
else
{
lean_object* v___x_5065_; lean_object* v___x_5066_; uint8_t v___x_5067_; 
v___x_5065_ = lean_unsigned_to_nat(1u);
v___x_5066_ = l_Lean_Syntax_getArg(v___x_5033_, v___x_5065_);
v___x_5067_ = l_Lean_Syntax_isNone(v___x_5066_);
if (v___x_5067_ == 0)
{
uint8_t v___x_5068_; 
lean_inc(v___x_5066_);
v___x_5068_ = l_Lean_Syntax_matchesNull(v___x_5066_, v___x_5065_);
if (v___x_5068_ == 0)
{
lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
lean_dec(v___x_5066_);
lean_dec(v___x_5033_);
v___x_5069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5023_);
v___x_5070_ = l_Lean_MessageData_ofSyntax(v_a_5023_);
v___x_5071_ = l_Lean_indentD(v___x_5070_);
v___x_5072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5069_);
lean_ctor_set(v___x_5072_, 1, v___x_5071_);
v___x_5073_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5072_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_dec_ref_known(v___x_5073_, 1);
v_snd_5005_ = v_b_4996_;
goto v___jp_5004_;
}
else
{
lean_object* v_a_5074_; 
v_a_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_a_5074_);
lean_dec_ref_known(v___x_5073_, 1);
v_a_5010_ = v_a_5074_;
goto v___jp_5009_;
}
}
else
{
lean_object* v___x_5075_; lean_object* v___x_5076_; uint8_t v___x_5077_; 
v___x_5075_ = l_Lean_Syntax_getArg(v___x_5066_, v___x_5032_);
lean_dec(v___x_5066_);
v___x_5076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_5075_);
v___x_5077_ = l_Lean_Syntax_isOfKind(v___x_5075_, v___x_5076_);
if (v___x_5077_ == 0)
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
lean_dec(v___x_5075_);
lean_dec(v___x_5033_);
v___x_5078_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5023_);
v___x_5079_ = l_Lean_MessageData_ofSyntax(v_a_5023_);
v___x_5080_ = l_Lean_indentD(v___x_5079_);
v___x_5081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5081_, 0, v___x_5078_);
lean_ctor_set(v___x_5081_, 1, v___x_5080_);
v___x_5082_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5081_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_dec_ref_known(v___x_5082_, 1);
v_snd_5005_ = v_b_4996_;
goto v___jp_5004_;
}
else
{
lean_object* v_a_5083_; 
v_a_5083_ = lean_ctor_get(v___x_5082_, 0);
lean_inc(v_a_5083_);
lean_dec_ref_known(v___x_5082_, 1);
v_a_5010_ = v_a_5083_;
goto v___jp_5009_;
}
}
else
{
lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5084_ = lean_box(0);
v___x_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5085_, 0, v___x_5075_);
lean_inc(v_a_5023_);
lean_inc_ref(v_b_4996_);
v___x_5086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_5033_, v_b_4996_, v_a_5023_, v___x_5025_, v_only_4991_, v_incremental_4992_, v___x_5084_, v___x_5085_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec(v___x_5033_);
v___y_5017_ = v___x_5086_;
goto v___jp_5016_;
}
}
}
else
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
lean_dec(v___x_5066_);
v___x_5087_ = lean_box(0);
v___x_5088_ = lean_box(0);
lean_inc(v_a_5023_);
lean_inc_ref(v_b_4996_);
v___x_5089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_5033_, v_b_4996_, v_a_5023_, v___x_5025_, v_only_4991_, v_incremental_4992_, v___x_5087_, v___x_5088_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec(v___x_5033_);
v___y_5017_ = v___x_5089_;
goto v___jp_5016_;
}
}
}
else
{
lean_object* v___x_5090_; uint8_t v___x_5091_; 
v___x_5090_ = l_Lean_Syntax_getArg(v___x_5033_, v___x_5032_);
v___x_5091_ = l_Lean_Syntax_isNone(v___x_5090_);
if (v___x_5091_ == 0)
{
lean_object* v___x_5092_; uint8_t v___x_5093_; 
v___x_5092_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_5090_);
v___x_5093_ = l_Lean_Syntax_matchesNull(v___x_5090_, v___x_5092_);
if (v___x_5093_ == 0)
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; 
lean_dec(v___x_5090_);
lean_dec(v___x_5033_);
v___x_5094_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5023_);
v___x_5095_ = l_Lean_MessageData_ofSyntax(v_a_5023_);
v___x_5096_ = l_Lean_indentD(v___x_5095_);
v___x_5097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5097_, 0, v___x_5094_);
lean_ctor_set(v___x_5097_, 1, v___x_5096_);
v___x_5098_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5097_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5098_) == 0)
{
lean_dec_ref_known(v___x_5098_, 1);
v_snd_5005_ = v_b_4996_;
goto v___jp_5004_;
}
else
{
lean_object* v_a_5099_; 
v_a_5099_ = lean_ctor_get(v___x_5098_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v___x_5098_, 1);
v_a_5010_ = v_a_5099_;
goto v___jp_5009_;
}
}
else
{
lean_object* v___x_5100_; lean_object* v___x_5101_; uint8_t v___x_5102_; 
v___x_5100_ = l_Lean_Syntax_getArg(v___x_5090_, v___x_5032_);
lean_dec(v___x_5090_);
v___x_5101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_5100_);
v___x_5102_ = l_Lean_Syntax_isOfKind(v___x_5100_, v___x_5101_);
if (v___x_5102_ == 0)
{
lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
lean_dec(v___x_5100_);
lean_dec(v___x_5033_);
v___x_5103_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5023_);
v___x_5104_ = l_Lean_MessageData_ofSyntax(v_a_5023_);
v___x_5105_ = l_Lean_indentD(v___x_5104_);
v___x_5106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5103_);
lean_ctor_set(v___x_5106_, 1, v___x_5105_);
v___x_5107_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5106_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_dec_ref_known(v___x_5107_, 1);
v_snd_5005_ = v_b_4996_;
goto v___jp_5004_;
}
else
{
lean_object* v_a_5108_; 
v_a_5108_ = lean_ctor_get(v___x_5107_, 0);
lean_inc(v_a_5108_);
lean_dec_ref_known(v___x_5107_, 1);
v_a_5010_ = v_a_5108_;
goto v___jp_5009_;
}
}
else
{
lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; 
v___x_5109_ = lean_box(0);
v___x_5110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5110_, 0, v___x_5100_);
lean_inc(v_a_5023_);
lean_inc_ref(v_b_4996_);
v___x_5111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_5033_, v_b_4996_, v_a_5023_, v___x_5035_, v_only_4991_, v_incremental_4992_, v___x_5109_, v___x_5110_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec(v___x_5033_);
v___y_5017_ = v___x_5111_;
goto v___jp_5016_;
}
}
}
else
{
lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; 
lean_dec(v___x_5090_);
v___x_5112_ = lean_box(0);
v___x_5113_ = lean_box(0);
lean_inc(v_a_5023_);
lean_inc_ref(v_b_4996_);
v___x_5114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_5033_, v_b_4996_, v_a_5023_, v___x_5035_, v_only_4991_, v_incremental_4992_, v___x_5112_, v___x_5113_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec(v___x_5033_);
v___y_5017_ = v___x_5114_;
goto v___jp_5016_;
}
}
}
else
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; uint8_t v___x_5118_; 
v___x_5115_ = lean_unsigned_to_nat(1u);
v___x_5116_ = l_Lean_Syntax_getArg(v___x_5033_, v___x_5115_);
lean_dec(v___x_5033_);
v___x_5117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_5116_);
v___x_5118_ = l_Lean_Syntax_isOfKind(v___x_5116_, v___x_5117_);
if (v___x_5118_ == 0)
{
lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; 
lean_dec(v___x_5116_);
v___x_5119_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5023_);
v___x_5120_ = l_Lean_MessageData_ofSyntax(v_a_5023_);
v___x_5121_ = l_Lean_indentD(v___x_5120_);
v___x_5122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5122_, 0, v___x_5119_);
lean_ctor_set(v___x_5122_, 1, v___x_5121_);
v___x_5123_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5122_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5123_) == 0)
{
lean_dec_ref_known(v___x_5123_, 1);
v_snd_5005_ = v_b_4996_;
goto v___jp_5004_;
}
else
{
lean_object* v_a_5124_; 
v_a_5124_ = lean_ctor_get(v___x_5123_, 0);
lean_inc(v_a_5124_);
lean_dec_ref_known(v___x_5123_, 1);
v_a_5010_ = v_a_5124_;
goto v___jp_5009_;
}
}
else
{
if (v_incremental_4992_ == 0)
{
lean_object* v___x_5125_; lean_object* v___x_5126_; 
v___x_5125_ = lean_box(0);
lean_inc_ref(v_b_4996_);
v___x_5126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_5116_, v___x_5025_, v_b_4996_, v___x_5125_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
v___y_5017_ = v___x_5126_;
goto v___jp_5016_;
}
else
{
lean_object* v___x_5127_; lean_object* v___x_5128_; 
v___x_5127_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_5128_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_5023_, v___x_5127_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5128_) == 0)
{
lean_object* v_a_5129_; lean_object* v___x_5130_; 
v_a_5129_ = lean_ctor_get(v___x_5128_, 0);
lean_inc(v_a_5129_);
lean_dec_ref_known(v___x_5128_, 1);
lean_inc_ref(v_b_4996_);
v___x_5130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_5116_, v___x_5025_, v_b_4996_, v_a_5129_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
v___y_5017_ = v___x_5130_;
goto v___jp_5016_;
}
else
{
lean_object* v_a_5131_; 
lean_dec(v___x_5116_);
v_a_5131_ = lean_ctor_get(v___x_5128_, 0);
lean_inc(v_a_5131_);
lean_dec_ref_known(v___x_5128_, 1);
v_a_5010_ = v_a_5131_;
goto v___jp_5009_;
}
}
}
}
}
}
v___jp_5004_:
{
size_t v___x_5006_; size_t v___x_5007_; 
v___x_5006_ = ((size_t)1ULL);
v___x_5007_ = lean_usize_add(v_i_4995_, v___x_5006_);
v_i_4995_ = v___x_5007_;
v_b_4996_ = v_snd_5005_;
goto _start;
}
v___jp_5009_:
{
uint8_t v___x_5011_; 
v___x_5011_ = l_Lean_Exception_isInterrupt(v_a_5010_);
if (v___x_5011_ == 0)
{
uint8_t v___x_5012_; 
lean_inc_ref(v_a_5010_);
v___x_5012_ = l_Lean_Exception_isRuntime(v_a_5010_);
if (v___x_5012_ == 0)
{
if (v_lax_4990_ == 0)
{
lean_object* v___x_5013_; 
lean_dec_ref(v_b_4996_);
v___x_5013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5013_, 0, v_a_5010_);
return v___x_5013_;
}
else
{
lean_dec_ref(v_a_5010_);
v_snd_5005_ = v_b_4996_;
goto v___jp_5004_;
}
}
else
{
lean_object* v___x_5014_; 
lean_dec_ref(v_b_4996_);
v___x_5014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5014_, 0, v_a_5010_);
return v___x_5014_;
}
}
else
{
lean_object* v___x_5015_; 
lean_dec_ref(v_b_4996_);
v___x_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5015_, 0, v_a_5010_);
return v___x_5015_;
}
}
v___jp_5016_:
{
if (lean_obj_tag(v___y_5017_) == 0)
{
lean_object* v_a_5018_; lean_object* v_snd_5019_; 
lean_dec_ref(v_b_4996_);
v_a_5018_ = lean_ctor_get(v___y_5017_, 0);
lean_inc(v_a_5018_);
lean_dec_ref_known(v___y_5017_, 1);
v_snd_5019_ = lean_ctor_get(v_a_5018_, 1);
lean_inc(v_snd_5019_);
lean_dec(v_a_5018_);
v_snd_5005_ = v_snd_5019_;
goto v___jp_5004_;
}
else
{
lean_object* v_a_5020_; 
v_a_5020_ = lean_ctor_get(v___y_5017_, 0);
lean_inc(v_a_5020_);
lean_dec_ref_known(v___y_5017_, 1);
v_a_5010_ = v_a_5020_;
goto v___jp_5009_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_5132_, lean_object* v_only_5133_, lean_object* v_incremental_5134_, lean_object* v_as_5135_, lean_object* v_sz_5136_, lean_object* v_i_5137_, lean_object* v_b_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_){
_start:
{
uint8_t v_lax_boxed_5146_; uint8_t v_only_boxed_5147_; uint8_t v_incremental_boxed_5148_; size_t v_sz_boxed_5149_; size_t v_i_boxed_5150_; lean_object* v_res_5151_; 
v_lax_boxed_5146_ = lean_unbox(v_lax_5132_);
v_only_boxed_5147_ = lean_unbox(v_only_5133_);
v_incremental_boxed_5148_ = lean_unbox(v_incremental_5134_);
v_sz_boxed_5149_ = lean_unbox_usize(v_sz_5136_);
lean_dec(v_sz_5136_);
v_i_boxed_5150_ = lean_unbox_usize(v_i_5137_);
lean_dec(v_i_5137_);
v_res_5151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_5146_, v_only_boxed_5147_, v_incremental_boxed_5148_, v_as_5135_, v_sz_boxed_5149_, v_i_boxed_5150_, v_b_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_);
lean_dec(v___y_5144_);
lean_dec_ref(v___y_5143_);
lean_dec(v___y_5142_);
lean_dec_ref(v___y_5141_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5139_);
lean_dec_ref(v_as_5135_);
return v_res_5151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_5152_, lean_object* v_ps_5153_, uint8_t v_only_5154_, uint8_t v_lax_5155_, uint8_t v_incremental_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_){
_start:
{
size_t v_sz_5164_; size_t v___x_5165_; lean_object* v___x_5166_; 
v_sz_5164_ = lean_array_size(v_ps_5153_);
v___x_5165_ = ((size_t)0ULL);
v___x_5166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_5155_, v_only_5154_, v_incremental_5156_, v_ps_5153_, v_sz_5164_, v___x_5165_, v_params_5152_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_5167_, lean_object* v_ps_5168_, lean_object* v_only_5169_, lean_object* v_lax_5170_, lean_object* v_incremental_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_){
_start:
{
uint8_t v_only_boxed_5179_; uint8_t v_lax_boxed_5180_; uint8_t v_incremental_boxed_5181_; lean_object* v_res_5182_; 
v_only_boxed_5179_ = lean_unbox(v_only_5169_);
v_lax_boxed_5180_ = lean_unbox(v_lax_5170_);
v_incremental_boxed_5181_ = lean_unbox(v_incremental_5171_);
v_res_5182_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5167_, v_ps_5168_, v_only_boxed_5179_, v_lax_boxed_5180_, v_incremental_boxed_5181_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_);
lean_dec(v_a_5177_);
lean_dec_ref(v_a_5176_);
lean_dec(v_a_5175_);
lean_dec_ref(v_a_5174_);
lean_dec(v_a_5173_);
lean_dec_ref(v_a_5172_);
lean_dec_ref(v_ps_5168_);
return v_res_5182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_){
_start:
{
lean_object* v_origin_5194_; 
v_origin_5194_ = lean_ctor_get(v_thm_5183_, 5);
if (lean_obj_tag(v_origin_5194_) == 0)
{
lean_object* v_declName_5195_; lean_object* v___x_5196_; 
lean_inc_ref(v_origin_5194_);
lean_dec_ref(v_thm_5183_);
v_declName_5195_ = lean_ctor_get(v_origin_5194_, 0);
lean_inc(v_declName_5195_);
lean_dec_ref_known(v_origin_5194_, 1);
v___x_5196_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_5195_, v_a_5191_, v_a_5192_);
return v___x_5196_;
}
else
{
lean_object* v_proof_5197_; lean_object* v___x_5198_; 
v_proof_5197_ = lean_ctor_get(v_thm_5183_, 1);
lean_inc_ref(v_proof_5197_);
lean_dec_ref(v_thm_5183_);
v___x_5198_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_5197_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_);
return v___x_5198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_, v_a_5207_, v_a_5208_);
lean_dec(v_a_5208_);
lean_dec_ref(v_a_5207_);
lean_dec(v_a_5206_);
lean_dec_ref(v_a_5205_);
lean_dec(v_a_5204_);
lean_dec_ref(v_a_5203_);
lean_dec(v_a_5202_);
lean_dec_ref(v_a_5201_);
lean_dec(v_a_5200_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_5211_, size_t v_sz_5212_, size_t v_i_5213_, lean_object* v_b_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_){
_start:
{
uint8_t v___x_5225_; 
v___x_5225_ = lean_usize_dec_lt(v_i_5213_, v_sz_5212_);
if (v___x_5225_ == 0)
{
lean_object* v___x_5226_; 
v___x_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5226_, 0, v_b_5214_);
return v___x_5226_;
}
else
{
lean_object* v_snd_5227_; lean_object* v___x_5229_; uint8_t v_isShared_5230_; uint8_t v_isSharedCheck_5253_; 
v_snd_5227_ = lean_ctor_get(v_b_5214_, 1);
v_isSharedCheck_5253_ = !lean_is_exclusive(v_b_5214_);
if (v_isSharedCheck_5253_ == 0)
{
lean_object* v_unused_5254_; 
v_unused_5254_ = lean_ctor_get(v_b_5214_, 0);
lean_dec(v_unused_5254_);
v___x_5229_ = v_b_5214_;
v_isShared_5230_ = v_isSharedCheck_5253_;
goto v_resetjp_5228_;
}
else
{
lean_inc(v_snd_5227_);
lean_dec(v_b_5214_);
v___x_5229_ = lean_box(0);
v_isShared_5230_ = v_isSharedCheck_5253_;
goto v_resetjp_5228_;
}
v_resetjp_5228_:
{
lean_object* v___x_5231_; lean_object* v_a_5233_; lean_object* v_a_5240_; lean_object* v___x_5241_; 
v___x_5231_ = lean_box(0);
v_a_5240_ = lean_array_uget_borrowed(v_as_5211_, v_i_5213_);
lean_inc(v_a_5240_);
v___x_5241_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5240_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_, v___y_5223_);
if (lean_obj_tag(v___x_5241_) == 0)
{
lean_object* v_a_5242_; uint8_t v___x_5243_; 
v_a_5242_ = lean_ctor_get(v___x_5241_, 0);
lean_inc(v_a_5242_);
lean_dec_ref_known(v___x_5241_, 1);
v___x_5243_ = lean_unbox(v_a_5242_);
lean_dec(v_a_5242_);
if (v___x_5243_ == 0)
{
v_a_5233_ = v_snd_5227_;
goto v___jp_5232_;
}
else
{
lean_object* v___x_5244_; 
lean_inc(v_a_5240_);
v___x_5244_ = l_Lean_PersistentArray_push___redArg(v_snd_5227_, v_a_5240_);
v_a_5233_ = v___x_5244_;
goto v___jp_5232_;
}
}
else
{
lean_object* v_a_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5252_; 
lean_del_object(v___x_5229_);
lean_dec(v_snd_5227_);
v_a_5245_ = lean_ctor_get(v___x_5241_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5241_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5247_ = v___x_5241_;
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_5241_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5250_; 
if (v_isShared_5248_ == 0)
{
v___x_5250_ = v___x_5247_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_a_5245_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
return v___x_5250_;
}
}
}
v___jp_5232_:
{
lean_object* v___x_5235_; 
if (v_isShared_5230_ == 0)
{
lean_ctor_set(v___x_5229_, 1, v_a_5233_);
lean_ctor_set(v___x_5229_, 0, v___x_5231_);
v___x_5235_ = v___x_5229_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5231_);
lean_ctor_set(v_reuseFailAlloc_5239_, 1, v_a_5233_);
v___x_5235_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
size_t v___x_5236_; size_t v___x_5237_; 
v___x_5236_ = ((size_t)1ULL);
v___x_5237_ = lean_usize_add(v_i_5213_, v___x_5236_);
v_i_5213_ = v___x_5237_;
v_b_5214_ = v___x_5235_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5255_, lean_object* v_sz_5256_, lean_object* v_i_5257_, lean_object* v_b_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_){
_start:
{
size_t v_sz_boxed_5269_; size_t v_i_boxed_5270_; lean_object* v_res_5271_; 
v_sz_boxed_5269_ = lean_unbox_usize(v_sz_5256_);
lean_dec(v_sz_5256_);
v_i_boxed_5270_ = lean_unbox_usize(v_i_5257_);
lean_dec(v_i_5257_);
v_res_5271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5255_, v_sz_boxed_5269_, v_i_boxed_5270_, v_b_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec(v___y_5265_);
lean_dec_ref(v___y_5264_);
lean_dec(v___y_5263_);
lean_dec_ref(v___y_5262_);
lean_dec(v___y_5261_);
lean_dec_ref(v___y_5260_);
lean_dec(v___y_5259_);
lean_dec_ref(v_as_5255_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5272_, size_t v_sz_5273_, size_t v_i_5274_, lean_object* v_b_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
uint8_t v___x_5286_; 
v___x_5286_ = lean_usize_dec_lt(v_i_5274_, v_sz_5273_);
if (v___x_5286_ == 0)
{
lean_object* v___x_5287_; 
v___x_5287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5287_, 0, v_b_5275_);
return v___x_5287_;
}
else
{
lean_object* v_snd_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5314_; 
v_snd_5288_ = lean_ctor_get(v_b_5275_, 1);
v_isSharedCheck_5314_ = !lean_is_exclusive(v_b_5275_);
if (v_isSharedCheck_5314_ == 0)
{
lean_object* v_unused_5315_; 
v_unused_5315_ = lean_ctor_get(v_b_5275_, 0);
lean_dec(v_unused_5315_);
v___x_5290_ = v_b_5275_;
v_isShared_5291_ = v_isSharedCheck_5314_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_snd_5288_);
lean_dec(v_b_5275_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5314_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5292_; lean_object* v_a_5294_; lean_object* v_a_5301_; lean_object* v___x_5302_; 
v___x_5292_ = lean_box(0);
v_a_5301_ = lean_array_uget_borrowed(v_as_5272_, v_i_5274_);
lean_inc(v_a_5301_);
v___x_5302_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5301_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_);
if (lean_obj_tag(v___x_5302_) == 0)
{
lean_object* v_a_5303_; uint8_t v___x_5304_; 
v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
lean_inc(v_a_5303_);
lean_dec_ref_known(v___x_5302_, 1);
v___x_5304_ = lean_unbox(v_a_5303_);
lean_dec(v_a_5303_);
if (v___x_5304_ == 0)
{
v_a_5294_ = v_snd_5288_;
goto v___jp_5293_;
}
else
{
lean_object* v___x_5305_; 
lean_inc(v_a_5301_);
v___x_5305_ = l_Lean_PersistentArray_push___redArg(v_snd_5288_, v_a_5301_);
v_a_5294_ = v___x_5305_;
goto v___jp_5293_;
}
}
else
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5313_; 
lean_del_object(v___x_5290_);
lean_dec(v_snd_5288_);
v_a_5306_ = lean_ctor_get(v___x_5302_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5302_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5308_ = v___x_5302_;
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v___x_5302_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v___x_5311_; 
if (v_isShared_5309_ == 0)
{
v___x_5311_ = v___x_5308_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v_a_5306_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
return v___x_5311_;
}
}
}
v___jp_5293_:
{
lean_object* v___x_5296_; 
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 1, v_a_5294_);
lean_ctor_set(v___x_5290_, 0, v___x_5292_);
v___x_5296_ = v___x_5290_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5300_; 
v_reuseFailAlloc_5300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5300_, 0, v___x_5292_);
lean_ctor_set(v_reuseFailAlloc_5300_, 1, v_a_5294_);
v___x_5296_ = v_reuseFailAlloc_5300_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
size_t v___x_5297_; size_t v___x_5298_; lean_object* v___x_5299_; 
v___x_5297_ = ((size_t)1ULL);
v___x_5298_ = lean_usize_add(v_i_5274_, v___x_5297_);
v___x_5299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5272_, v_sz_5273_, v___x_5298_, v___x_5296_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_);
return v___x_5299_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5316_, lean_object* v_sz_5317_, lean_object* v_i_5318_, lean_object* v_b_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_){
_start:
{
size_t v_sz_boxed_5330_; size_t v_i_boxed_5331_; lean_object* v_res_5332_; 
v_sz_boxed_5330_ = lean_unbox_usize(v_sz_5317_);
lean_dec(v_sz_5317_);
v_i_boxed_5331_ = lean_unbox_usize(v_i_5318_);
lean_dec(v_i_5318_);
v_res_5332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5316_, v_sz_boxed_5330_, v_i_boxed_5331_, v_b_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec(v___y_5320_);
lean_dec_ref(v_as_5316_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5333_, size_t v_sz_5334_, size_t v_i_5335_, lean_object* v_b_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_){
_start:
{
uint8_t v___x_5347_; 
v___x_5347_ = lean_usize_dec_lt(v_i_5335_, v_sz_5334_);
if (v___x_5347_ == 0)
{
lean_object* v___x_5348_; 
v___x_5348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5348_, 0, v_b_5336_);
return v___x_5348_;
}
else
{
lean_object* v_snd_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5375_; 
v_snd_5349_ = lean_ctor_get(v_b_5336_, 1);
v_isSharedCheck_5375_ = !lean_is_exclusive(v_b_5336_);
if (v_isSharedCheck_5375_ == 0)
{
lean_object* v_unused_5376_; 
v_unused_5376_ = lean_ctor_get(v_b_5336_, 0);
lean_dec(v_unused_5376_);
v___x_5351_ = v_b_5336_;
v_isShared_5352_ = v_isSharedCheck_5375_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_snd_5349_);
lean_dec(v_b_5336_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5375_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
lean_object* v___x_5353_; lean_object* v_a_5355_; lean_object* v_a_5362_; lean_object* v___x_5363_; 
v___x_5353_ = lean_box(0);
v_a_5362_ = lean_array_uget_borrowed(v_as_5333_, v_i_5335_);
lean_inc(v_a_5362_);
v___x_5363_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5362_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_);
if (lean_obj_tag(v___x_5363_) == 0)
{
lean_object* v_a_5364_; uint8_t v___x_5365_; 
v_a_5364_ = lean_ctor_get(v___x_5363_, 0);
lean_inc(v_a_5364_);
lean_dec_ref_known(v___x_5363_, 1);
v___x_5365_ = lean_unbox(v_a_5364_);
lean_dec(v_a_5364_);
if (v___x_5365_ == 0)
{
v_a_5355_ = v_snd_5349_;
goto v___jp_5354_;
}
else
{
lean_object* v___x_5366_; 
lean_inc(v_a_5362_);
v___x_5366_ = l_Lean_PersistentArray_push___redArg(v_snd_5349_, v_a_5362_);
v_a_5355_ = v___x_5366_;
goto v___jp_5354_;
}
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
lean_del_object(v___x_5351_);
lean_dec(v_snd_5349_);
v_a_5367_ = lean_ctor_get(v___x_5363_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5363_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5369_ = v___x_5363_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5363_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
v___jp_5354_:
{
lean_object* v___x_5357_; 
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 1, v_a_5355_);
lean_ctor_set(v___x_5351_, 0, v___x_5353_);
v___x_5357_ = v___x_5351_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v___x_5353_);
lean_ctor_set(v_reuseFailAlloc_5361_, 1, v_a_5355_);
v___x_5357_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
size_t v___x_5358_; size_t v___x_5359_; 
v___x_5358_ = ((size_t)1ULL);
v___x_5359_ = lean_usize_add(v_i_5335_, v___x_5358_);
v_i_5335_ = v___x_5359_;
v_b_5336_ = v___x_5357_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5377_, lean_object* v_sz_5378_, lean_object* v_i_5379_, lean_object* v_b_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_){
_start:
{
size_t v_sz_boxed_5391_; size_t v_i_boxed_5392_; lean_object* v_res_5393_; 
v_sz_boxed_5391_ = lean_unbox_usize(v_sz_5378_);
lean_dec(v_sz_5378_);
v_i_boxed_5392_ = lean_unbox_usize(v_i_5379_);
lean_dec(v_i_5379_);
v_res_5393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5377_, v_sz_boxed_5391_, v_i_boxed_5392_, v_b_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_);
lean_dec(v___y_5389_);
lean_dec_ref(v___y_5388_);
lean_dec(v___y_5387_);
lean_dec_ref(v___y_5386_);
lean_dec(v___y_5385_);
lean_dec_ref(v___y_5384_);
lean_dec(v___y_5383_);
lean_dec_ref(v___y_5382_);
lean_dec(v___y_5381_);
lean_dec_ref(v_as_5377_);
return v_res_5393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5394_, size_t v_sz_5395_, size_t v_i_5396_, lean_object* v_b_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_){
_start:
{
uint8_t v___x_5408_; 
v___x_5408_ = lean_usize_dec_lt(v_i_5396_, v_sz_5395_);
if (v___x_5408_ == 0)
{
lean_object* v___x_5409_; 
v___x_5409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5409_, 0, v_b_5397_);
return v___x_5409_;
}
else
{
lean_object* v_snd_5410_; lean_object* v___x_5412_; uint8_t v_isShared_5413_; uint8_t v_isSharedCheck_5436_; 
v_snd_5410_ = lean_ctor_get(v_b_5397_, 1);
v_isSharedCheck_5436_ = !lean_is_exclusive(v_b_5397_);
if (v_isSharedCheck_5436_ == 0)
{
lean_object* v_unused_5437_; 
v_unused_5437_ = lean_ctor_get(v_b_5397_, 0);
lean_dec(v_unused_5437_);
v___x_5412_ = v_b_5397_;
v_isShared_5413_ = v_isSharedCheck_5436_;
goto v_resetjp_5411_;
}
else
{
lean_inc(v_snd_5410_);
lean_dec(v_b_5397_);
v___x_5412_ = lean_box(0);
v_isShared_5413_ = v_isSharedCheck_5436_;
goto v_resetjp_5411_;
}
v_resetjp_5411_:
{
lean_object* v___x_5414_; lean_object* v_a_5416_; lean_object* v_a_5423_; lean_object* v___x_5424_; 
v___x_5414_ = lean_box(0);
v_a_5423_ = lean_array_uget_borrowed(v_as_5394_, v_i_5396_);
lean_inc(v_a_5423_);
v___x_5424_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5423_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_);
if (lean_obj_tag(v___x_5424_) == 0)
{
lean_object* v_a_5425_; uint8_t v___x_5426_; 
v_a_5425_ = lean_ctor_get(v___x_5424_, 0);
lean_inc(v_a_5425_);
lean_dec_ref_known(v___x_5424_, 1);
v___x_5426_ = lean_unbox(v_a_5425_);
lean_dec(v_a_5425_);
if (v___x_5426_ == 0)
{
v_a_5416_ = v_snd_5410_;
goto v___jp_5415_;
}
else
{
lean_object* v___x_5427_; 
lean_inc(v_a_5423_);
v___x_5427_ = l_Lean_PersistentArray_push___redArg(v_snd_5410_, v_a_5423_);
v_a_5416_ = v___x_5427_;
goto v___jp_5415_;
}
}
else
{
lean_object* v_a_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5435_; 
lean_del_object(v___x_5412_);
lean_dec(v_snd_5410_);
v_a_5428_ = lean_ctor_get(v___x_5424_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v___x_5424_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5430_ = v___x_5424_;
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_a_5428_);
lean_dec(v___x_5424_);
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
v___jp_5415_:
{
lean_object* v___x_5418_; 
if (v_isShared_5413_ == 0)
{
lean_ctor_set(v___x_5412_, 1, v_a_5416_);
lean_ctor_set(v___x_5412_, 0, v___x_5414_);
v___x_5418_ = v___x_5412_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v___x_5414_);
lean_ctor_set(v_reuseFailAlloc_5422_, 1, v_a_5416_);
v___x_5418_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
size_t v___x_5419_; size_t v___x_5420_; lean_object* v___x_5421_; 
v___x_5419_ = ((size_t)1ULL);
v___x_5420_ = lean_usize_add(v_i_5396_, v___x_5419_);
v___x_5421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5394_, v_sz_5395_, v___x_5420_, v___x_5418_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_);
return v___x_5421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5438_, lean_object* v_sz_5439_, lean_object* v_i_5440_, lean_object* v_b_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_){
_start:
{
size_t v_sz_boxed_5452_; size_t v_i_boxed_5453_; lean_object* v_res_5454_; 
v_sz_boxed_5452_ = lean_unbox_usize(v_sz_5439_);
lean_dec(v_sz_5439_);
v_i_boxed_5453_ = lean_unbox_usize(v_i_5440_);
lean_dec(v_i_5440_);
v_res_5454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5438_, v_sz_boxed_5452_, v_i_boxed_5453_, v_b_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
lean_dec(v___y_5450_);
lean_dec_ref(v___y_5449_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec(v___y_5446_);
lean_dec_ref(v___y_5445_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec_ref(v_as_5438_);
return v_res_5454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5455_, lean_object* v_n_5456_, lean_object* v_b_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_){
_start:
{
if (lean_obj_tag(v_n_5456_) == 0)
{
lean_object* v_cs_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; size_t v_sz_5471_; size_t v___x_5472_; lean_object* v___x_5473_; 
v_cs_5468_ = lean_ctor_get(v_n_5456_, 0);
v___x_5469_ = lean_box(0);
v___x_5470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5470_, 0, v___x_5469_);
lean_ctor_set(v___x_5470_, 1, v_b_5457_);
v_sz_5471_ = lean_array_size(v_cs_5468_);
v___x_5472_ = ((size_t)0ULL);
v___x_5473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5455_, v_cs_5468_, v_sz_5471_, v___x_5472_, v___x_5470_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_);
if (lean_obj_tag(v___x_5473_) == 0)
{
lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5488_; 
v_a_5474_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5488_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5488_ == 0)
{
v___x_5476_ = v___x_5473_;
v_isShared_5477_ = v_isSharedCheck_5488_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_dec(v___x_5473_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5488_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v_fst_5478_; 
v_fst_5478_ = lean_ctor_get(v_a_5474_, 0);
if (lean_obj_tag(v_fst_5478_) == 0)
{
lean_object* v_snd_5479_; lean_object* v___x_5480_; lean_object* v___x_5482_; 
v_snd_5479_ = lean_ctor_get(v_a_5474_, 1);
lean_inc(v_snd_5479_);
lean_dec(v_a_5474_);
v___x_5480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5480_, 0, v_snd_5479_);
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 0, v___x_5480_);
v___x_5482_ = v___x_5476_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5480_);
v___x_5482_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
return v___x_5482_;
}
}
else
{
lean_object* v_val_5484_; lean_object* v___x_5486_; 
lean_inc_ref(v_fst_5478_);
lean_dec(v_a_5474_);
v_val_5484_ = lean_ctor_get(v_fst_5478_, 0);
lean_inc(v_val_5484_);
lean_dec_ref_known(v_fst_5478_, 1);
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 0, v_val_5484_);
v___x_5486_ = v___x_5476_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_val_5484_);
v___x_5486_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
return v___x_5486_;
}
}
}
}
else
{
lean_object* v_a_5489_; lean_object* v___x_5491_; uint8_t v_isShared_5492_; uint8_t v_isSharedCheck_5496_; 
v_a_5489_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5496_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5496_ == 0)
{
v___x_5491_ = v___x_5473_;
v_isShared_5492_ = v_isSharedCheck_5496_;
goto v_resetjp_5490_;
}
else
{
lean_inc(v_a_5489_);
lean_dec(v___x_5473_);
v___x_5491_ = lean_box(0);
v_isShared_5492_ = v_isSharedCheck_5496_;
goto v_resetjp_5490_;
}
v_resetjp_5490_:
{
lean_object* v___x_5494_; 
if (v_isShared_5492_ == 0)
{
v___x_5494_ = v___x_5491_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v_a_5489_);
v___x_5494_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
return v___x_5494_;
}
}
}
}
else
{
lean_object* v_vs_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; size_t v_sz_5500_; size_t v___x_5501_; lean_object* v___x_5502_; 
v_vs_5497_ = lean_ctor_get(v_n_5456_, 0);
v___x_5498_ = lean_box(0);
v___x_5499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5499_, 0, v___x_5498_);
lean_ctor_set(v___x_5499_, 1, v_b_5457_);
v_sz_5500_ = lean_array_size(v_vs_5497_);
v___x_5501_ = ((size_t)0ULL);
v___x_5502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5497_, v_sz_5500_, v___x_5501_, v___x_5499_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_);
if (lean_obj_tag(v___x_5502_) == 0)
{
lean_object* v_a_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5517_; 
v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5505_ = v___x_5502_;
v_isShared_5506_ = v_isSharedCheck_5517_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_a_5503_);
lean_dec(v___x_5502_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5517_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v_fst_5507_; 
v_fst_5507_ = lean_ctor_get(v_a_5503_, 0);
if (lean_obj_tag(v_fst_5507_) == 0)
{
lean_object* v_snd_5508_; lean_object* v___x_5509_; lean_object* v___x_5511_; 
v_snd_5508_ = lean_ctor_get(v_a_5503_, 1);
lean_inc(v_snd_5508_);
lean_dec(v_a_5503_);
v___x_5509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5509_, 0, v_snd_5508_);
if (v_isShared_5506_ == 0)
{
lean_ctor_set(v___x_5505_, 0, v___x_5509_);
v___x_5511_ = v___x_5505_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v___x_5509_);
v___x_5511_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
return v___x_5511_;
}
}
else
{
lean_object* v_val_5513_; lean_object* v___x_5515_; 
lean_inc_ref(v_fst_5507_);
lean_dec(v_a_5503_);
v_val_5513_ = lean_ctor_get(v_fst_5507_, 0);
lean_inc(v_val_5513_);
lean_dec_ref_known(v_fst_5507_, 1);
if (v_isShared_5506_ == 0)
{
lean_ctor_set(v___x_5505_, 0, v_val_5513_);
v___x_5515_ = v___x_5505_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_val_5513_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
}
}
else
{
lean_object* v_a_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5525_; 
v_a_5518_ = lean_ctor_get(v___x_5502_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5520_ = v___x_5502_;
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_a_5518_);
lean_dec(v___x_5502_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5523_; 
if (v_isShared_5521_ == 0)
{
v___x_5523_ = v___x_5520_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5518_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
return v___x_5523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5526_, lean_object* v_as_5527_, size_t v_sz_5528_, size_t v_i_5529_, lean_object* v_b_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_){
_start:
{
uint8_t v___x_5541_; 
v___x_5541_ = lean_usize_dec_lt(v_i_5529_, v_sz_5528_);
if (v___x_5541_ == 0)
{
lean_object* v___x_5542_; 
v___x_5542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5542_, 0, v_b_5530_);
return v___x_5542_;
}
else
{
lean_object* v_snd_5543_; lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5577_; 
v_snd_5543_ = lean_ctor_get(v_b_5530_, 1);
v_isSharedCheck_5577_ = !lean_is_exclusive(v_b_5530_);
if (v_isSharedCheck_5577_ == 0)
{
lean_object* v_unused_5578_; 
v_unused_5578_ = lean_ctor_get(v_b_5530_, 0);
lean_dec(v_unused_5578_);
v___x_5545_ = v_b_5530_;
v_isShared_5546_ = v_isSharedCheck_5577_;
goto v_resetjp_5544_;
}
else
{
lean_inc(v_snd_5543_);
lean_dec(v_b_5530_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5577_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
lean_object* v___x_5547_; lean_object* v_a_5548_; lean_object* v___x_5549_; 
v___x_5547_ = lean_box(0);
v_a_5548_ = lean_array_uget_borrowed(v_as_5527_, v_i_5529_);
lean_inc(v_snd_5543_);
v___x_5549_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5526_, v_a_5548_, v_snd_5543_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_);
if (lean_obj_tag(v___x_5549_) == 0)
{
lean_object* v_a_5550_; lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5568_; 
v_a_5550_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5568_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5568_ == 0)
{
v___x_5552_ = v___x_5549_;
v_isShared_5553_ = v_isSharedCheck_5568_;
goto v_resetjp_5551_;
}
else
{
lean_inc(v_a_5550_);
lean_dec(v___x_5549_);
v___x_5552_ = lean_box(0);
v_isShared_5553_ = v_isSharedCheck_5568_;
goto v_resetjp_5551_;
}
v_resetjp_5551_:
{
if (lean_obj_tag(v_a_5550_) == 0)
{
lean_object* v___x_5554_; lean_object* v___x_5556_; 
v___x_5554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5554_, 0, v_a_5550_);
if (v_isShared_5546_ == 0)
{
lean_ctor_set(v___x_5545_, 0, v___x_5554_);
v___x_5556_ = v___x_5545_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v___x_5554_);
lean_ctor_set(v_reuseFailAlloc_5560_, 1, v_snd_5543_);
v___x_5556_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
lean_object* v___x_5558_; 
if (v_isShared_5553_ == 0)
{
lean_ctor_set(v___x_5552_, 0, v___x_5556_);
v___x_5558_ = v___x_5552_;
goto v_reusejp_5557_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v___x_5556_);
v___x_5558_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5557_;
}
v_reusejp_5557_:
{
return v___x_5558_;
}
}
}
else
{
lean_object* v_a_5561_; lean_object* v___x_5563_; 
lean_del_object(v___x_5552_);
lean_dec(v_snd_5543_);
v_a_5561_ = lean_ctor_get(v_a_5550_, 0);
lean_inc(v_a_5561_);
lean_dec_ref_known(v_a_5550_, 1);
if (v_isShared_5546_ == 0)
{
lean_ctor_set(v___x_5545_, 1, v_a_5561_);
lean_ctor_set(v___x_5545_, 0, v___x_5547_);
v___x_5563_ = v___x_5545_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v___x_5547_);
lean_ctor_set(v_reuseFailAlloc_5567_, 1, v_a_5561_);
v___x_5563_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
size_t v___x_5564_; size_t v___x_5565_; 
v___x_5564_ = ((size_t)1ULL);
v___x_5565_ = lean_usize_add(v_i_5529_, v___x_5564_);
v_i_5529_ = v___x_5565_;
v_b_5530_ = v___x_5563_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5569_; lean_object* v___x_5571_; uint8_t v_isShared_5572_; uint8_t v_isSharedCheck_5576_; 
lean_del_object(v___x_5545_);
lean_dec(v_snd_5543_);
v_a_5569_ = lean_ctor_get(v___x_5549_, 0);
v_isSharedCheck_5576_ = !lean_is_exclusive(v___x_5549_);
if (v_isSharedCheck_5576_ == 0)
{
v___x_5571_ = v___x_5549_;
v_isShared_5572_ = v_isSharedCheck_5576_;
goto v_resetjp_5570_;
}
else
{
lean_inc(v_a_5569_);
lean_dec(v___x_5549_);
v___x_5571_ = lean_box(0);
v_isShared_5572_ = v_isSharedCheck_5576_;
goto v_resetjp_5570_;
}
v_resetjp_5570_:
{
lean_object* v___x_5574_; 
if (v_isShared_5572_ == 0)
{
v___x_5574_ = v___x_5571_;
goto v_reusejp_5573_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_a_5569_);
v___x_5574_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5573_;
}
v_reusejp_5573_:
{
return v___x_5574_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5579_, lean_object* v_as_5580_, lean_object* v_sz_5581_, lean_object* v_i_5582_, lean_object* v_b_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_){
_start:
{
size_t v_sz_boxed_5594_; size_t v_i_boxed_5595_; lean_object* v_res_5596_; 
v_sz_boxed_5594_ = lean_unbox_usize(v_sz_5581_);
lean_dec(v_sz_5581_);
v_i_boxed_5595_ = lean_unbox_usize(v_i_5582_);
lean_dec(v_i_5582_);
v_res_5596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5579_, v_as_5580_, v_sz_boxed_5594_, v_i_boxed_5595_, v_b_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_);
lean_dec(v___y_5592_);
lean_dec_ref(v___y_5591_);
lean_dec(v___y_5590_);
lean_dec_ref(v___y_5589_);
lean_dec(v___y_5588_);
lean_dec_ref(v___y_5587_);
lean_dec(v___y_5586_);
lean_dec_ref(v___y_5585_);
lean_dec(v___y_5584_);
lean_dec_ref(v_as_5580_);
lean_dec_ref(v_init_5579_);
return v_res_5596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5597_, lean_object* v_n_5598_, lean_object* v_b_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_){
_start:
{
lean_object* v_res_5610_; 
v_res_5610_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5597_, v_n_5598_, v_b_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
lean_dec(v___y_5608_);
lean_dec_ref(v___y_5607_);
lean_dec(v___y_5606_);
lean_dec_ref(v___y_5605_);
lean_dec(v___y_5604_);
lean_dec_ref(v___y_5603_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec(v___y_5600_);
lean_dec_ref(v_n_5598_);
lean_dec_ref(v_init_5597_);
return v_res_5610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5611_, lean_object* v_init_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_){
_start:
{
lean_object* v_root_5623_; lean_object* v_tail_5624_; lean_object* v___x_5625_; 
v_root_5623_ = lean_ctor_get(v_t_5611_, 0);
v_tail_5624_ = lean_ctor_get(v_t_5611_, 1);
lean_inc_ref(v_init_5612_);
v___x_5625_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5612_, v_root_5623_, v_init_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
lean_dec_ref(v_init_5612_);
if (lean_obj_tag(v___x_5625_) == 0)
{
lean_object* v_a_5626_; lean_object* v___x_5628_; uint8_t v_isShared_5629_; uint8_t v_isSharedCheck_5662_; 
v_a_5626_ = lean_ctor_get(v___x_5625_, 0);
v_isSharedCheck_5662_ = !lean_is_exclusive(v___x_5625_);
if (v_isSharedCheck_5662_ == 0)
{
v___x_5628_ = v___x_5625_;
v_isShared_5629_ = v_isSharedCheck_5662_;
goto v_resetjp_5627_;
}
else
{
lean_inc(v_a_5626_);
lean_dec(v___x_5625_);
v___x_5628_ = lean_box(0);
v_isShared_5629_ = v_isSharedCheck_5662_;
goto v_resetjp_5627_;
}
v_resetjp_5627_:
{
if (lean_obj_tag(v_a_5626_) == 0)
{
lean_object* v_a_5630_; lean_object* v___x_5632_; 
v_a_5630_ = lean_ctor_get(v_a_5626_, 0);
lean_inc(v_a_5630_);
lean_dec_ref_known(v_a_5626_, 1);
if (v_isShared_5629_ == 0)
{
lean_ctor_set(v___x_5628_, 0, v_a_5630_);
v___x_5632_ = v___x_5628_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_a_5630_);
v___x_5632_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
return v___x_5632_;
}
}
else
{
lean_object* v_a_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; size_t v_sz_5637_; size_t v___x_5638_; lean_object* v___x_5639_; 
lean_del_object(v___x_5628_);
v_a_5634_ = lean_ctor_get(v_a_5626_, 0);
lean_inc(v_a_5634_);
lean_dec_ref_known(v_a_5626_, 1);
v___x_5635_ = lean_box(0);
v___x_5636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5635_);
lean_ctor_set(v___x_5636_, 1, v_a_5634_);
v_sz_5637_ = lean_array_size(v_tail_5624_);
v___x_5638_ = ((size_t)0ULL);
v___x_5639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5624_, v_sz_5637_, v___x_5638_, v___x_5636_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
if (lean_obj_tag(v___x_5639_) == 0)
{
lean_object* v_a_5640_; lean_object* v___x_5642_; uint8_t v_isShared_5643_; uint8_t v_isSharedCheck_5653_; 
v_a_5640_ = lean_ctor_get(v___x_5639_, 0);
v_isSharedCheck_5653_ = !lean_is_exclusive(v___x_5639_);
if (v_isSharedCheck_5653_ == 0)
{
v___x_5642_ = v___x_5639_;
v_isShared_5643_ = v_isSharedCheck_5653_;
goto v_resetjp_5641_;
}
else
{
lean_inc(v_a_5640_);
lean_dec(v___x_5639_);
v___x_5642_ = lean_box(0);
v_isShared_5643_ = v_isSharedCheck_5653_;
goto v_resetjp_5641_;
}
v_resetjp_5641_:
{
lean_object* v_fst_5644_; 
v_fst_5644_ = lean_ctor_get(v_a_5640_, 0);
if (lean_obj_tag(v_fst_5644_) == 0)
{
lean_object* v_snd_5645_; lean_object* v___x_5647_; 
v_snd_5645_ = lean_ctor_get(v_a_5640_, 1);
lean_inc(v_snd_5645_);
lean_dec(v_a_5640_);
if (v_isShared_5643_ == 0)
{
lean_ctor_set(v___x_5642_, 0, v_snd_5645_);
v___x_5647_ = v___x_5642_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_snd_5645_);
v___x_5647_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
return v___x_5647_;
}
}
else
{
lean_object* v_val_5649_; lean_object* v___x_5651_; 
lean_inc_ref(v_fst_5644_);
lean_dec(v_a_5640_);
v_val_5649_ = lean_ctor_get(v_fst_5644_, 0);
lean_inc(v_val_5649_);
lean_dec_ref_known(v_fst_5644_, 1);
if (v_isShared_5643_ == 0)
{
lean_ctor_set(v___x_5642_, 0, v_val_5649_);
v___x_5651_ = v___x_5642_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_val_5649_);
v___x_5651_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
return v___x_5651_;
}
}
}
}
else
{
lean_object* v_a_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5661_; 
v_a_5654_ = lean_ctor_get(v___x_5639_, 0);
v_isSharedCheck_5661_ = !lean_is_exclusive(v___x_5639_);
if (v_isSharedCheck_5661_ == 0)
{
v___x_5656_ = v___x_5639_;
v_isShared_5657_ = v_isSharedCheck_5661_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_a_5654_);
lean_dec(v___x_5639_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5661_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v___x_5659_; 
if (v_isShared_5657_ == 0)
{
v___x_5659_ = v___x_5656_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_a_5654_);
v___x_5659_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
return v___x_5659_;
}
}
}
}
}
}
else
{
lean_object* v_a_5663_; lean_object* v___x_5665_; uint8_t v_isShared_5666_; uint8_t v_isSharedCheck_5670_; 
v_a_5663_ = lean_ctor_get(v___x_5625_, 0);
v_isSharedCheck_5670_ = !lean_is_exclusive(v___x_5625_);
if (v_isSharedCheck_5670_ == 0)
{
v___x_5665_ = v___x_5625_;
v_isShared_5666_ = v_isSharedCheck_5670_;
goto v_resetjp_5664_;
}
else
{
lean_inc(v_a_5663_);
lean_dec(v___x_5625_);
v___x_5665_ = lean_box(0);
v_isShared_5666_ = v_isSharedCheck_5670_;
goto v_resetjp_5664_;
}
v_resetjp_5664_:
{
lean_object* v___x_5668_; 
if (v_isShared_5666_ == 0)
{
v___x_5668_ = v___x_5665_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_a_5663_);
v___x_5668_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
return v___x_5668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5671_, lean_object* v_init_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_){
_start:
{
lean_object* v_res_5683_; 
v_res_5683_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5671_, v_init_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5678_);
lean_dec(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
lean_dec(v___y_5673_);
lean_dec_ref(v_t_5671_);
return v_res_5683_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; 
v___x_5684_ = lean_unsigned_to_nat(32u);
v___x_5685_ = lean_mk_empty_array_with_capacity(v___x_5684_);
v___x_5686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5685_);
return v___x_5686_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v_result_5692_; 
v___x_5687_ = ((size_t)5ULL);
v___x_5688_ = lean_unsigned_to_nat(0u);
v___x_5689_ = lean_unsigned_to_nat(32u);
v___x_5690_ = lean_mk_empty_array_with_capacity(v___x_5689_);
v___x_5691_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5692_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5692_, 0, v___x_5691_);
lean_ctor_set(v_result_5692_, 1, v___x_5690_);
lean_ctor_set(v_result_5692_, 2, v___x_5688_);
lean_ctor_set(v_result_5692_, 3, v___x_5688_);
lean_ctor_set_usize(v_result_5692_, 4, v___x_5687_);
return v_result_5692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_){
_start:
{
lean_object* v_result_5704_; lean_object* v___x_5705_; 
v_result_5704_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5705_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5693_, v_result_5704_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
return v___x_5705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_){
_start:
{
lean_object* v_res_5717_; 
v_res_5717_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_, v_a_5712_, v_a_5713_, v_a_5714_, v_a_5715_);
lean_dec(v_a_5715_);
lean_dec_ref(v_a_5714_);
lean_dec(v_a_5713_);
lean_dec_ref(v_a_5712_);
lean_dec(v_a_5711_);
lean_dec_ref(v_a_5710_);
lean_dec(v_a_5709_);
lean_dec_ref(v_a_5708_);
lean_dec(v_a_5707_);
lean_dec_ref(v_thms_5706_);
return v_res_5717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(lean_object* v___x_5718_, uint8_t v___x_5719_, lean_object* v_keepIdentParam_5720_, lean_object* v_x_5721_, lean_object* v_mod_x3f_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_){
_start:
{
lean_object* v___x_5730_; lean_object* v_id_5731_; lean_object* v___x_5732_; uint8_t v___x_5733_; 
v___x_5730_ = lean_unsigned_to_nat(2u);
v_id_5731_ = l_Lean_Syntax_getArg(v___x_5718_, v___x_5730_);
v___x_5732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v_id_5731_);
v___x_5733_ = l_Lean_Syntax_isOfKind(v_id_5731_, v___x_5732_);
if (v___x_5733_ == 0)
{
lean_object* v___x_5734_; lean_object* v___x_5735_; 
lean_dec(v_id_5731_);
lean_dec(v_mod_x3f_5722_);
lean_dec_ref(v_keepIdentParam_5720_);
v___x_5734_ = lean_box(v___x_5719_);
v___x_5735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5735_, 0, v___x_5734_);
return v___x_5735_;
}
else
{
lean_object* v___x_5736_; 
lean_inc(v___y_5728_);
lean_inc_ref(v___y_5727_);
lean_inc(v___y_5726_);
lean_inc_ref(v___y_5725_);
lean_inc(v___y_5724_);
lean_inc_ref(v___y_5723_);
v___x_5736_ = lean_apply_9(v_keepIdentParam_5720_, v_mod_x3f_5722_, v_id_5731_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, lean_box(0));
return v___x_5736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1___boxed(lean_object* v___x_5737_, lean_object* v___x_5738_, lean_object* v_keepIdentParam_5739_, lean_object* v_x_5740_, lean_object* v_mod_x3f_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_){
_start:
{
uint8_t v___x_6759__boxed_5749_; lean_object* v_res_5750_; 
v___x_6759__boxed_5749_ = lean_unbox(v___x_5738_);
v_res_5750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(v___x_5737_, v___x_6759__boxed_5749_, v_keepIdentParam_5739_, v_x_5740_, v_mod_x3f_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_);
lean_dec(v___y_5747_);
lean_dec_ref(v___y_5746_);
lean_dec(v___y_5745_);
lean_dec_ref(v___y_5744_);
lean_dec(v___y_5743_);
lean_dec_ref(v___y_5742_);
lean_dec(v___x_5737_);
return v_res_5750_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0(void){
_start:
{
lean_object* v___x_5751_; lean_object* v___x_5752_; 
v___x_5751_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_5752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5752_, 0, v___x_5751_);
return v___x_5752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0(uint8_t v___x_5753_, uint8_t v___x_5754_, lean_object* v_mod_x3f_5755_, lean_object* v_id_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_){
_start:
{
lean_object* v___y_5765_; lean_object* v___y_5766_; lean_object* v___y_5767_; lean_object* v___y_5768_; lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5821_ = l_Lean_TSyntax_getId(v_id_5756_);
v___x_5822_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_5821_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_);
if (lean_obj_tag(v___x_5822_) == 0)
{
lean_object* v_a_5823_; lean_object* v___x_5825_; uint8_t v_isShared_5826_; uint8_t v_isSharedCheck_5833_; 
v_a_5823_ = lean_ctor_get(v___x_5822_, 0);
v_isSharedCheck_5833_ = !lean_is_exclusive(v___x_5822_);
if (v_isSharedCheck_5833_ == 0)
{
v___x_5825_ = v___x_5822_;
v_isShared_5826_ = v_isSharedCheck_5833_;
goto v_resetjp_5824_;
}
else
{
lean_inc(v_a_5823_);
lean_dec(v___x_5822_);
v___x_5825_ = lean_box(0);
v_isShared_5826_ = v_isSharedCheck_5833_;
goto v_resetjp_5824_;
}
v_resetjp_5824_:
{
if (lean_obj_tag(v_a_5823_) == 1)
{
lean_object* v_val_5827_; lean_object* v_snd_5828_; 
v_val_5827_ = lean_ctor_get(v_a_5823_, 0);
lean_inc(v_val_5827_);
lean_dec_ref_known(v_a_5823_, 1);
v_snd_5828_ = lean_ctor_get(v_val_5827_, 1);
lean_inc(v_snd_5828_);
lean_dec(v_val_5827_);
if (lean_obj_tag(v_snd_5828_) == 1)
{
lean_object* v___x_5829_; lean_object* v___x_5831_; 
lean_dec_ref_known(v_snd_5828_, 2);
lean_dec(v_id_5756_);
lean_dec(v_mod_x3f_5755_);
v___x_5829_ = lean_box(v___x_5754_);
if (v_isShared_5826_ == 0)
{
lean_ctor_set(v___x_5825_, 0, v___x_5829_);
v___x_5831_ = v___x_5825_;
goto v_reusejp_5830_;
}
else
{
lean_object* v_reuseFailAlloc_5832_; 
v_reuseFailAlloc_5832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5832_, 0, v___x_5829_);
v___x_5831_ = v_reuseFailAlloc_5832_;
goto v_reusejp_5830_;
}
v_reusejp_5830_:
{
return v___x_5831_;
}
}
else
{
lean_dec(v_snd_5828_);
lean_del_object(v___x_5825_);
goto v___jp_5793_;
}
}
else
{
lean_del_object(v___x_5825_);
lean_dec(v_a_5823_);
goto v___jp_5793_;
}
}
}
else
{
lean_object* v_a_5834_; lean_object* v___x_5836_; uint8_t v_isShared_5837_; uint8_t v_isSharedCheck_5841_; 
lean_dec(v_id_5756_);
lean_dec(v_mod_x3f_5755_);
v_a_5834_ = lean_ctor_get(v___x_5822_, 0);
v_isSharedCheck_5841_ = !lean_is_exclusive(v___x_5822_);
if (v_isSharedCheck_5841_ == 0)
{
v___x_5836_ = v___x_5822_;
v_isShared_5837_ = v_isSharedCheck_5841_;
goto v_resetjp_5835_;
}
else
{
lean_inc(v_a_5834_);
lean_dec(v___x_5822_);
v___x_5836_ = lean_box(0);
v_isShared_5837_ = v_isSharedCheck_5841_;
goto v_resetjp_5835_;
}
v_resetjp_5835_:
{
lean_object* v___x_5839_; 
if (v_isShared_5837_ == 0)
{
v___x_5839_ = v___x_5836_;
goto v_reusejp_5838_;
}
else
{
lean_object* v_reuseFailAlloc_5840_; 
v_reuseFailAlloc_5840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5840_, 0, v_a_5834_);
v___x_5839_ = v_reuseFailAlloc_5840_;
goto v_reusejp_5838_;
}
v_reusejp_5838_:
{
return v___x_5839_;
}
}
}
v___jp_5764_:
{
lean_object* v___x_5769_; 
v___x_5769_ = l_Lean_realizeGlobalConstNoOverload(v_id_5756_, v___y_5767_, v___y_5768_);
if (lean_obj_tag(v___x_5769_) == 0)
{
lean_object* v_a_5770_; lean_object* v___x_5771_; 
v_a_5770_ = lean_ctor_get(v___x_5769_, 0);
lean_inc_n(v_a_5770_, 2);
lean_dec_ref_known(v___x_5769_, 1);
v___x_5771_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_a_5770_, v___x_5753_, v___y_5767_, v___y_5768_);
if (lean_obj_tag(v___x_5771_) == 0)
{
lean_object* v_a_5772_; uint8_t v___x_5773_; 
v_a_5772_ = lean_ctor_get(v___x_5771_, 0);
v___x_5773_ = lean_unbox(v_a_5772_);
if (v___x_5773_ == 0)
{
lean_object* v___x_5774_; lean_object* v___x_5775_; 
lean_dec_ref_known(v___x_5771_, 1);
v___x_5774_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0);
v___x_5775_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(v_a_5770_, v___x_5774_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_);
return v___x_5775_;
}
else
{
lean_dec(v_a_5770_);
return v___x_5771_;
}
}
else
{
lean_dec(v_a_5770_);
return v___x_5771_;
}
}
else
{
lean_object* v_a_5776_; lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5792_; 
v_a_5776_ = lean_ctor_get(v___x_5769_, 0);
v_isSharedCheck_5792_ = !lean_is_exclusive(v___x_5769_);
if (v_isSharedCheck_5792_ == 0)
{
v___x_5778_ = v___x_5769_;
v_isShared_5779_ = v_isSharedCheck_5792_;
goto v_resetjp_5777_;
}
else
{
lean_inc(v_a_5776_);
lean_dec(v___x_5769_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5792_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
uint8_t v___x_5780_; 
v___x_5780_ = l_Lean_Exception_isInterrupt(v_a_5776_);
if (v___x_5780_ == 0)
{
uint8_t v___x_5781_; 
lean_inc(v_a_5776_);
v___x_5781_ = l_Lean_Exception_isRuntime(v_a_5776_);
if (v___x_5781_ == 0)
{
lean_object* v___x_5782_; lean_object* v___x_5784_; 
lean_dec(v_a_5776_);
v___x_5782_ = lean_box(v___x_5781_);
if (v_isShared_5779_ == 0)
{
lean_ctor_set_tag(v___x_5778_, 0);
lean_ctor_set(v___x_5778_, 0, v___x_5782_);
v___x_5784_ = v___x_5778_;
goto v_reusejp_5783_;
}
else
{
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v___x_5782_);
v___x_5784_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5783_;
}
v_reusejp_5783_:
{
return v___x_5784_;
}
}
else
{
lean_object* v___x_5787_; 
if (v_isShared_5779_ == 0)
{
v___x_5787_ = v___x_5778_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5788_; 
v_reuseFailAlloc_5788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5788_, 0, v_a_5776_);
v___x_5787_ = v_reuseFailAlloc_5788_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
return v___x_5787_;
}
}
}
else
{
lean_object* v___x_5790_; 
if (v_isShared_5779_ == 0)
{
v___x_5790_ = v___x_5778_;
goto v_reusejp_5789_;
}
else
{
lean_object* v_reuseFailAlloc_5791_; 
v_reuseFailAlloc_5791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5791_, 0, v_a_5776_);
v___x_5790_ = v_reuseFailAlloc_5791_;
goto v_reusejp_5789_;
}
v_reusejp_5789_:
{
return v___x_5790_;
}
}
}
}
}
v___jp_5793_:
{
if (lean_obj_tag(v_mod_x3f_5755_) == 1)
{
lean_object* v_val_5794_; lean_object* v___x_5795_; 
v_val_5794_ = lean_ctor_get(v_mod_x3f_5755_, 0);
lean_inc(v_val_5794_);
lean_dec_ref_known(v_mod_x3f_5755_, 1);
v___x_5795_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_5794_, v___y_5761_, v___y_5762_);
if (lean_obj_tag(v___x_5795_) == 0)
{
lean_object* v_a_5796_; lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5812_; 
v_a_5796_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_5812_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5812_ == 0)
{
v___x_5798_ = v___x_5795_;
v_isShared_5799_ = v_isSharedCheck_5812_;
goto v_resetjp_5797_;
}
else
{
lean_inc(v_a_5796_);
lean_dec(v___x_5795_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5812_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
switch(lean_obj_tag(v_a_5796_))
{
case 0:
{
lean_object* v___x_5800_; lean_object* v___x_5802_; 
lean_dec_ref_known(v_a_5796_, 1);
lean_dec(v_id_5756_);
v___x_5800_ = lean_box(v___x_5753_);
if (v_isShared_5799_ == 0)
{
lean_ctor_set(v___x_5798_, 0, v___x_5800_);
v___x_5802_ = v___x_5798_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v___x_5800_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
case 2:
{
lean_object* v___x_5804_; lean_object* v___x_5806_; 
lean_dec(v_id_5756_);
v___x_5804_ = lean_box(v___x_5753_);
if (v_isShared_5799_ == 0)
{
lean_ctor_set(v___x_5798_, 0, v___x_5804_);
v___x_5806_ = v___x_5798_;
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
case 3:
{
lean_del_object(v___x_5798_);
v___y_5765_ = v___y_5759_;
v___y_5766_ = v___y_5760_;
v___y_5767_ = v___y_5761_;
v___y_5768_ = v___y_5762_;
goto v___jp_5764_;
}
default: 
{
lean_object* v___x_5808_; lean_object* v___x_5810_; 
lean_dec(v_a_5796_);
lean_dec(v_id_5756_);
v___x_5808_ = lean_box(v___x_5754_);
if (v_isShared_5799_ == 0)
{
lean_ctor_set(v___x_5798_, 0, v___x_5808_);
v___x_5810_ = v___x_5798_;
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
}
}
}
else
{
lean_object* v_a_5813_; lean_object* v___x_5815_; uint8_t v_isShared_5816_; uint8_t v_isSharedCheck_5820_; 
lean_dec(v_id_5756_);
v_a_5813_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_5820_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5820_ == 0)
{
v___x_5815_ = v___x_5795_;
v_isShared_5816_ = v_isSharedCheck_5820_;
goto v_resetjp_5814_;
}
else
{
lean_inc(v_a_5813_);
lean_dec(v___x_5795_);
v___x_5815_ = lean_box(0);
v_isShared_5816_ = v_isSharedCheck_5820_;
goto v_resetjp_5814_;
}
v_resetjp_5814_:
{
lean_object* v___x_5818_; 
if (v_isShared_5816_ == 0)
{
v___x_5818_ = v___x_5815_;
goto v_reusejp_5817_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_a_5813_);
v___x_5818_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5817_;
}
v_reusejp_5817_:
{
return v___x_5818_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_5755_);
v___y_5765_ = v___y_5759_;
v___y_5766_ = v___y_5760_;
v___y_5767_ = v___y_5761_;
v___y_5768_ = v___y_5762_;
goto v___jp_5764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___boxed(lean_object* v___x_5842_, lean_object* v___x_5843_, lean_object* v_mod_x3f_5844_, lean_object* v_id_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_){
_start:
{
uint8_t v___x_6806__boxed_5853_; uint8_t v___x_6807__boxed_5854_; lean_object* v_res_5855_; 
v___x_6806__boxed_5853_ = lean_unbox(v___x_5842_);
v___x_6807__boxed_5854_ = lean_unbox(v___x_5843_);
v_res_5855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0(v___x_6806__boxed_5853_, v___x_6807__boxed_5854_, v_mod_x3f_5844_, v_id_5845_, v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_);
lean_dec(v___y_5851_);
lean_dec_ref(v___y_5850_);
lean_dec(v___y_5849_);
lean_dec_ref(v___y_5848_);
lean_dec(v___y_5847_);
lean_dec_ref(v___y_5846_);
return v_res_5855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(lean_object* v___x_5856_, uint8_t v___x_5857_, lean_object* v_keepIdentParam_5858_, lean_object* v_x_5859_, lean_object* v_mod_x3f_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_){
_start:
{
lean_object* v___x_5868_; lean_object* v_id_5869_; lean_object* v___x_5870_; uint8_t v___x_5871_; 
v___x_5868_ = lean_unsigned_to_nat(1u);
v_id_5869_ = l_Lean_Syntax_getArg(v___x_5856_, v___x_5868_);
v___x_5870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v_id_5869_);
v___x_5871_ = l_Lean_Syntax_isOfKind(v_id_5869_, v___x_5870_);
if (v___x_5871_ == 0)
{
lean_object* v___x_5872_; lean_object* v___x_5873_; 
lean_dec(v_id_5869_);
lean_dec(v_mod_x3f_5860_);
lean_dec_ref(v_keepIdentParam_5858_);
v___x_5872_ = lean_box(v___x_5857_);
v___x_5873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5873_, 0, v___x_5872_);
return v___x_5873_;
}
else
{
lean_object* v___x_5874_; 
lean_inc(v___y_5866_);
lean_inc_ref(v___y_5865_);
lean_inc(v___y_5864_);
lean_inc_ref(v___y_5863_);
lean_inc(v___y_5862_);
lean_inc_ref(v___y_5861_);
v___x_5874_ = lean_apply_9(v_keepIdentParam_5858_, v_mod_x3f_5860_, v_id_5869_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, lean_box(0));
return v___x_5874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2___boxed(lean_object* v___x_5875_, lean_object* v___x_5876_, lean_object* v_keepIdentParam_5877_, lean_object* v_x_5878_, lean_object* v_mod_x3f_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_){
_start:
{
uint8_t v___x_6999__boxed_5887_; lean_object* v_res_5888_; 
v___x_6999__boxed_5887_ = lean_unbox(v___x_5876_);
v_res_5888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(v___x_5875_, v___x_6999__boxed_5887_, v_keepIdentParam_5877_, v_x_5878_, v_mod_x3f_5879_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_);
lean_dec(v___y_5885_);
lean_dec_ref(v___y_5884_);
lean_dec(v___y_5883_);
lean_dec_ref(v___y_5882_);
lean_dec(v___y_5881_);
lean_dec_ref(v___y_5880_);
lean_dec(v___x_5875_);
return v_res_5888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(lean_object* v_as_5889_, size_t v_i_5890_, size_t v_stop_5891_, lean_object* v_b_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_){
_start:
{
lean_object* v_a_5901_; uint8_t v___x_5905_; 
v___x_5905_ = lean_usize_dec_eq(v_i_5890_, v_stop_5891_);
if (v___x_5905_ == 0)
{
lean_object* v___x_5906_; lean_object* v___y_5910_; lean_object* v___x_5921_; uint8_t v___x_5922_; 
v___x_5906_ = lean_array_uget_borrowed(v_as_5889_, v_i_5890_);
v___x_5921_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v___x_5906_);
v___x_5922_ = l_Lean_Syntax_isOfKind(v___x_5906_, v___x_5921_);
if (v___x_5922_ == 0)
{
goto v___jp_5907_;
}
else
{
lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v_keepIdentParam_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; uint8_t v___x_5929_; 
v___x_5923_ = lean_box(v___x_5905_);
v___x_5924_ = lean_box(v___x_5922_);
v_keepIdentParam_5925_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___boxed), 11, 2);
lean_closure_set(v_keepIdentParam_5925_, 0, v___x_5923_);
lean_closure_set(v_keepIdentParam_5925_, 1, v___x_5924_);
v___x_5926_ = lean_unsigned_to_nat(0u);
v___x_5927_ = l_Lean_Syntax_getArg(v___x_5906_, v___x_5926_);
v___x_5928_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_5927_);
v___x_5929_ = l_Lean_Syntax_isOfKind(v___x_5927_, v___x_5928_);
if (v___x_5929_ == 0)
{
lean_object* v___x_5930_; uint8_t v___x_5931_; 
v___x_5930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_5927_);
v___x_5931_ = l_Lean_Syntax_isOfKind(v___x_5927_, v___x_5930_);
if (v___x_5931_ == 0)
{
lean_object* v___x_5932_; uint8_t v___x_5933_; 
lean_dec_ref(v_keepIdentParam_5925_);
v___x_5932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_5927_);
v___x_5933_ = l_Lean_Syntax_isOfKind(v___x_5927_, v___x_5932_);
if (v___x_5933_ == 0)
{
lean_object* v___x_5934_; uint8_t v___x_5935_; 
v___x_5934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_5927_);
v___x_5935_ = l_Lean_Syntax_isOfKind(v___x_5927_, v___x_5934_);
if (v___x_5935_ == 0)
{
lean_dec(v___x_5927_);
goto v___jp_5907_;
}
else
{
lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; uint8_t v___x_5939_; 
v___x_5936_ = lean_unsigned_to_nat(1u);
v___x_5937_ = l_Lean_Syntax_getArg(v___x_5927_, v___x_5936_);
lean_dec(v___x_5927_);
v___x_5938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13));
v___x_5939_ = l_Lean_Syntax_isOfKind(v___x_5937_, v___x_5938_);
if (v___x_5939_ == 0)
{
goto v___jp_5907_;
}
else
{
v_a_5901_ = v_b_5892_;
goto v___jp_5900_;
}
}
}
else
{
lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; uint8_t v___x_5943_; 
v___x_5940_ = lean_unsigned_to_nat(1u);
v___x_5941_ = l_Lean_Syntax_getArg(v___x_5927_, v___x_5940_);
lean_dec(v___x_5927_);
v___x_5942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
v___x_5943_ = l_Lean_Syntax_isOfKind(v___x_5941_, v___x_5942_);
if (v___x_5943_ == 0)
{
goto v___jp_5907_;
}
else
{
v_a_5901_ = v_b_5892_;
goto v___jp_5900_;
}
}
}
else
{
lean_object* v___x_5944_; lean_object* v___x_5945_; uint8_t v___x_5946_; 
v___x_5944_ = lean_unsigned_to_nat(1u);
v___x_5945_ = l_Lean_Syntax_getArg(v___x_5927_, v___x_5944_);
v___x_5946_ = l_Lean_Syntax_isNone(v___x_5945_);
if (v___x_5946_ == 0)
{
uint8_t v___x_5947_; 
lean_inc(v___x_5945_);
v___x_5947_ = l_Lean_Syntax_matchesNull(v___x_5945_, v___x_5944_);
if (v___x_5947_ == 0)
{
lean_dec(v___x_5945_);
lean_dec(v___x_5927_);
lean_dec_ref(v_keepIdentParam_5925_);
goto v___jp_5907_;
}
else
{
lean_object* v_mod_x3f_5948_; lean_object* v___x_5949_; uint8_t v___x_5950_; 
v_mod_x3f_5948_ = l_Lean_Syntax_getArg(v___x_5945_, v___x_5926_);
lean_dec(v___x_5945_);
v___x_5949_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v_mod_x3f_5948_);
v___x_5950_ = l_Lean_Syntax_isOfKind(v_mod_x3f_5948_, v___x_5949_);
if (v___x_5950_ == 0)
{
lean_dec(v_mod_x3f_5948_);
lean_dec(v___x_5927_);
lean_dec_ref(v_keepIdentParam_5925_);
goto v___jp_5907_;
}
else
{
lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; 
v___x_5951_ = lean_box(0);
v___x_5952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5952_, 0, v_mod_x3f_5948_);
v___x_5953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(v___x_5927_, v___x_5922_, v_keepIdentParam_5925_, v___x_5951_, v___x_5952_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
lean_dec(v___x_5927_);
v___y_5910_ = v___x_5953_;
goto v___jp_5909_;
}
}
}
else
{
lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; 
lean_dec(v___x_5945_);
v___x_5954_ = lean_box(0);
v___x_5955_ = lean_box(0);
v___x_5956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(v___x_5927_, v___x_5922_, v_keepIdentParam_5925_, v___x_5954_, v___x_5955_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
lean_dec(v___x_5927_);
v___y_5910_ = v___x_5956_;
goto v___jp_5909_;
}
}
}
else
{
lean_object* v___x_5957_; uint8_t v___x_5958_; 
v___x_5957_ = l_Lean_Syntax_getArg(v___x_5927_, v___x_5926_);
v___x_5958_ = l_Lean_Syntax_isNone(v___x_5957_);
if (v___x_5958_ == 0)
{
lean_object* v___x_5959_; uint8_t v___x_5960_; 
v___x_5959_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_5957_);
v___x_5960_ = l_Lean_Syntax_matchesNull(v___x_5957_, v___x_5959_);
if (v___x_5960_ == 0)
{
lean_dec(v___x_5957_);
lean_dec(v___x_5927_);
lean_dec_ref(v_keepIdentParam_5925_);
goto v___jp_5907_;
}
else
{
lean_object* v_mod_x3f_5961_; lean_object* v___x_5962_; uint8_t v___x_5963_; 
v_mod_x3f_5961_ = l_Lean_Syntax_getArg(v___x_5957_, v___x_5926_);
lean_dec(v___x_5957_);
v___x_5962_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v_mod_x3f_5961_);
v___x_5963_ = l_Lean_Syntax_isOfKind(v_mod_x3f_5961_, v___x_5962_);
if (v___x_5963_ == 0)
{
lean_dec(v_mod_x3f_5961_);
lean_dec(v___x_5927_);
lean_dec_ref(v_keepIdentParam_5925_);
goto v___jp_5907_;
}
else
{
lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; 
v___x_5964_ = lean_box(0);
v___x_5965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5965_, 0, v_mod_x3f_5961_);
v___x_5966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(v___x_5927_, v___x_5922_, v_keepIdentParam_5925_, v___x_5964_, v___x_5965_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
lean_dec(v___x_5927_);
v___y_5910_ = v___x_5966_;
goto v___jp_5909_;
}
}
}
else
{
lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; 
lean_dec(v___x_5957_);
v___x_5967_ = lean_box(0);
v___x_5968_ = lean_box(0);
v___x_5969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(v___x_5927_, v___x_5922_, v_keepIdentParam_5925_, v___x_5967_, v___x_5968_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
lean_dec(v___x_5927_);
v___y_5910_ = v___x_5969_;
goto v___jp_5909_;
}
}
}
v___jp_5907_:
{
lean_object* v___x_5908_; 
lean_inc(v___x_5906_);
v___x_5908_ = lean_array_push(v_b_5892_, v___x_5906_);
v_a_5901_ = v___x_5908_;
goto v___jp_5900_;
}
v___jp_5909_:
{
if (lean_obj_tag(v___y_5910_) == 0)
{
lean_object* v_a_5911_; uint8_t v___x_5912_; 
v_a_5911_ = lean_ctor_get(v___y_5910_, 0);
lean_inc(v_a_5911_);
lean_dec_ref_known(v___y_5910_, 1);
v___x_5912_ = lean_unbox(v_a_5911_);
lean_dec(v_a_5911_);
if (v___x_5912_ == 0)
{
v_a_5901_ = v_b_5892_;
goto v___jp_5900_;
}
else
{
goto v___jp_5907_;
}
}
else
{
lean_object* v_a_5913_; lean_object* v___x_5915_; uint8_t v_isShared_5916_; uint8_t v_isSharedCheck_5920_; 
lean_dec_ref(v_b_5892_);
v_a_5913_ = lean_ctor_get(v___y_5910_, 0);
v_isSharedCheck_5920_ = !lean_is_exclusive(v___y_5910_);
if (v_isSharedCheck_5920_ == 0)
{
v___x_5915_ = v___y_5910_;
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
else
{
lean_inc(v_a_5913_);
lean_dec(v___y_5910_);
v___x_5915_ = lean_box(0);
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
v_resetjp_5914_:
{
lean_object* v___x_5918_; 
if (v_isShared_5916_ == 0)
{
v___x_5918_ = v___x_5915_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_a_5913_);
v___x_5918_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
return v___x_5918_;
}
}
}
}
}
else
{
lean_object* v___x_5970_; 
v___x_5970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5970_, 0, v_b_5892_);
return v___x_5970_;
}
v___jp_5900_:
{
size_t v___x_5902_; size_t v___x_5903_; 
v___x_5902_ = ((size_t)1ULL);
v___x_5903_ = lean_usize_add(v_i_5890_, v___x_5902_);
v_i_5890_ = v___x_5903_;
v_b_5892_ = v_a_5901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___boxed(lean_object* v_as_5971_, lean_object* v_i_5972_, lean_object* v_stop_5973_, lean_object* v_b_5974_, lean_object* v___y_5975_, lean_object* v___y_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_){
_start:
{
size_t v_i_boxed_5982_; size_t v_stop_boxed_5983_; lean_object* v_res_5984_; 
v_i_boxed_5982_ = lean_unbox_usize(v_i_5972_);
lean_dec(v_i_5972_);
v_stop_boxed_5983_ = lean_unbox_usize(v_stop_5973_);
lean_dec(v_stop_5973_);
v_res_5984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(v_as_5971_, v_i_boxed_5982_, v_stop_boxed_5983_, v_b_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_, v___y_5980_);
lean_dec(v___y_5980_);
lean_dec_ref(v___y_5979_);
lean_dec(v___y_5978_);
lean_dec_ref(v___y_5977_);
lean_dec(v___y_5976_);
lean_dec_ref(v___y_5975_);
lean_dec_ref(v_as_5971_);
return v_res_5984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_getPreservedParams(lean_object* v_params_5987_, lean_object* v_a_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_, lean_object* v_a_5992_, lean_object* v_a_5993_){
_start:
{
lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; uint8_t v___x_5998_; 
v___x_5995_ = lean_unsigned_to_nat(0u);
v___x_5996_ = lean_array_get_size(v_params_5987_);
v___x_5997_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_getPreservedParams___closed__0));
v___x_5998_ = lean_nat_dec_lt(v___x_5995_, v___x_5996_);
if (v___x_5998_ == 0)
{
lean_object* v___x_5999_; 
v___x_5999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5997_);
return v___x_5999_;
}
else
{
size_t v___x_6000_; size_t v___x_6001_; lean_object* v___x_6002_; 
v___x_6000_ = ((size_t)0ULL);
v___x_6001_ = lean_usize_of_nat(v___x_5996_);
v___x_6002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(v_params_5987_, v___x_6000_, v___x_6001_, v___x_5997_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_);
return v___x_6002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_getPreservedParams___boxed(lean_object* v_params_6003_, lean_object* v_a_6004_, lean_object* v_a_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_){
_start:
{
lean_object* v_res_6011_; 
v_res_6011_ = l_Lean_Elab_Tactic_Grind_getPreservedParams(v_params_6003_, v_a_6004_, v_a_6005_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_);
lean_dec(v_a_6009_);
lean_dec_ref(v_a_6008_);
lean_dec(v_a_6007_);
lean_dec_ref(v_a_6006_);
lean_dec(v_a_6005_);
lean_dec_ref(v_a_6004_);
lean_dec_ref(v_params_6003_);
return v_res_6011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_6014_, lean_object* v_newThms_6015_, lean_object* v_gmt_6016_, lean_object* v_numInstances_6017_, lean_object* v_numDelayedInstances_6018_, lean_object* v_num_6019_, lean_object* v_preInstances_6020_, lean_object* v_nextThmIdx_6021_, lean_object* v_matchEqNames_6022_, lean_object* v_delayedThmInsts_6023_, lean_object* v_nextDeclIdx_6024_, lean_object* v_enodeMap_6025_, lean_object* v_exprs_6026_, lean_object* v_parents_6027_, lean_object* v_congrTable_6028_, lean_object* v_appMap_6029_, lean_object* v_indicesFound_6030_, lean_object* v_toProcess_6031_, lean_object* v_internalizing_6032_, uint8_t v_inconsistent_6033_, lean_object* v_nextIdx_6034_, lean_object* v_newRawFacts_6035_, lean_object* v_facts_6036_, lean_object* v_extThms_6037_, lean_object* v_inj_6038_, lean_object* v_split_6039_, lean_object* v_clean_6040_, lean_object* v_sstates_6041_, lean_object* v_mvarId_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_){
_start:
{
lean_object* v___x_6053_; 
v___x_6053_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_6014_, v___y_6043_, v___y_6044_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_);
if (lean_obj_tag(v___x_6053_) == 0)
{
lean_object* v_a_6054_; lean_object* v___x_6055_; 
v_a_6054_ = lean_ctor_get(v___x_6053_, 0);
lean_inc(v_a_6054_);
lean_dec_ref_known(v___x_6053_, 1);
v___x_6055_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_6015_, v___y_6043_, v___y_6044_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_);
if (lean_obj_tag(v___x_6055_) == 0)
{
lean_object* v_a_6056_; lean_object* v___x_6058_; uint8_t v_isShared_6059_; uint8_t v_isSharedCheck_6067_; 
v_a_6056_ = lean_ctor_get(v___x_6055_, 0);
v_isSharedCheck_6067_ = !lean_is_exclusive(v___x_6055_);
if (v_isSharedCheck_6067_ == 0)
{
v___x_6058_ = v___x_6055_;
v_isShared_6059_ = v_isSharedCheck_6067_;
goto v_resetjp_6057_;
}
else
{
lean_inc(v_a_6056_);
lean_dec(v___x_6055_);
v___x_6058_ = lean_box(0);
v_isShared_6059_ = v_isSharedCheck_6067_;
goto v_resetjp_6057_;
}
v_resetjp_6057_:
{
lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6065_; 
v___x_6060_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_6061_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6060_);
lean_ctor_set(v___x_6061_, 1, v_gmt_6016_);
lean_ctor_set(v___x_6061_, 2, v_a_6054_);
lean_ctor_set(v___x_6061_, 3, v_a_6056_);
lean_ctor_set(v___x_6061_, 4, v_numInstances_6017_);
lean_ctor_set(v___x_6061_, 5, v_numDelayedInstances_6018_);
lean_ctor_set(v___x_6061_, 6, v_num_6019_);
lean_ctor_set(v___x_6061_, 7, v_preInstances_6020_);
lean_ctor_set(v___x_6061_, 8, v_nextThmIdx_6021_);
lean_ctor_set(v___x_6061_, 9, v_matchEqNames_6022_);
lean_ctor_set(v___x_6061_, 10, v_delayedThmInsts_6023_);
v___x_6062_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v___x_6062_, 0, v_nextDeclIdx_6024_);
lean_ctor_set(v___x_6062_, 1, v_enodeMap_6025_);
lean_ctor_set(v___x_6062_, 2, v_exprs_6026_);
lean_ctor_set(v___x_6062_, 3, v_parents_6027_);
lean_ctor_set(v___x_6062_, 4, v_congrTable_6028_);
lean_ctor_set(v___x_6062_, 5, v_appMap_6029_);
lean_ctor_set(v___x_6062_, 6, v_indicesFound_6030_);
lean_ctor_set(v___x_6062_, 7, v_toProcess_6031_);
lean_ctor_set(v___x_6062_, 8, v_internalizing_6032_);
lean_ctor_set(v___x_6062_, 9, v_nextIdx_6034_);
lean_ctor_set(v___x_6062_, 10, v_newRawFacts_6035_);
lean_ctor_set(v___x_6062_, 11, v_facts_6036_);
lean_ctor_set(v___x_6062_, 12, v_extThms_6037_);
lean_ctor_set(v___x_6062_, 13, v___x_6061_);
lean_ctor_set(v___x_6062_, 14, v_inj_6038_);
lean_ctor_set(v___x_6062_, 15, v_split_6039_);
lean_ctor_set(v___x_6062_, 16, v_clean_6040_);
lean_ctor_set(v___x_6062_, 17, v_sstates_6041_);
lean_ctor_set_uint8(v___x_6062_, sizeof(void*)*18, v_inconsistent_6033_);
v___x_6063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6062_);
lean_ctor_set(v___x_6063_, 1, v_mvarId_6042_);
if (v_isShared_6059_ == 0)
{
lean_ctor_set(v___x_6058_, 0, v___x_6063_);
v___x_6065_ = v___x_6058_;
goto v_reusejp_6064_;
}
else
{
lean_object* v_reuseFailAlloc_6066_; 
v_reuseFailAlloc_6066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6066_, 0, v___x_6063_);
v___x_6065_ = v_reuseFailAlloc_6066_;
goto v_reusejp_6064_;
}
v_reusejp_6064_:
{
return v___x_6065_;
}
}
}
else
{
lean_object* v_a_6068_; lean_object* v___x_6070_; uint8_t v_isShared_6071_; uint8_t v_isSharedCheck_6075_; 
lean_dec(v_a_6054_);
lean_dec(v_mvarId_6042_);
lean_dec_ref(v_sstates_6041_);
lean_dec_ref(v_clean_6040_);
lean_dec_ref(v_split_6039_);
lean_dec_ref(v_inj_6038_);
lean_dec_ref(v_extThms_6037_);
lean_dec_ref(v_facts_6036_);
lean_dec_ref(v_newRawFacts_6035_);
lean_dec(v_nextIdx_6034_);
lean_dec_ref(v_internalizing_6032_);
lean_dec_ref(v_toProcess_6031_);
lean_dec_ref(v_indicesFound_6030_);
lean_dec_ref(v_appMap_6029_);
lean_dec_ref(v_congrTable_6028_);
lean_dec_ref(v_parents_6027_);
lean_dec_ref(v_exprs_6026_);
lean_dec_ref(v_enodeMap_6025_);
lean_dec(v_nextDeclIdx_6024_);
lean_dec_ref(v_delayedThmInsts_6023_);
lean_dec_ref(v_matchEqNames_6022_);
lean_dec(v_nextThmIdx_6021_);
lean_dec_ref(v_preInstances_6020_);
lean_dec(v_num_6019_);
lean_dec(v_numDelayedInstances_6018_);
lean_dec(v_numInstances_6017_);
lean_dec(v_gmt_6016_);
v_a_6068_ = lean_ctor_get(v___x_6055_, 0);
v_isSharedCheck_6075_ = !lean_is_exclusive(v___x_6055_);
if (v_isSharedCheck_6075_ == 0)
{
v___x_6070_ = v___x_6055_;
v_isShared_6071_ = v_isSharedCheck_6075_;
goto v_resetjp_6069_;
}
else
{
lean_inc(v_a_6068_);
lean_dec(v___x_6055_);
v___x_6070_ = lean_box(0);
v_isShared_6071_ = v_isSharedCheck_6075_;
goto v_resetjp_6069_;
}
v_resetjp_6069_:
{
lean_object* v___x_6073_; 
if (v_isShared_6071_ == 0)
{
v___x_6073_ = v___x_6070_;
goto v_reusejp_6072_;
}
else
{
lean_object* v_reuseFailAlloc_6074_; 
v_reuseFailAlloc_6074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6074_, 0, v_a_6068_);
v___x_6073_ = v_reuseFailAlloc_6074_;
goto v_reusejp_6072_;
}
v_reusejp_6072_:
{
return v___x_6073_;
}
}
}
}
else
{
lean_object* v_a_6076_; lean_object* v___x_6078_; uint8_t v_isShared_6079_; uint8_t v_isSharedCheck_6083_; 
lean_dec(v_mvarId_6042_);
lean_dec_ref(v_sstates_6041_);
lean_dec_ref(v_clean_6040_);
lean_dec_ref(v_split_6039_);
lean_dec_ref(v_inj_6038_);
lean_dec_ref(v_extThms_6037_);
lean_dec_ref(v_facts_6036_);
lean_dec_ref(v_newRawFacts_6035_);
lean_dec(v_nextIdx_6034_);
lean_dec_ref(v_internalizing_6032_);
lean_dec_ref(v_toProcess_6031_);
lean_dec_ref(v_indicesFound_6030_);
lean_dec_ref(v_appMap_6029_);
lean_dec_ref(v_congrTable_6028_);
lean_dec_ref(v_parents_6027_);
lean_dec_ref(v_exprs_6026_);
lean_dec_ref(v_enodeMap_6025_);
lean_dec(v_nextDeclIdx_6024_);
lean_dec_ref(v_delayedThmInsts_6023_);
lean_dec_ref(v_matchEqNames_6022_);
lean_dec(v_nextThmIdx_6021_);
lean_dec_ref(v_preInstances_6020_);
lean_dec(v_num_6019_);
lean_dec(v_numDelayedInstances_6018_);
lean_dec(v_numInstances_6017_);
lean_dec(v_gmt_6016_);
v_a_6076_ = lean_ctor_get(v___x_6053_, 0);
v_isSharedCheck_6083_ = !lean_is_exclusive(v___x_6053_);
if (v_isSharedCheck_6083_ == 0)
{
v___x_6078_ = v___x_6053_;
v_isShared_6079_ = v_isSharedCheck_6083_;
goto v_resetjp_6077_;
}
else
{
lean_inc(v_a_6076_);
lean_dec(v___x_6053_);
v___x_6078_ = lean_box(0);
v_isShared_6079_ = v_isSharedCheck_6083_;
goto v_resetjp_6077_;
}
v_resetjp_6077_:
{
lean_object* v___x_6081_; 
if (v_isShared_6079_ == 0)
{
v___x_6081_ = v___x_6078_;
goto v_reusejp_6080_;
}
else
{
lean_object* v_reuseFailAlloc_6082_; 
v_reuseFailAlloc_6082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6082_, 0, v_a_6076_);
v___x_6081_ = v_reuseFailAlloc_6082_;
goto v_reusejp_6080_;
}
v_reusejp_6080_:
{
return v___x_6081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_6084_ = _args[0];
lean_object* v_newThms_6085_ = _args[1];
lean_object* v_gmt_6086_ = _args[2];
lean_object* v_numInstances_6087_ = _args[3];
lean_object* v_numDelayedInstances_6088_ = _args[4];
lean_object* v_num_6089_ = _args[5];
lean_object* v_preInstances_6090_ = _args[6];
lean_object* v_nextThmIdx_6091_ = _args[7];
lean_object* v_matchEqNames_6092_ = _args[8];
lean_object* v_delayedThmInsts_6093_ = _args[9];
lean_object* v_nextDeclIdx_6094_ = _args[10];
lean_object* v_enodeMap_6095_ = _args[11];
lean_object* v_exprs_6096_ = _args[12];
lean_object* v_parents_6097_ = _args[13];
lean_object* v_congrTable_6098_ = _args[14];
lean_object* v_appMap_6099_ = _args[15];
lean_object* v_indicesFound_6100_ = _args[16];
lean_object* v_toProcess_6101_ = _args[17];
lean_object* v_internalizing_6102_ = _args[18];
lean_object* v_inconsistent_6103_ = _args[19];
lean_object* v_nextIdx_6104_ = _args[20];
lean_object* v_newRawFacts_6105_ = _args[21];
lean_object* v_facts_6106_ = _args[22];
lean_object* v_extThms_6107_ = _args[23];
lean_object* v_inj_6108_ = _args[24];
lean_object* v_split_6109_ = _args[25];
lean_object* v_clean_6110_ = _args[26];
lean_object* v_sstates_6111_ = _args[27];
lean_object* v_mvarId_6112_ = _args[28];
lean_object* v___y_6113_ = _args[29];
lean_object* v___y_6114_ = _args[30];
lean_object* v___y_6115_ = _args[31];
lean_object* v___y_6116_ = _args[32];
lean_object* v___y_6117_ = _args[33];
lean_object* v___y_6118_ = _args[34];
lean_object* v___y_6119_ = _args[35];
lean_object* v___y_6120_ = _args[36];
lean_object* v___y_6121_ = _args[37];
lean_object* v___y_6122_ = _args[38];
_start:
{
uint8_t v_inconsistent_boxed_6123_; lean_object* v_res_6124_; 
v_inconsistent_boxed_6123_ = lean_unbox(v_inconsistent_6103_);
v_res_6124_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_6084_, v_newThms_6085_, v_gmt_6086_, v_numInstances_6087_, v_numDelayedInstances_6088_, v_num_6089_, v_preInstances_6090_, v_nextThmIdx_6091_, v_matchEqNames_6092_, v_delayedThmInsts_6093_, v_nextDeclIdx_6094_, v_enodeMap_6095_, v_exprs_6096_, v_parents_6097_, v_congrTable_6098_, v_appMap_6099_, v_indicesFound_6100_, v_toProcess_6101_, v_internalizing_6102_, v_inconsistent_boxed_6123_, v_nextIdx_6104_, v_newRawFacts_6105_, v_facts_6106_, v_extThms_6107_, v_inj_6108_, v_split_6109_, v_clean_6110_, v_sstates_6111_, v_mvarId_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_);
lean_dec(v___y_6121_);
lean_dec_ref(v___y_6120_);
lean_dec(v___y_6119_);
lean_dec_ref(v___y_6118_);
lean_dec(v___y_6117_);
lean_dec_ref(v___y_6116_);
lean_dec(v___y_6115_);
lean_dec_ref(v___y_6114_);
lean_dec(v___y_6113_);
lean_dec_ref(v_newThms_6085_);
lean_dec_ref(v_thms_6084_);
return v_res_6124_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_6125_; 
v___x_6125_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_6125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_6126_, size_t v_i_6127_, lean_object* v_bs_6128_){
_start:
{
uint8_t v___x_6129_; 
v___x_6129_ = lean_usize_dec_lt(v_i_6127_, v_sz_6126_);
if (v___x_6129_ == 0)
{
return v_bs_6128_;
}
else
{
lean_object* v_v_6130_; lean_object* v_casesTypes_6131_; lean_object* v_extThms_6132_; lean_object* v_funCC_6133_; lean_object* v_inj_6134_; lean_object* v___x_6136_; uint8_t v_isShared_6137_; uint8_t v_isSharedCheck_6148_; 
v_v_6130_ = lean_array_uget(v_bs_6128_, v_i_6127_);
v_casesTypes_6131_ = lean_ctor_get(v_v_6130_, 0);
v_extThms_6132_ = lean_ctor_get(v_v_6130_, 1);
v_funCC_6133_ = lean_ctor_get(v_v_6130_, 2);
v_inj_6134_ = lean_ctor_get(v_v_6130_, 4);
v_isSharedCheck_6148_ = !lean_is_exclusive(v_v_6130_);
if (v_isSharedCheck_6148_ == 0)
{
lean_object* v_unused_6149_; 
v_unused_6149_ = lean_ctor_get(v_v_6130_, 3);
lean_dec(v_unused_6149_);
v___x_6136_ = v_v_6130_;
v_isShared_6137_ = v_isSharedCheck_6148_;
goto v_resetjp_6135_;
}
else
{
lean_inc(v_inj_6134_);
lean_inc(v_funCC_6133_);
lean_inc(v_extThms_6132_);
lean_inc(v_casesTypes_6131_);
lean_dec(v_v_6130_);
v___x_6136_ = lean_box(0);
v_isShared_6137_ = v_isSharedCheck_6148_;
goto v_resetjp_6135_;
}
v_resetjp_6135_:
{
lean_object* v___x_6138_; lean_object* v_bs_x27_6139_; lean_object* v___x_6140_; lean_object* v___x_6142_; 
v___x_6138_ = lean_unsigned_to_nat(0u);
v_bs_x27_6139_ = lean_array_uset(v_bs_6128_, v_i_6127_, v___x_6138_);
v___x_6140_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_6137_ == 0)
{
lean_ctor_set(v___x_6136_, 3, v___x_6140_);
v___x_6142_ = v___x_6136_;
goto v_reusejp_6141_;
}
else
{
lean_object* v_reuseFailAlloc_6147_; 
v_reuseFailAlloc_6147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6147_, 0, v_casesTypes_6131_);
lean_ctor_set(v_reuseFailAlloc_6147_, 1, v_extThms_6132_);
lean_ctor_set(v_reuseFailAlloc_6147_, 2, v_funCC_6133_);
lean_ctor_set(v_reuseFailAlloc_6147_, 3, v___x_6140_);
lean_ctor_set(v_reuseFailAlloc_6147_, 4, v_inj_6134_);
v___x_6142_ = v_reuseFailAlloc_6147_;
goto v_reusejp_6141_;
}
v_reusejp_6141_:
{
size_t v___x_6143_; size_t v___x_6144_; lean_object* v___x_6145_; 
v___x_6143_ = ((size_t)1ULL);
v___x_6144_ = lean_usize_add(v_i_6127_, v___x_6143_);
v___x_6145_ = lean_array_uset(v_bs_x27_6139_, v_i_6127_, v___x_6142_);
v_i_6127_ = v___x_6144_;
v_bs_6128_ = v___x_6145_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_6150_, lean_object* v_i_6151_, lean_object* v_bs_6152_){
_start:
{
size_t v_sz_boxed_6153_; size_t v_i_boxed_6154_; lean_object* v_res_6155_; 
v_sz_boxed_6153_ = lean_unbox_usize(v_sz_6150_);
lean_dec(v_sz_6150_);
v_i_boxed_6154_ = lean_unbox_usize(v_i_6151_);
lean_dec(v_i_6151_);
v_res_6155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_6153_, v_i_boxed_6154_, v_bs_6152_);
return v_res_6155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_6156_, lean_object* v_ps_6157_, uint8_t v_only_6158_, lean_object* v_k_6159_, lean_object* v_a_6160_, lean_object* v_a_6161_, lean_object* v_a_6162_, lean_object* v_a_6163_, lean_object* v_a_6164_, lean_object* v_a_6165_, lean_object* v_a_6166_, lean_object* v_a_6167_){
_start:
{
lean_object* v___y_6170_; lean_object* v___y_6171_; lean_object* v___y_6172_; lean_object* v___y_6173_; lean_object* v___y_6174_; lean_object* v___y_6175_; lean_object* v___y_6176_; lean_object* v___y_6177_; lean_object* v___y_6178_; uint8_t v___y_6191_; uint8_t v___y_6192_; lean_object* v_params_6193_; lean_object* v___y_6194_; lean_object* v___y_6195_; lean_object* v___y_6196_; lean_object* v___y_6197_; lean_object* v___y_6198_; lean_object* v___y_6199_; lean_object* v___y_6200_; lean_object* v___y_6201_; uint8_t v___y_6305_; 
if (v_only_6158_ == 0)
{
lean_object* v___x_6327_; lean_object* v___x_6328_; uint8_t v___x_6329_; 
v___x_6327_ = lean_array_get_size(v_ps_6157_);
v___x_6328_ = lean_unsigned_to_nat(0u);
v___x_6329_ = lean_nat_dec_eq(v___x_6327_, v___x_6328_);
if (v___x_6329_ == 0)
{
v___y_6305_ = v___x_6329_;
goto v___jp_6304_;
}
else
{
lean_object* v___x_6330_; 
lean_dec_ref(v_params_6156_);
lean_inc(v_a_6167_);
lean_inc_ref(v_a_6166_);
lean_inc(v_a_6165_);
lean_inc_ref(v_a_6164_);
lean_inc(v_a_6163_);
lean_inc_ref(v_a_6162_);
lean_inc(v_a_6161_);
lean_inc_ref(v_a_6160_);
v___x_6330_ = lean_apply_9(v_k_6159_, v_a_6160_, v_a_6161_, v_a_6162_, v_a_6163_, v_a_6164_, v_a_6165_, v_a_6166_, v_a_6167_, lean_box(0));
return v___x_6330_;
}
}
else
{
uint8_t v___x_6331_; 
v___x_6331_ = 0;
v___y_6305_ = v___x_6331_;
goto v___jp_6304_;
}
v___jp_6169_:
{
lean_object* v___x_6179_; lean_object* v___x_6180_; 
v___x_6179_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_6179_, 0, v___y_6170_);
v___x_6180_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_6179_, v___y_6171_, v___y_6172_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_);
if (lean_obj_tag(v___x_6180_) == 0)
{
lean_object* v___x_6181_; 
lean_dec_ref_known(v___x_6180_, 1);
lean_inc(v___y_6178_);
lean_inc_ref(v___y_6177_);
lean_inc(v___y_6176_);
lean_inc_ref(v___y_6175_);
lean_inc(v___y_6174_);
lean_inc_ref(v___y_6173_);
lean_inc(v___y_6172_);
v___x_6181_ = lean_apply_9(v_k_6159_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, lean_box(0));
return v___x_6181_;
}
else
{
lean_object* v_a_6182_; lean_object* v___x_6184_; uint8_t v_isShared_6185_; uint8_t v_isSharedCheck_6189_; 
lean_dec_ref(v___y_6171_);
lean_dec_ref(v_k_6159_);
v_a_6182_ = lean_ctor_get(v___x_6180_, 0);
v_isSharedCheck_6189_ = !lean_is_exclusive(v___x_6180_);
if (v_isSharedCheck_6189_ == 0)
{
v___x_6184_ = v___x_6180_;
v_isShared_6185_ = v_isSharedCheck_6189_;
goto v_resetjp_6183_;
}
else
{
lean_inc(v_a_6182_);
lean_dec(v___x_6180_);
v___x_6184_ = lean_box(0);
v_isShared_6185_ = v_isSharedCheck_6189_;
goto v_resetjp_6183_;
}
v_resetjp_6183_:
{
lean_object* v___x_6187_; 
if (v_isShared_6185_ == 0)
{
v___x_6187_ = v___x_6184_;
goto v_reusejp_6186_;
}
else
{
lean_object* v_reuseFailAlloc_6188_; 
v_reuseFailAlloc_6188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6188_, 0, v_a_6182_);
v___x_6187_ = v_reuseFailAlloc_6188_;
goto v_reusejp_6186_;
}
v_reusejp_6186_:
{
return v___x_6187_;
}
}
}
}
v___jp_6190_:
{
lean_object* v___x_6202_; 
v___x_6202_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_6193_, v_ps_6157_, v_only_6158_, v___y_6191_, v___y_6192_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
if (lean_obj_tag(v___x_6202_) == 0)
{
lean_object* v_a_6203_; lean_object* v_ctx_6204_; lean_object* v_anchorRefs_x3f_6205_; lean_object* v_toContext_6206_; lean_object* v_sctx_6207_; lean_object* v_methods_6208_; uint8_t v_sym_6209_; lean_object* v_simp_6210_; lean_object* v_simpMethods_6211_; lean_object* v_symSimpMethods_6212_; lean_object* v_symDSimpMethods_6213_; lean_object* v_config_6214_; uint8_t v_cheapCases_6215_; uint8_t v_reportMVarIssue_6216_; lean_object* v_splitSource_6217_; lean_object* v_ematchDiagSource_6218_; lean_object* v_symPrios_6219_; lean_object* v_extensions_6220_; uint8_t v_debug_6221_; uint8_t v_ematchDiag_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; 
v_a_6203_ = lean_ctor_get(v___x_6202_, 0);
lean_inc_n(v_a_6203_, 2);
lean_dec_ref_known(v___x_6202_, 1);
v_ctx_6204_ = lean_ctor_get(v___y_6194_, 1);
v_anchorRefs_x3f_6205_ = lean_ctor_get(v_a_6203_, 8);
v_toContext_6206_ = lean_ctor_get(v___y_6194_, 0);
v_sctx_6207_ = lean_ctor_get(v___y_6194_, 2);
v_methods_6208_ = lean_ctor_get(v___y_6194_, 3);
v_sym_6209_ = lean_ctor_get_uint8(v___y_6194_, sizeof(void*)*5);
v_simp_6210_ = lean_ctor_get(v_ctx_6204_, 0);
v_simpMethods_6211_ = lean_ctor_get(v_ctx_6204_, 1);
v_symSimpMethods_6212_ = lean_ctor_get(v_ctx_6204_, 2);
v_symDSimpMethods_6213_ = lean_ctor_get(v_ctx_6204_, 3);
v_config_6214_ = lean_ctor_get(v_ctx_6204_, 4);
v_cheapCases_6215_ = lean_ctor_get_uint8(v_ctx_6204_, sizeof(void*)*10);
v_reportMVarIssue_6216_ = lean_ctor_get_uint8(v_ctx_6204_, sizeof(void*)*10 + 1);
v_splitSource_6217_ = lean_ctor_get(v_ctx_6204_, 6);
v_ematchDiagSource_6218_ = lean_ctor_get(v_ctx_6204_, 7);
v_symPrios_6219_ = lean_ctor_get(v_ctx_6204_, 8);
v_extensions_6220_ = lean_ctor_get(v_ctx_6204_, 9);
v_debug_6221_ = lean_ctor_get_uint8(v_ctx_6204_, sizeof(void*)*10 + 2);
v_ematchDiag_6222_ = lean_ctor_get_uint8(v_ctx_6204_, sizeof(void*)*10 + 3);
lean_inc_ref(v_extensions_6220_);
lean_inc_ref(v_symPrios_6219_);
lean_inc(v_ematchDiagSource_6218_);
lean_inc(v_splitSource_6217_);
lean_inc(v_anchorRefs_x3f_6205_);
lean_inc_ref(v_config_6214_);
lean_inc_ref(v_symDSimpMethods_6213_);
lean_inc_ref(v_symSimpMethods_6212_);
lean_inc_ref(v_simpMethods_6211_);
lean_inc_ref(v_simp_6210_);
v___x_6223_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_6223_, 0, v_simp_6210_);
lean_ctor_set(v___x_6223_, 1, v_simpMethods_6211_);
lean_ctor_set(v___x_6223_, 2, v_symSimpMethods_6212_);
lean_ctor_set(v___x_6223_, 3, v_symDSimpMethods_6213_);
lean_ctor_set(v___x_6223_, 4, v_config_6214_);
lean_ctor_set(v___x_6223_, 5, v_anchorRefs_x3f_6205_);
lean_ctor_set(v___x_6223_, 6, v_splitSource_6217_);
lean_ctor_set(v___x_6223_, 7, v_ematchDiagSource_6218_);
lean_ctor_set(v___x_6223_, 8, v_symPrios_6219_);
lean_ctor_set(v___x_6223_, 9, v_extensions_6220_);
lean_ctor_set_uint8(v___x_6223_, sizeof(void*)*10, v_cheapCases_6215_);
lean_ctor_set_uint8(v___x_6223_, sizeof(void*)*10 + 1, v_reportMVarIssue_6216_);
lean_ctor_set_uint8(v___x_6223_, sizeof(void*)*10 + 2, v_debug_6221_);
lean_ctor_set_uint8(v___x_6223_, sizeof(void*)*10 + 3, v_ematchDiag_6222_);
lean_inc_ref(v_methods_6208_);
lean_inc_ref(v_sctx_6207_);
lean_inc_ref(v_toContext_6206_);
v___x_6224_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_6224_, 0, v_toContext_6206_);
lean_ctor_set(v___x_6224_, 1, v___x_6223_);
lean_ctor_set(v___x_6224_, 2, v_sctx_6207_);
lean_ctor_set(v___x_6224_, 3, v_methods_6208_);
lean_ctor_set(v___x_6224_, 4, v_a_6203_);
lean_ctor_set_uint8(v___x_6224_, sizeof(void*)*5, v_sym_6209_);
if (v_only_6158_ == 0)
{
v___y_6170_ = v_a_6203_;
v___y_6171_ = v___x_6224_;
v___y_6172_ = v___y_6195_;
v___y_6173_ = v___y_6196_;
v___y_6174_ = v___y_6197_;
v___y_6175_ = v___y_6198_;
v___y_6176_ = v___y_6199_;
v___y_6177_ = v___y_6200_;
v___y_6178_ = v___y_6201_;
goto v___jp_6169_;
}
else
{
lean_object* v___x_6225_; 
v___x_6225_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_6195_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
if (lean_obj_tag(v___x_6225_) == 0)
{
lean_object* v_a_6226_; lean_object* v_toGoalState_6227_; lean_object* v_ematch_6228_; lean_object* v_mvarId_6229_; lean_object* v___x_6231_; uint8_t v_isShared_6232_; uint8_t v_isSharedCheck_6286_; 
v_a_6226_ = lean_ctor_get(v___x_6225_, 0);
lean_inc(v_a_6226_);
lean_dec_ref_known(v___x_6225_, 1);
v_toGoalState_6227_ = lean_ctor_get(v_a_6226_, 0);
lean_inc_ref(v_toGoalState_6227_);
v_ematch_6228_ = lean_ctor_get(v_toGoalState_6227_, 13);
lean_inc_ref(v_ematch_6228_);
v_mvarId_6229_ = lean_ctor_get(v_a_6226_, 1);
v_isSharedCheck_6286_ = !lean_is_exclusive(v_a_6226_);
if (v_isSharedCheck_6286_ == 0)
{
lean_object* v_unused_6287_; 
v_unused_6287_ = lean_ctor_get(v_a_6226_, 0);
lean_dec(v_unused_6287_);
v___x_6231_ = v_a_6226_;
v_isShared_6232_ = v_isSharedCheck_6286_;
goto v_resetjp_6230_;
}
else
{
lean_inc(v_mvarId_6229_);
lean_dec(v_a_6226_);
v___x_6231_ = lean_box(0);
v_isShared_6232_ = v_isSharedCheck_6286_;
goto v_resetjp_6230_;
}
v_resetjp_6230_:
{
lean_object* v_nextDeclIdx_6233_; lean_object* v_enodeMap_6234_; lean_object* v_exprs_6235_; lean_object* v_parents_6236_; lean_object* v_congrTable_6237_; lean_object* v_appMap_6238_; lean_object* v_indicesFound_6239_; lean_object* v_toProcess_6240_; lean_object* v_internalizing_6241_; uint8_t v_inconsistent_6242_; lean_object* v_nextIdx_6243_; lean_object* v_newRawFacts_6244_; lean_object* v_facts_6245_; lean_object* v_extThms_6246_; lean_object* v_inj_6247_; lean_object* v_split_6248_; lean_object* v_clean_6249_; lean_object* v_sstates_6250_; lean_object* v_gmt_6251_; lean_object* v_thms_6252_; lean_object* v_newThms_6253_; lean_object* v_numInstances_6254_; lean_object* v_numDelayedInstances_6255_; lean_object* v_num_6256_; lean_object* v_preInstances_6257_; lean_object* v_nextThmIdx_6258_; lean_object* v_matchEqNames_6259_; lean_object* v_delayedThmInsts_6260_; lean_object* v___x_6261_; lean_object* v___f_6262_; lean_object* v___x_6263_; 
v_nextDeclIdx_6233_ = lean_ctor_get(v_toGoalState_6227_, 0);
lean_inc(v_nextDeclIdx_6233_);
v_enodeMap_6234_ = lean_ctor_get(v_toGoalState_6227_, 1);
lean_inc_ref(v_enodeMap_6234_);
v_exprs_6235_ = lean_ctor_get(v_toGoalState_6227_, 2);
lean_inc_ref(v_exprs_6235_);
v_parents_6236_ = lean_ctor_get(v_toGoalState_6227_, 3);
lean_inc_ref(v_parents_6236_);
v_congrTable_6237_ = lean_ctor_get(v_toGoalState_6227_, 4);
lean_inc_ref(v_congrTable_6237_);
v_appMap_6238_ = lean_ctor_get(v_toGoalState_6227_, 5);
lean_inc_ref(v_appMap_6238_);
v_indicesFound_6239_ = lean_ctor_get(v_toGoalState_6227_, 6);
lean_inc_ref(v_indicesFound_6239_);
v_toProcess_6240_ = lean_ctor_get(v_toGoalState_6227_, 7);
lean_inc_ref(v_toProcess_6240_);
v_internalizing_6241_ = lean_ctor_get(v_toGoalState_6227_, 8);
lean_inc_ref(v_internalizing_6241_);
v_inconsistent_6242_ = lean_ctor_get_uint8(v_toGoalState_6227_, sizeof(void*)*18);
v_nextIdx_6243_ = lean_ctor_get(v_toGoalState_6227_, 9);
lean_inc(v_nextIdx_6243_);
v_newRawFacts_6244_ = lean_ctor_get(v_toGoalState_6227_, 10);
lean_inc_ref(v_newRawFacts_6244_);
v_facts_6245_ = lean_ctor_get(v_toGoalState_6227_, 11);
lean_inc_ref(v_facts_6245_);
v_extThms_6246_ = lean_ctor_get(v_toGoalState_6227_, 12);
lean_inc_ref(v_extThms_6246_);
v_inj_6247_ = lean_ctor_get(v_toGoalState_6227_, 14);
lean_inc_ref(v_inj_6247_);
v_split_6248_ = lean_ctor_get(v_toGoalState_6227_, 15);
lean_inc_ref(v_split_6248_);
v_clean_6249_ = lean_ctor_get(v_toGoalState_6227_, 16);
lean_inc_ref(v_clean_6249_);
v_sstates_6250_ = lean_ctor_get(v_toGoalState_6227_, 17);
lean_inc_ref(v_sstates_6250_);
lean_dec_ref(v_toGoalState_6227_);
v_gmt_6251_ = lean_ctor_get(v_ematch_6228_, 1);
lean_inc(v_gmt_6251_);
v_thms_6252_ = lean_ctor_get(v_ematch_6228_, 2);
lean_inc_ref(v_thms_6252_);
v_newThms_6253_ = lean_ctor_get(v_ematch_6228_, 3);
lean_inc_ref(v_newThms_6253_);
v_numInstances_6254_ = lean_ctor_get(v_ematch_6228_, 4);
lean_inc(v_numInstances_6254_);
v_numDelayedInstances_6255_ = lean_ctor_get(v_ematch_6228_, 5);
lean_inc(v_numDelayedInstances_6255_);
v_num_6256_ = lean_ctor_get(v_ematch_6228_, 6);
lean_inc(v_num_6256_);
v_preInstances_6257_ = lean_ctor_get(v_ematch_6228_, 7);
lean_inc_ref(v_preInstances_6257_);
v_nextThmIdx_6258_ = lean_ctor_get(v_ematch_6228_, 8);
lean_inc(v_nextThmIdx_6258_);
v_matchEqNames_6259_ = lean_ctor_get(v_ematch_6228_, 9);
lean_inc_ref(v_matchEqNames_6259_);
v_delayedThmInsts_6260_ = lean_ctor_get(v_ematch_6228_, 10);
lean_inc_ref(v_delayedThmInsts_6260_);
lean_dec_ref(v_ematch_6228_);
v___x_6261_ = lean_box(v_inconsistent_6242_);
v___f_6262_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 39, 29);
lean_closure_set(v___f_6262_, 0, v_thms_6252_);
lean_closure_set(v___f_6262_, 1, v_newThms_6253_);
lean_closure_set(v___f_6262_, 2, v_gmt_6251_);
lean_closure_set(v___f_6262_, 3, v_numInstances_6254_);
lean_closure_set(v___f_6262_, 4, v_numDelayedInstances_6255_);
lean_closure_set(v___f_6262_, 5, v_num_6256_);
lean_closure_set(v___f_6262_, 6, v_preInstances_6257_);
lean_closure_set(v___f_6262_, 7, v_nextThmIdx_6258_);
lean_closure_set(v___f_6262_, 8, v_matchEqNames_6259_);
lean_closure_set(v___f_6262_, 9, v_delayedThmInsts_6260_);
lean_closure_set(v___f_6262_, 10, v_nextDeclIdx_6233_);
lean_closure_set(v___f_6262_, 11, v_enodeMap_6234_);
lean_closure_set(v___f_6262_, 12, v_exprs_6235_);
lean_closure_set(v___f_6262_, 13, v_parents_6236_);
lean_closure_set(v___f_6262_, 14, v_congrTable_6237_);
lean_closure_set(v___f_6262_, 15, v_appMap_6238_);
lean_closure_set(v___f_6262_, 16, v_indicesFound_6239_);
lean_closure_set(v___f_6262_, 17, v_toProcess_6240_);
lean_closure_set(v___f_6262_, 18, v_internalizing_6241_);
lean_closure_set(v___f_6262_, 19, v___x_6261_);
lean_closure_set(v___f_6262_, 20, v_nextIdx_6243_);
lean_closure_set(v___f_6262_, 21, v_newRawFacts_6244_);
lean_closure_set(v___f_6262_, 22, v_facts_6245_);
lean_closure_set(v___f_6262_, 23, v_extThms_6246_);
lean_closure_set(v___f_6262_, 24, v_inj_6247_);
lean_closure_set(v___f_6262_, 25, v_split_6248_);
lean_closure_set(v___f_6262_, 26, v_clean_6249_);
lean_closure_set(v___f_6262_, 27, v_sstates_6250_);
lean_closure_set(v___f_6262_, 28, v_mvarId_6229_);
v___x_6263_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_6262_, v___x_6224_, v___y_6195_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
if (lean_obj_tag(v___x_6263_) == 0)
{
lean_object* v_a_6264_; lean_object* v___x_6265_; lean_object* v___x_6267_; 
v_a_6264_ = lean_ctor_get(v___x_6263_, 0);
lean_inc(v_a_6264_);
lean_dec_ref_known(v___x_6263_, 1);
v___x_6265_ = lean_box(0);
if (v_isShared_6232_ == 0)
{
lean_ctor_set_tag(v___x_6231_, 1);
lean_ctor_set(v___x_6231_, 1, v___x_6265_);
lean_ctor_set(v___x_6231_, 0, v_a_6264_);
v___x_6267_ = v___x_6231_;
goto v_reusejp_6266_;
}
else
{
lean_object* v_reuseFailAlloc_6277_; 
v_reuseFailAlloc_6277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6277_, 0, v_a_6264_);
lean_ctor_set(v_reuseFailAlloc_6277_, 1, v___x_6265_);
v___x_6267_ = v_reuseFailAlloc_6277_;
goto v_reusejp_6266_;
}
v_reusejp_6266_:
{
lean_object* v___x_6268_; 
v___x_6268_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_6267_, v___y_6195_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
if (lean_obj_tag(v___x_6268_) == 0)
{
lean_dec_ref_known(v___x_6268_, 1);
v___y_6170_ = v_a_6203_;
v___y_6171_ = v___x_6224_;
v___y_6172_ = v___y_6195_;
v___y_6173_ = v___y_6196_;
v___y_6174_ = v___y_6197_;
v___y_6175_ = v___y_6198_;
v___y_6176_ = v___y_6199_;
v___y_6177_ = v___y_6200_;
v___y_6178_ = v___y_6201_;
goto v___jp_6169_;
}
else
{
lean_object* v_a_6269_; lean_object* v___x_6271_; uint8_t v_isShared_6272_; uint8_t v_isSharedCheck_6276_; 
lean_dec_ref_known(v___x_6224_, 5);
lean_dec(v_a_6203_);
lean_dec_ref(v_k_6159_);
v_a_6269_ = lean_ctor_get(v___x_6268_, 0);
v_isSharedCheck_6276_ = !lean_is_exclusive(v___x_6268_);
if (v_isSharedCheck_6276_ == 0)
{
v___x_6271_ = v___x_6268_;
v_isShared_6272_ = v_isSharedCheck_6276_;
goto v_resetjp_6270_;
}
else
{
lean_inc(v_a_6269_);
lean_dec(v___x_6268_);
v___x_6271_ = lean_box(0);
v_isShared_6272_ = v_isSharedCheck_6276_;
goto v_resetjp_6270_;
}
v_resetjp_6270_:
{
lean_object* v___x_6274_; 
if (v_isShared_6272_ == 0)
{
v___x_6274_ = v___x_6271_;
goto v_reusejp_6273_;
}
else
{
lean_object* v_reuseFailAlloc_6275_; 
v_reuseFailAlloc_6275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6275_, 0, v_a_6269_);
v___x_6274_ = v_reuseFailAlloc_6275_;
goto v_reusejp_6273_;
}
v_reusejp_6273_:
{
return v___x_6274_;
}
}
}
}
}
else
{
lean_object* v_a_6278_; lean_object* v___x_6280_; uint8_t v_isShared_6281_; uint8_t v_isSharedCheck_6285_; 
lean_del_object(v___x_6231_);
lean_dec_ref_known(v___x_6224_, 5);
lean_dec(v_a_6203_);
lean_dec_ref(v_k_6159_);
v_a_6278_ = lean_ctor_get(v___x_6263_, 0);
v_isSharedCheck_6285_ = !lean_is_exclusive(v___x_6263_);
if (v_isSharedCheck_6285_ == 0)
{
v___x_6280_ = v___x_6263_;
v_isShared_6281_ = v_isSharedCheck_6285_;
goto v_resetjp_6279_;
}
else
{
lean_inc(v_a_6278_);
lean_dec(v___x_6263_);
v___x_6280_ = lean_box(0);
v_isShared_6281_ = v_isSharedCheck_6285_;
goto v_resetjp_6279_;
}
v_resetjp_6279_:
{
lean_object* v___x_6283_; 
if (v_isShared_6281_ == 0)
{
v___x_6283_ = v___x_6280_;
goto v_reusejp_6282_;
}
else
{
lean_object* v_reuseFailAlloc_6284_; 
v_reuseFailAlloc_6284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6284_, 0, v_a_6278_);
v___x_6283_ = v_reuseFailAlloc_6284_;
goto v_reusejp_6282_;
}
v_reusejp_6282_:
{
return v___x_6283_;
}
}
}
}
}
else
{
lean_object* v_a_6288_; lean_object* v___x_6290_; uint8_t v_isShared_6291_; uint8_t v_isSharedCheck_6295_; 
lean_dec_ref_known(v___x_6224_, 5);
lean_dec(v_a_6203_);
lean_dec_ref(v_k_6159_);
v_a_6288_ = lean_ctor_get(v___x_6225_, 0);
v_isSharedCheck_6295_ = !lean_is_exclusive(v___x_6225_);
if (v_isSharedCheck_6295_ == 0)
{
v___x_6290_ = v___x_6225_;
v_isShared_6291_ = v_isSharedCheck_6295_;
goto v_resetjp_6289_;
}
else
{
lean_inc(v_a_6288_);
lean_dec(v___x_6225_);
v___x_6290_ = lean_box(0);
v_isShared_6291_ = v_isSharedCheck_6295_;
goto v_resetjp_6289_;
}
v_resetjp_6289_:
{
lean_object* v___x_6293_; 
if (v_isShared_6291_ == 0)
{
v___x_6293_ = v___x_6290_;
goto v_reusejp_6292_;
}
else
{
lean_object* v_reuseFailAlloc_6294_; 
v_reuseFailAlloc_6294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6294_, 0, v_a_6288_);
v___x_6293_ = v_reuseFailAlloc_6294_;
goto v_reusejp_6292_;
}
v_reusejp_6292_:
{
return v___x_6293_;
}
}
}
}
}
else
{
lean_object* v_a_6296_; lean_object* v___x_6298_; uint8_t v_isShared_6299_; uint8_t v_isSharedCheck_6303_; 
lean_dec_ref(v_k_6159_);
v_a_6296_ = lean_ctor_get(v___x_6202_, 0);
v_isSharedCheck_6303_ = !lean_is_exclusive(v___x_6202_);
if (v_isSharedCheck_6303_ == 0)
{
v___x_6298_ = v___x_6202_;
v_isShared_6299_ = v_isSharedCheck_6303_;
goto v_resetjp_6297_;
}
else
{
lean_inc(v_a_6296_);
lean_dec(v___x_6202_);
v___x_6298_ = lean_box(0);
v_isShared_6299_ = v_isSharedCheck_6303_;
goto v_resetjp_6297_;
}
v_resetjp_6297_:
{
lean_object* v___x_6301_; 
if (v_isShared_6299_ == 0)
{
v___x_6301_ = v___x_6298_;
goto v_reusejp_6300_;
}
else
{
lean_object* v_reuseFailAlloc_6302_; 
v_reuseFailAlloc_6302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6302_, 0, v_a_6296_);
v___x_6301_ = v_reuseFailAlloc_6302_;
goto v_reusejp_6300_;
}
v_reusejp_6300_:
{
return v___x_6301_;
}
}
}
}
v___jp_6304_:
{
uint8_t v___x_6306_; 
v___x_6306_ = 1;
if (v_only_6158_ == 0)
{
v___y_6191_ = v___y_6305_;
v___y_6192_ = v___x_6306_;
v_params_6193_ = v_params_6156_;
v___y_6194_ = v_a_6160_;
v___y_6195_ = v_a_6161_;
v___y_6196_ = v_a_6162_;
v___y_6197_ = v_a_6163_;
v___y_6198_ = v_a_6164_;
v___y_6199_ = v_a_6165_;
v___y_6200_ = v_a_6166_;
v___y_6201_ = v_a_6167_;
goto v___jp_6190_;
}
else
{
lean_object* v_config_6307_; lean_object* v_extensions_6308_; lean_object* v_extra_6309_; lean_object* v_extraInj_6310_; lean_object* v_extraFacts_6311_; lean_object* v_symPrios_6312_; lean_object* v_norm_6313_; lean_object* v_normProcs_6314_; lean_object* v___x_6316_; uint8_t v_isShared_6317_; uint8_t v_isSharedCheck_6325_; 
v_config_6307_ = lean_ctor_get(v_params_6156_, 0);
v_extensions_6308_ = lean_ctor_get(v_params_6156_, 1);
v_extra_6309_ = lean_ctor_get(v_params_6156_, 2);
v_extraInj_6310_ = lean_ctor_get(v_params_6156_, 3);
v_extraFacts_6311_ = lean_ctor_get(v_params_6156_, 4);
v_symPrios_6312_ = lean_ctor_get(v_params_6156_, 5);
v_norm_6313_ = lean_ctor_get(v_params_6156_, 6);
v_normProcs_6314_ = lean_ctor_get(v_params_6156_, 7);
v_isSharedCheck_6325_ = !lean_is_exclusive(v_params_6156_);
if (v_isSharedCheck_6325_ == 0)
{
lean_object* v_unused_6326_; 
v_unused_6326_ = lean_ctor_get(v_params_6156_, 8);
lean_dec(v_unused_6326_);
v___x_6316_ = v_params_6156_;
v_isShared_6317_ = v_isSharedCheck_6325_;
goto v_resetjp_6315_;
}
else
{
lean_inc(v_normProcs_6314_);
lean_inc(v_norm_6313_);
lean_inc(v_symPrios_6312_);
lean_inc(v_extraFacts_6311_);
lean_inc(v_extraInj_6310_);
lean_inc(v_extra_6309_);
lean_inc(v_extensions_6308_);
lean_inc(v_config_6307_);
lean_dec(v_params_6156_);
v___x_6316_ = lean_box(0);
v_isShared_6317_ = v_isSharedCheck_6325_;
goto v_resetjp_6315_;
}
v_resetjp_6315_:
{
size_t v_sz_6318_; size_t v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v_params_6323_; 
v_sz_6318_ = lean_array_size(v_extensions_6308_);
v___x_6319_ = ((size_t)0ULL);
v___x_6320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_6318_, v___x_6319_, v_extensions_6308_);
v___x_6321_ = lean_box(0);
if (v_isShared_6317_ == 0)
{
lean_ctor_set(v___x_6316_, 8, v___x_6321_);
lean_ctor_set(v___x_6316_, 1, v___x_6320_);
v_params_6323_ = v___x_6316_;
goto v_reusejp_6322_;
}
else
{
lean_object* v_reuseFailAlloc_6324_; 
v_reuseFailAlloc_6324_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6324_, 0, v_config_6307_);
lean_ctor_set(v_reuseFailAlloc_6324_, 1, v___x_6320_);
lean_ctor_set(v_reuseFailAlloc_6324_, 2, v_extra_6309_);
lean_ctor_set(v_reuseFailAlloc_6324_, 3, v_extraInj_6310_);
lean_ctor_set(v_reuseFailAlloc_6324_, 4, v_extraFacts_6311_);
lean_ctor_set(v_reuseFailAlloc_6324_, 5, v_symPrios_6312_);
lean_ctor_set(v_reuseFailAlloc_6324_, 6, v_norm_6313_);
lean_ctor_set(v_reuseFailAlloc_6324_, 7, v_normProcs_6314_);
lean_ctor_set(v_reuseFailAlloc_6324_, 8, v___x_6321_);
v_params_6323_ = v_reuseFailAlloc_6324_;
goto v_reusejp_6322_;
}
v_reusejp_6322_:
{
v___y_6191_ = v___y_6305_;
v___y_6192_ = v___x_6306_;
v_params_6193_ = v_params_6323_;
v___y_6194_ = v_a_6160_;
v___y_6195_ = v_a_6161_;
v___y_6196_ = v_a_6162_;
v___y_6197_ = v_a_6163_;
v___y_6198_ = v_a_6164_;
v___y_6199_ = v_a_6165_;
v___y_6200_ = v_a_6166_;
v___y_6201_ = v_a_6167_;
goto v___jp_6190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_6332_, lean_object* v_ps_6333_, lean_object* v_only_6334_, lean_object* v_k_6335_, lean_object* v_a_6336_, lean_object* v_a_6337_, lean_object* v_a_6338_, lean_object* v_a_6339_, lean_object* v_a_6340_, lean_object* v_a_6341_, lean_object* v_a_6342_, lean_object* v_a_6343_, lean_object* v_a_6344_){
_start:
{
uint8_t v_only_boxed_6345_; lean_object* v_res_6346_; 
v_only_boxed_6345_ = lean_unbox(v_only_6334_);
v_res_6346_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_6332_, v_ps_6333_, v_only_boxed_6345_, v_k_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_);
lean_dec(v_a_6343_);
lean_dec_ref(v_a_6342_);
lean_dec(v_a_6341_);
lean_dec_ref(v_a_6340_);
lean_dec(v_a_6339_);
lean_dec_ref(v_a_6338_);
lean_dec(v_a_6337_);
lean_dec_ref(v_a_6336_);
lean_dec_ref(v_ps_6333_);
return v_res_6346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_6347_, lean_object* v_params_6348_, lean_object* v_ps_6349_, uint8_t v_only_6350_, lean_object* v_k_6351_, lean_object* v_a_6352_, lean_object* v_a_6353_, lean_object* v_a_6354_, lean_object* v_a_6355_, lean_object* v_a_6356_, lean_object* v_a_6357_, lean_object* v_a_6358_, lean_object* v_a_6359_){
_start:
{
lean_object* v___x_6361_; 
v___x_6361_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_6348_, v_ps_6349_, v_only_6350_, v_k_6351_, v_a_6352_, v_a_6353_, v_a_6354_, v_a_6355_, v_a_6356_, v_a_6357_, v_a_6358_, v_a_6359_);
return v___x_6361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_6362_, lean_object* v_params_6363_, lean_object* v_ps_6364_, lean_object* v_only_6365_, lean_object* v_k_6366_, lean_object* v_a_6367_, lean_object* v_a_6368_, lean_object* v_a_6369_, lean_object* v_a_6370_, lean_object* v_a_6371_, lean_object* v_a_6372_, lean_object* v_a_6373_, lean_object* v_a_6374_, lean_object* v_a_6375_){
_start:
{
uint8_t v_only_boxed_6376_; lean_object* v_res_6377_; 
v_only_boxed_6376_ = lean_unbox(v_only_6365_);
v_res_6377_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_6362_, v_params_6363_, v_ps_6364_, v_only_boxed_6376_, v_k_6366_, v_a_6367_, v_a_6368_, v_a_6369_, v_a_6370_, v_a_6371_, v_a_6372_, v_a_6373_, v_a_6374_);
lean_dec(v_a_6374_);
lean_dec_ref(v_a_6373_);
lean_dec(v_a_6372_);
lean_dec_ref(v_a_6371_);
lean_dec(v_a_6370_);
lean_dec_ref(v_a_6369_);
lean_dec(v_a_6368_);
lean_dec_ref(v_a_6367_);
lean_dec_ref(v_ps_6364_);
return v_res_6377_;
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
