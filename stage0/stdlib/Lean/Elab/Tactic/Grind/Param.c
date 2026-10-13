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
lean_object* l_Lean_AsyncConstantInfo_toConstantVal(lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(lean_object* v_declName_1837_, lean_object* v_symPrios_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
uint8_t v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = 0;
lean_inc(v_declName_1837_);
v___x_1845_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1837_, v___x_1844_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1922_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1922_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1922_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
uint8_t v_kind_1919_; 
v_kind_1919_ = lean_ctor_get_uint8(v_a_1846_, sizeof(void*)*3);
switch(v_kind_1919_)
{
case 1:
{
goto v___jp_1850_;
}
case 2:
{
goto v___jp_1850_;
}
case 6:
{
goto v___jp_1850_;
}
default: 
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_del_object(v___x_1848_);
lean_dec(v_a_1846_);
lean_dec_ref(v_symPrios_1838_);
lean_dec(v_declName_1837_);
v___x_1920_ = lean_box(v___x_1844_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
v___jp_1850_:
{
lean_object* v___x_1851_; lean_object* v_levelParams_1852_; lean_object* v_type_1853_; uint8_t v___x_1854_; 
v___x_1851_ = l_Lean_AsyncConstantInfo_toConstantVal(v_a_1846_);
v_levelParams_1852_ = lean_ctor_get(v___x_1851_, 1);
lean_inc(v_levelParams_1852_);
v_type_1853_ = lean_ctor_get(v___x_1851_, 2);
lean_inc_ref(v_type_1853_);
lean_dec_ref(v___x_1851_);
v___x_1854_ = l_List_isEmpty___redArg(v_levelParams_1852_);
lean_dec(v_levelParams_1852_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_dec_ref(v_type_1853_);
lean_dec_ref(v_symPrios_1838_);
lean_dec(v_declName_1837_);
v___x_1855_ = lean_box(v___x_1844_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1855_);
v___x_1857_ = v___x_1848_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
else
{
lean_object* v___x_1859_; 
lean_del_object(v___x_1848_);
lean_inc_ref(v_type_1853_);
v___x_1859_ = l_Lean_Meta_whnfR(v_type_1853_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1910_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1910_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1910_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
uint8_t v___x_1864_; 
v___x_1864_ = l_Lean_Expr_isForall(v_a_1860_);
lean_dec(v_a_1860_);
if (v___x_1864_ == 0)
{
if (v___x_1854_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
lean_dec_ref(v_type_1853_);
lean_dec_ref(v_symPrios_1838_);
lean_dec(v_declName_1837_);
v___x_1865_ = lean_box(v___x_1844_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1865_);
v___x_1867_ = v___x_1862_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
else
{
lean_object* v___x_1869_; 
lean_del_object(v___x_1862_);
v___x_1869_ = l_Lean_Meta_isProp(v_type_1853_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1905_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1905_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1905_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
uint8_t v___x_1874_; 
v___x_1874_ = lean_unbox(v_a_1870_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
lean_dec(v_a_1870_);
lean_dec_ref(v_symPrios_1838_);
lean_dec(v_declName_1837_);
v___x_1875_ = lean_box(v___x_1844_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1875_);
v___x_1877_ = v___x_1872_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_del_object(v___x_1872_);
lean_inc(v_declName_1837_);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_declName_1837_);
v___x_1880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__0));
v___x_1881_ = lean_box(0);
v___x_1882_ = l_Lean_mkConst(v_declName_1837_, v___x_1881_);
v___x_1883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v___x_1884_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_1879_, v___x_1880_, v___x_1882_, v___x_1883_, v_symPrios_1838_, v___x_1854_, v___x_1844_, v___x_1844_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1896_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1896_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1896_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
if (lean_obj_tag(v_a_1885_) == 0)
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v_a_1870_);
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1870_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
lean_dec_ref_known(v_a_1885_, 1);
lean_dec(v_a_1870_);
v___x_1892_ = lean_box(v___x_1864_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1892_);
v___x_1894_ = v___x_1887_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v_a_1870_);
v_a_1897_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1884_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1884_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_symPrios_1838_);
lean_dec(v_declName_1837_);
return v___x_1869_;
}
}
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1908_; 
lean_dec_ref(v_type_1853_);
lean_dec_ref(v_symPrios_1838_);
lean_dec(v_declName_1837_);
v___x_1906_ = lean_box(v___x_1844_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1906_);
v___x_1908_ = v___x_1862_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec_ref(v_type_1853_);
lean_dec_ref(v_symPrios_1838_);
lean_dec(v_declName_1837_);
v_a_1911_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1859_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1859_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
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
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref(v_symPrios_1838_);
lean_dec(v_declName_1837_);
v_a_1923_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1845_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1845_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___boxed(lean_object* v_declName_1931_, lean_object* v_symPrios_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(v_declName_1931_, v_symPrios_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(lean_object* v_params_1939_, lean_object* v_declName_1940_, uint8_t v_minIndexable_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1973_; 
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v___x_1947_, 0);
lean_dec(v_unused_1974_);
v___x_1949_ = v___x_1947_;
v_isShared_1950_ = v_isSharedCheck_1973_;
goto v_resetjp_1948_;
}
else
{
lean_dec(v___x_1947_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1973_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v_config_1951_; lean_object* v_extensions_1952_; lean_object* v_extra_1953_; lean_object* v_extraInj_1954_; lean_object* v_extraFacts_1955_; lean_object* v_symPrios_1956_; lean_object* v_norm_1957_; lean_object* v_normProcs_1958_; lean_object* v_anchorRefs_x3f_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1972_; 
v_config_1951_ = lean_ctor_get(v_params_1939_, 0);
v_extensions_1952_ = lean_ctor_get(v_params_1939_, 1);
v_extra_1953_ = lean_ctor_get(v_params_1939_, 2);
v_extraInj_1954_ = lean_ctor_get(v_params_1939_, 3);
v_extraFacts_1955_ = lean_ctor_get(v_params_1939_, 4);
v_symPrios_1956_ = lean_ctor_get(v_params_1939_, 5);
v_norm_1957_ = lean_ctor_get(v_params_1939_, 6);
v_normProcs_1958_ = lean_ctor_get(v_params_1939_, 7);
v_anchorRefs_x3f_1959_ = lean_ctor_get(v_params_1939_, 8);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_params_1939_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1961_ = v_params_1939_;
v_isShared_1962_ = v_isSharedCheck_1972_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_anchorRefs_x3f_1959_);
lean_inc(v_normProcs_1958_);
lean_inc(v_norm_1957_);
lean_inc(v_symPrios_1956_);
lean_inc(v_extraFacts_1955_);
lean_inc(v_extraInj_1954_);
lean_inc(v_extra_1953_);
lean_inc(v_extensions_1952_);
lean_inc(v_config_1951_);
lean_dec(v_params_1939_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1972_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1963_ = lean_box(0);
v___x_1964_ = l_Lean_mkConst(v_declName_1940_, v___x_1963_);
v___x_1965_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_1955_, v___x_1964_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 4, v___x_1965_);
v___x_1967_ = v___x_1961_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_config_1951_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_extensions_1952_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_extra_1953_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_extraInj_1954_);
lean_ctor_set(v_reuseFailAlloc_1971_, 4, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1971_, 5, v_symPrios_1956_);
lean_ctor_set(v_reuseFailAlloc_1971_, 6, v_norm_1957_);
lean_ctor_set(v_reuseFailAlloc_1971_, 7, v_normProcs_1958_);
lean_ctor_set(v_reuseFailAlloc_1971_, 8, v_anchorRefs_x3f_1959_);
v___x_1967_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1969_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1967_);
v___x_1969_ = v___x_1949_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec(v_declName_1940_);
lean_dec_ref(v_params_1939_);
v_a_1975_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1947_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1947_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact___boxed(lean_object* v_params_1983_, lean_object* v_declName_1984_, lean_object* v_minIndexable_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
uint8_t v_minIndexable_boxed_1991_; lean_object* v_res_1992_; 
v_minIndexable_boxed_1991_ = lean_unbox(v_minIndexable_1985_);
v_res_1992_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(v_params_1983_, v_declName_1984_, v_minIndexable_boxed_1991_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1995_, lean_object* v_val_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v_config_2000_; lean_object* v_extensions_2001_; lean_object* v_extra_2002_; lean_object* v_extraInj_2003_; lean_object* v_extraFacts_2004_; lean_object* v_symPrios_2005_; lean_object* v_norm_2006_; lean_object* v_normProcs_2007_; lean_object* v_anchorRefs_x3f_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2038_; 
v_config_2000_ = lean_ctor_get(v_params_1995_, 0);
v_extensions_2001_ = lean_ctor_get(v_params_1995_, 1);
v_extra_2002_ = lean_ctor_get(v_params_1995_, 2);
v_extraInj_2003_ = lean_ctor_get(v_params_1995_, 3);
v_extraFacts_2004_ = lean_ctor_get(v_params_1995_, 4);
v_symPrios_2005_ = lean_ctor_get(v_params_1995_, 5);
v_norm_2006_ = lean_ctor_get(v_params_1995_, 6);
v_normProcs_2007_ = lean_ctor_get(v_params_1995_, 7);
v_anchorRefs_x3f_2008_ = lean_ctor_get(v_params_1995_, 8);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_params_1995_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2010_ = v_params_1995_;
v_isShared_2011_ = v_isSharedCheck_2038_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_anchorRefs_x3f_2008_);
lean_inc(v_normProcs_2007_);
lean_inc(v_norm_2006_);
lean_inc(v_symPrios_2005_);
lean_inc(v_extraFacts_2004_);
lean_inc(v_extraInj_2003_);
lean_inc(v_extra_2002_);
lean_inc(v_extensions_2001_);
lean_inc(v_config_2000_);
lean_dec(v_params_1995_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2038_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___y_2013_; 
if (lean_obj_tag(v_anchorRefs_x3f_2008_) == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_2013_ = v___x_2036_;
goto v___jp_2012_;
}
else
{
lean_object* v_val_2037_; 
v_val_2037_ = lean_ctor_get(v_anchorRefs_x3f_2008_, 0);
lean_inc(v_val_2037_);
lean_dec_ref_known(v_anchorRefs_x3f_2008_, 1);
v___y_2013_ = v_val_2037_;
goto v___jp_2012_;
}
v___jp_2012_:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1996_, v_a_1997_, v_a_1998_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2027_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2027_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2027_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2019_ = lean_array_push(v___y_2013_, v_a_2015_);
v___x_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 8, v___x_2020_);
v___x_2022_ = v___x_2010_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_config_2000_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_extensions_2001_);
lean_ctor_set(v_reuseFailAlloc_2026_, 2, v_extra_2002_);
lean_ctor_set(v_reuseFailAlloc_2026_, 3, v_extraInj_2003_);
lean_ctor_set(v_reuseFailAlloc_2026_, 4, v_extraFacts_2004_);
lean_ctor_set(v_reuseFailAlloc_2026_, 5, v_symPrios_2005_);
lean_ctor_set(v_reuseFailAlloc_2026_, 6, v_norm_2006_);
lean_ctor_set(v_reuseFailAlloc_2026_, 7, v_normProcs_2007_);
lean_ctor_set(v_reuseFailAlloc_2026_, 8, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2024_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2022_);
v___x_2024_ = v___x_2017_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
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
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec_ref(v___y_2013_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_normProcs_2007_);
lean_dec_ref(v_norm_2006_);
lean_dec_ref(v_symPrios_2005_);
lean_dec_ref(v_extraFacts_2004_);
lean_dec_ref(v_extraInj_2003_);
lean_dec_ref(v_extra_2002_);
lean_dec_ref(v_extensions_2001_);
lean_dec_ref(v_config_2000_);
v_a_2028_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2014_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2014_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_2039_, lean_object* v_val_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_2039_, v_val_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_val_2040_);
return v_res_2044_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_config_2052_; uint8_t v_revert_2053_; 
v_config_2052_ = lean_ctor_get(v_params_2048_, 0);
v_revert_2053_ = lean_ctor_get_uint8(v_config_2052_, sizeof(void*)*14 + 31);
if (v_revert_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_box(0);
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_2057_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_2056_, v_a_2049_, v_a_2050_);
return v___x_2057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2058_, v_a_2059_, v_a_2060_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
lean_dec_ref(v_params_2058_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_2063_, lean_object* v___y_2064_){
_start:
{
uint8_t v___x_2066_; 
v___x_2066_ = l_Lean_Expr_hasMVar(v_e_2063_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; 
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v_e_2063_);
return v___x_2067_;
}
else
{
lean_object* v___x_2068_; lean_object* v_mctx_2069_; lean_object* v___x_2070_; lean_object* v_fst_2071_; lean_object* v_snd_2072_; lean_object* v___x_2073_; lean_object* v_cache_2074_; lean_object* v_zetaDeltaFVarIds_2075_; lean_object* v_postponed_2076_; lean_object* v_diag_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2086_; 
v___x_2068_ = lean_st_ref_get(v___y_2064_);
v_mctx_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc_ref(v_mctx_2069_);
lean_dec(v___x_2068_);
v___x_2070_ = l_Lean_instantiateMVarsCore(v_mctx_2069_, v_e_2063_);
v_fst_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_fst_2071_);
v_snd_2072_ = lean_ctor_get(v___x_2070_, 1);
lean_inc(v_snd_2072_);
lean_dec_ref(v___x_2070_);
v___x_2073_ = lean_st_ref_take(v___y_2064_);
v_cache_2074_ = lean_ctor_get(v___x_2073_, 1);
v_zetaDeltaFVarIds_2075_ = lean_ctor_get(v___x_2073_, 2);
v_postponed_2076_ = lean_ctor_get(v___x_2073_, 3);
v_diag_2077_ = lean_ctor_get(v___x_2073_, 4);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v___x_2073_, 0);
lean_dec(v_unused_2087_);
v___x_2079_ = v___x_2073_;
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_diag_2077_);
lean_inc(v_postponed_2076_);
lean_inc(v_zetaDeltaFVarIds_2075_);
lean_inc(v_cache_2074_);
lean_dec(v___x_2073_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2086_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v_snd_2072_);
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_snd_2072_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_cache_2074_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_zetaDeltaFVarIds_2075_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_postponed_2076_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_diag_2077_);
v___x_2082_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = lean_st_ref_put(v___y_2064_, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v_fst_2071_);
return v___x_2084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_2088_, v___y_2089_);
lean_dec(v___y_2089_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_2092_, v___y_2096_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(uint8_t v___x_2110_, uint8_t v___x_2111_, uint8_t v_____do__lift_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
if (v_____do__lift_2112_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = lean_box(v___x_2110_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_box(v___x_2111_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v___x_2124_, lean_object* v___x_2125_, lean_object* v_____do__lift_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
uint8_t v___x_14719__boxed_2134_; uint8_t v___x_14720__boxed_2135_; uint8_t v_____do__lift_14721__boxed_2136_; lean_object* v_res_2137_; 
v___x_14719__boxed_2134_ = lean_unbox(v___x_2124_);
v___x_14720__boxed_2135_ = lean_unbox(v___x_2125_);
v_____do__lift_14721__boxed_2136_ = lean_unbox(v_____do__lift_2126_);
v_res_2137_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_14719__boxed_2134_, v___x_14720__boxed_2135_, v_____do__lift_14721__boxed_2136_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(uint8_t v___x_2138_, uint8_t v___x_2139_, lean_object* v_as_2140_, size_t v_i_2141_, size_t v_stop_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_usize_dec_eq(v_i_2141_, v_stop_2142_);
if (v___x_2148_ == 0)
{
uint8_t v___x_2149_; uint8_t v_a_2151_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2149_ = 1;
v___x_2157_ = lean_array_uget_borrowed(v_as_2140_, v_i_2141_);
lean_inc(v___x_2157_);
v___x_2158_ = l_Lean_Meta_isProof(v___x_2157_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; uint8_t v___x_2160_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2158_, 1);
v___x_2160_ = lean_unbox(v_a_2159_);
lean_dec(v_a_2159_);
if (v___x_2160_ == 0)
{
v_a_2151_ = v___x_2138_;
goto v___jp_2150_;
}
else
{
v_a_2151_ = v___x_2139_;
goto v___jp_2150_;
}
}
else
{
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2161_; uint8_t v___x_2162_; 
v_a_2161_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2158_, 1);
v___x_2162_ = lean_unbox(v_a_2161_);
lean_dec(v_a_2161_);
v_a_2151_ = v___x_2162_;
goto v___jp_2150_;
}
else
{
return v___x_2158_;
}
}
v___jp_2150_:
{
if (v_a_2151_ == 0)
{
size_t v___x_2152_; size_t v___x_2153_; 
v___x_2152_ = ((size_t)1ULL);
v___x_2153_ = lean_usize_add(v_i_2141_, v___x_2152_);
v_i_2141_ = v___x_2153_;
goto _start;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_box(v___x_2149_);
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
return v___x_2156_;
}
}
}
else
{
uint8_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = 0;
v___x_2164_ = lean_box(v___x_2163_);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v___x_2166_, lean_object* v___x_2167_, lean_object* v_as_2168_, lean_object* v_i_2169_, lean_object* v_stop_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
uint8_t v___x_14757__boxed_2176_; uint8_t v___x_14758__boxed_2177_; size_t v_i_boxed_2178_; size_t v_stop_boxed_2179_; lean_object* v_res_2180_; 
v___x_14757__boxed_2176_ = lean_unbox(v___x_2166_);
v___x_14758__boxed_2177_ = lean_unbox(v___x_2167_);
v_i_boxed_2178_ = lean_unbox_usize(v_i_2169_);
lean_dec(v_i_2169_);
v_stop_boxed_2179_ = lean_unbox_usize(v_stop_2170_);
lean_dec(v_stop_2170_);
v_res_2180_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_14757__boxed_2176_, v___x_14758__boxed_2177_, v_as_2168_, v_i_boxed_2178_, v_stop_boxed_2179_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec_ref(v_as_2168_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_p_2181_, lean_object* v_term_2182_, lean_object* v___x_2183_, uint8_t v___x_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_toCold_2192_; lean_object* v_currRecDepth_2193_; lean_object* v_ref_2194_; uint16_t v_optionFlags_2195_; uint8_t v_suppressElabErrors_2196_; uint8_t v_isRecordingDeps_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2294_; 
v_toCold_2192_ = lean_ctor_get(v___y_2189_, 0);
v_currRecDepth_2193_ = lean_ctor_get(v___y_2189_, 1);
v_ref_2194_ = lean_ctor_get(v___y_2189_, 2);
v_optionFlags_2195_ = lean_ctor_get_uint16(v___y_2189_, sizeof(void*)*3);
v_suppressElabErrors_2196_ = lean_ctor_get_uint8(v___y_2189_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2197_ = lean_ctor_get_uint8(v___y_2189_, sizeof(void*)*3 + 3);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___y_2189_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2199_ = v___y_2189_;
v_isShared_2200_ = v_isSharedCheck_2294_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_ref_2194_);
lean_inc(v_currRecDepth_2193_);
lean_inc(v_toCold_2192_);
lean_dec(v___y_2189_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2294_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v_ref_2201_; lean_object* v___x_2203_; 
v_ref_2201_ = l_Lean_replaceRef(v_p_2181_, v_ref_2194_);
lean_dec(v_ref_2194_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 2, v_ref_2201_);
v___x_2203_ = v___x_2199_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_toCold_2192_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_currRecDepth_2193_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_ref_2201_);
lean_ctor_set_uint16(v_reuseFailAlloc_2293_, sizeof(void*)*3, v_optionFlags_2195_);
lean_ctor_set_uint8(v_reuseFailAlloc_2293_, sizeof(void*)*3 + 2, v_suppressElabErrors_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2293_, sizeof(void*)*3 + 3, v_isRecordingDeps_2197_);
v___x_2203_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Elab_Term_elabTerm(v_term_2182_, v___x_2183_, v___x_2184_, v___x_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___x_2203_, v___y_2190_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2204_, 1);
v___x_2206_ = 1;
v___x_2207_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_2206_, v___x_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___x_2203_, v___y_2190_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v___x_2208_; lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref_known(v___x_2207_, 1);
v___x_2208_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_2205_, v___y_2188_);
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2211_ = v___x_2208_;
v_isShared_2212_ = v_isSharedCheck_2276_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2276_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
uint8_t v___x_2213_; 
v___x_2213_ = l_Lean_Expr_hasSyntheticSorry(v_a_2209_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = l_Lean_Expr_eta(v_a_2209_);
v___x_2215_ = l_Lean_Expr_hasMVar(v___x_2214_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; 
lean_dec_ref(v___x_2203_);
v___x_2216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__0));
v___x_2217_ = lean_box(v___x_2215_);
v___x_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2214_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2216_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2220_);
v___x_2222_ = v___x_2211_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
else
{
lean_object* v___x_2224_; 
lean_del_object(v___x_2211_);
v___x_2224_ = l_Lean_Meta_abstractMVars(v___x_2214_, v___x_2184_, v___y_2187_, v___y_2188_, v___x_2203_, v___y_2190_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2263_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2263_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2263_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v_paramNames_2229_; lean_object* v_mvars_2230_; lean_object* v_expr_2231_; uint8_t v_a_2233_; lean_object* v___y_2242_; lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
v_paramNames_2229_ = lean_ctor_get(v_a_2225_, 0);
lean_inc_ref(v_paramNames_2229_);
v_mvars_2230_ = lean_ctor_get(v_a_2225_, 1);
lean_inc_ref(v_mvars_2230_);
v_expr_2231_ = lean_ctor_get(v_a_2225_, 2);
lean_inc_ref(v_expr_2231_);
lean_dec(v_a_2225_);
v___x_2253_ = lean_unsigned_to_nat(0u);
v___x_2254_ = lean_array_get_size(v_mvars_2230_);
v___x_2255_ = lean_nat_dec_lt(v___x_2253_, v___x_2254_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; 
lean_dec_ref(v_mvars_2230_);
v___x_2256_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2215_, v___x_2213_, v___x_2255_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___x_2203_, v___y_2190_);
lean_dec_ref(v___x_2203_);
v___y_2242_ = v___x_2256_;
goto v___jp_2241_;
}
else
{
if (v___x_2255_ == 0)
{
lean_dec_ref(v_mvars_2230_);
lean_dec_ref(v___x_2203_);
v_a_2233_ = v___x_2215_;
goto v___jp_2232_;
}
else
{
size_t v___x_2257_; size_t v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = ((size_t)0ULL);
v___x_2258_ = lean_usize_of_nat(v___x_2254_);
v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2215_, v___x_2213_, v_mvars_2230_, v___x_2257_, v___x_2258_, v___y_2187_, v___y_2188_, v___x_2203_, v___y_2190_);
lean_dec_ref(v_mvars_2230_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; uint8_t v___x_2261_; lean_object* v___x_2262_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v___x_2259_, 1);
v___x_2261_ = lean_unbox(v_a_2260_);
lean_dec(v_a_2260_);
v___x_2262_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v___x_2215_, v___x_2213_, v___x_2261_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___x_2203_, v___y_2190_);
lean_dec_ref(v___x_2203_);
v___y_2242_ = v___x_2262_;
goto v___jp_2241_;
}
else
{
lean_dec_ref(v___x_2203_);
v___y_2242_ = v___x_2259_;
goto v___jp_2241_;
}
}
}
v___jp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2234_ = lean_box(v_a_2233_);
v___x_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2235_, 0, v_expr_2231_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2236_, 0, v_paramNames_2229_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
v___x_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2237_);
v___x_2239_ = v___x_2227_;
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
v___jp_2241_:
{
if (lean_obj_tag(v___y_2242_) == 0)
{
lean_object* v_a_2243_; uint8_t v___x_2244_; 
v_a_2243_ = lean_ctor_get(v___y_2242_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v___y_2242_, 1);
v___x_2244_ = lean_unbox(v_a_2243_);
lean_dec(v_a_2243_);
v_a_2233_ = v___x_2244_;
goto v___jp_2232_;
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec_ref(v_expr_2231_);
lean_dec_ref(v_paramNames_2229_);
lean_del_object(v___x_2227_);
v_a_2245_ = lean_ctor_get(v___y_2242_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___y_2242_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___y_2242_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___y_2242_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec_ref(v___x_2203_);
v_a_2264_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2224_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2224_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_dec(v_a_2209_);
lean_dec_ref(v___x_2203_);
v___x_2272_ = lean_box(0);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2272_);
v___x_2274_ = v___x_2211_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v_a_2205_);
lean_dec_ref(v___x_2203_);
v_a_2277_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2207_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2207_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec_ref(v___x_2203_);
v_a_2285_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2204_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2204_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_p_2295_, lean_object* v_term_2296_, lean_object* v___x_2297_, lean_object* v___x_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
uint8_t v___x_14818__boxed_2306_; lean_object* v_res_2307_; 
v___x_14818__boxed_2306_ = lean_unbox(v___x_2298_);
v_res_2307_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_p_2295_, v_term_2296_, v___x_2297_, v___x_14818__boxed_2306_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v_p_2295_);
return v_res_2307_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__2));
v___x_2313_ = l_Lean_stringToMessageData(v___x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(lean_object* v_params_2314_, lean_object* v_p_2315_, lean_object* v_fst_2316_, lean_object* v_fst_2317_, uint8_t v___x_2318_, uint8_t v_minIndexable_2319_, lean_object* v_kind_2320_, lean_object* v_idx_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_symPrios_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; 
v_symPrios_2327_ = lean_ctor_get(v_params_2314_, 5);
lean_inc_ref(v_symPrios_2327_);
lean_dec_ref(v_params_2314_);
v___x_2328_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__1));
v___x_2329_ = lean_name_append_index_after(v___x_2328_, v_idx_2321_);
v___x_2330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
lean_ctor_set(v___x_2330_, 1, v_p_2315_);
v___x_2331_ = 0;
v___x_2332_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2330_, v_fst_2316_, v_fst_2317_, v_kind_2320_, v_symPrios_2327_, v___x_2318_, v___x_2331_, v_minIndexable_2319_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2343_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2343_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2343_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
if (lean_obj_tag(v_a_2333_) == 1)
{
lean_object* v_val_2337_; lean_object* v___x_2339_; 
v_val_2337_ = lean_ctor_get(v_a_2333_, 0);
lean_inc(v_val_2337_);
lean_dec_ref_known(v_a_2333_, 1);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v_val_2337_);
v___x_2339_ = v___x_2335_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_val_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
else
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_del_object(v___x_2335_);
lean_dec(v_a_2333_);
v___x_2341_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___closed__3);
v___x_2342_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2341_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v___x_2342_;
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
v_a_2344_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2332_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2332_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed(lean_object* v_params_2352_, lean_object* v_p_2353_, lean_object* v_fst_2354_, lean_object* v_fst_2355_, lean_object* v___x_2356_, lean_object* v_minIndexable_2357_, lean_object* v_kind_2358_, lean_object* v_idx_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
uint8_t v___x_15048__boxed_2365_; uint8_t v_minIndexable_boxed_2366_; lean_object* v_res_2367_; 
v___x_15048__boxed_2365_ = lean_unbox(v___x_2356_);
v_minIndexable_boxed_2366_ = lean_unbox(v_minIndexable_2357_);
v_res_2367_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2(v_params_2352_, v_p_2353_, v_fst_2354_, v_fst_2355_, v___x_15048__boxed_2365_, v_minIndexable_boxed_2366_, v_kind_2358_, v_idx_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2367_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_box(1);
v___x_2369_ = l_Lean_MessageData_ofFormat(v___x_2368_);
return v___x_2369_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__2));
v___x_2374_ = l_Lean_MessageData_ofFormat(v___x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(lean_object* v_x_2375_, lean_object* v_x_2376_){
_start:
{
if (lean_obj_tag(v_x_2376_) == 0)
{
return v_x_2375_;
}
else
{
lean_object* v_head_2377_; lean_object* v_tail_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2400_; 
v_head_2377_ = lean_ctor_get(v_x_2376_, 0);
v_tail_2378_ = lean_ctor_get(v_x_2376_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_x_2376_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2380_ = v_x_2376_;
v_isShared_2381_ = v_isSharedCheck_2400_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_tail_2378_);
lean_inc(v_head_2377_);
lean_dec(v_x_2376_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2400_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v_before_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2398_; 
v_before_2382_ = lean_ctor_get(v_head_2377_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_head_2377_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v_head_2377_, 1);
lean_dec(v_unused_2399_);
v___x_2384_ = v_head_2377_;
v_isShared_2385_ = v_isSharedCheck_2398_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_before_2382_);
lean_dec(v_head_2377_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2398_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2386_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2385_ == 0)
{
lean_ctor_set_tag(v___x_2384_, 7);
lean_ctor_set(v___x_2384_, 1, v___x_2386_);
lean_ctor_set(v___x_2384_, 0, v_x_2375_);
v___x_2388_ = v___x_2384_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_x_2375_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2389_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__3);
if (v_isShared_2381_ == 0)
{
lean_ctor_set_tag(v___x_2380_, 7);
lean_ctor_set(v___x_2380_, 1, v___x_2389_);
lean_ctor_set(v___x_2380_, 0, v___x_2388_);
v___x_2391_ = v___x_2380_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = l_Lean_MessageData_ofSyntax(v_before_2382_);
v___x_2393_ = l_Lean_indentD(v___x_2392_);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2391_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v_x_2375_ = v___x_2394_;
v_x_2376_ = v_tail_2378_;
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
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__1));
v___x_2405_ = l_Lean_MessageData_ofFormat(v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(lean_object* v_msgData_2406_, lean_object* v_macroStack_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2410_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2408_);
v___x_2411_ = l_Lean_Elab_pp_macroStack;
v___x_2412_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_2410_, v___x_2411_);
lean_dec_ref(v___x_2410_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; 
lean_dec(v_macroStack_2407_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_msgData_2406_);
return v___x_2413_;
}
else
{
if (lean_obj_tag(v_macroStack_2407_) == 0)
{
lean_object* v___x_2414_; 
v___x_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_msgData_2406_);
return v___x_2414_;
}
else
{
lean_object* v_head_2415_; lean_object* v_after_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2431_; 
v_head_2415_ = lean_ctor_get(v_macroStack_2407_, 0);
lean_inc(v_head_2415_);
v_after_2416_ = lean_ctor_get(v_head_2415_, 1);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_head_2415_);
if (v_isSharedCheck_2431_ == 0)
{
lean_object* v_unused_2432_; 
v_unused_2432_ = lean_ctor_get(v_head_2415_, 0);
lean_dec(v_unused_2432_);
v___x_2418_ = v_head_2415_;
v_isShared_2419_ = v_isSharedCheck_2431_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_after_2416_);
lean_dec(v_head_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2431_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3___closed__0);
if (v_isShared_2419_ == 0)
{
lean_ctor_set_tag(v___x_2418_, 7);
lean_ctor_set(v___x_2418_, 1, v___x_2420_);
lean_ctor_set(v___x_2418_, 0, v_msgData_2406_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_msgData_2406_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v_msgData_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2423_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___closed__2);
v___x_2424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = l_Lean_MessageData_ofSyntax(v_after_2416_);
v___x_2426_ = l_Lean_indentD(v___x_2425_);
v_msgData_2427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2427_, 0, v___x_2424_);
lean_ctor_set(v_msgData_2427_, 1, v___x_2426_);
v___x_2428_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2_spec__3(v_msgData_2427_, v_macroStack_2407_);
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
return v___x_2429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg___boxed(lean_object* v_msgData_2433_, lean_object* v_macroStack_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2433_, v_macroStack_2434_, v___y_2435_);
lean_dec_ref(v___y_2435_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(lean_object* v_msg_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_ref_2446_; lean_object* v_macroStack_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v_a_2450_; lean_object* v___x_2451_; lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2460_; 
v_ref_2446_ = lean_ctor_get(v___y_2443_, 2);
v_macroStack_2447_ = lean_ctor_get(v___y_2439_, 1);
v___x_2448_ = l_Lean_Elab_getBetterRef(v_ref_2446_, v_macroStack_2447_);
v___x_2449_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2438_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref(v___x_2449_);
lean_inc(v_macroStack_2447_);
v___x_2451_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_a_2450_, v_macroStack_2447_, v___y_2443_);
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2460_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2460_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v___x_2458_; 
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2448_);
lean_ctor_set(v___x_2456_, 1, v_a_2452_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set_tag(v___x_2454_, 1);
lean_ctor_set(v___x_2454_, 0, v___x_2456_);
v___x_2458_ = v___x_2454_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg___boxed(lean_object* v_msg_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
return v_res_2469_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2472_ = l_Lean_stringToMessageData(v___x_2471_);
return v___x_2472_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2475_ = l_Lean_stringToMessageData(v___x_2474_);
return v___x_2475_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2478_ = l_Lean_stringToMessageData(v___x_2477_);
return v___x_2478_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_2481_ = l_Lean_stringToMessageData(v___x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2482_, lean_object* v_p_2483_, lean_object* v_mod_x3f_2484_, lean_object* v_term_2485_, uint8_t v_minIndexable_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v___y_2495_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; uint8_t v___y_2635_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; uint8_t v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v_kind_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v_toCold_2856_; lean_object* v_currRecDepth_2857_; lean_object* v_ref_2858_; uint16_t v_optionFlags_2859_; uint8_t v_suppressElabErrors_2860_; uint8_t v_isRecordingDeps_2861_; lean_object* v_ref_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_toCold_2856_ = lean_ctor_get(v_a_2491_, 0);
v_currRecDepth_2857_ = lean_ctor_get(v_a_2491_, 1);
v_ref_2858_ = lean_ctor_get(v_a_2491_, 2);
v_optionFlags_2859_ = lean_ctor_get_uint16(v_a_2491_, sizeof(void*)*3);
v_suppressElabErrors_2860_ = lean_ctor_get_uint8(v_a_2491_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2861_ = lean_ctor_get_uint8(v_a_2491_, sizeof(void*)*3 + 3);
v_ref_2862_ = l_Lean_replaceRef(v_p_2483_, v_ref_2858_);
lean_inc(v_currRecDepth_2857_);
lean_inc_ref(v_toCold_2856_);
v___x_2863_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2863_, 0, v_toCold_2856_);
lean_ctor_set(v___x_2863_, 1, v_currRecDepth_2857_);
lean_ctor_set(v___x_2863_, 2, v_ref_2862_);
lean_ctor_set_uint16(v___x_2863_, sizeof(void*)*3, v_optionFlags_2859_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*3 + 2, v_suppressElabErrors_2860_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*3 + 3, v_isRecordingDeps_2861_);
v___x_2864_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2482_, v___x_2863_, v_a_2492_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_dec_ref_known(v___x_2864_, 1);
if (lean_obj_tag(v_mod_x3f_2484_) == 1)
{
lean_object* v_val_2865_; lean_object* v___x_2866_; 
v_val_2865_ = lean_ctor_get(v_mod_x3f_2484_, 0);
lean_inc(v_val_2865_);
v___x_2866_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2865_, v___x_2863_, v_a_2492_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2866_, 1);
switch(lean_obj_tag(v_a_2867_))
{
case 0:
{
lean_object* v_k_2868_; 
v_k_2868_ = lean_ctor_get(v_a_2867_, 0);
lean_inc(v_k_2868_);
lean_dec_ref_known(v_a_2867_, 1);
if (lean_obj_tag(v_k_2868_) == 9)
{
lean_dec_ref_known(v_mod_x3f_2484_, 1);
lean_dec(v_term_2485_);
lean_dec(v_p_2483_);
lean_dec_ref(v_params_2482_);
v___y_2815_ = v_a_2487_;
v___y_2816_ = v_a_2488_;
v___y_2817_ = v_a_2489_;
v___y_2818_ = v_a_2490_;
v___y_2819_ = v___x_2863_;
v___y_2820_ = v_a_2492_;
goto v___jp_2814_;
}
else
{
v_kind_2746_ = v_k_2868_;
v___y_2747_ = v_a_2487_;
v___y_2748_ = v_a_2488_;
v___y_2749_ = v_a_2489_;
v___y_2750_ = v_a_2490_;
v___y_2751_ = v___x_2863_;
v___y_2752_ = v_a_2492_;
goto v___jp_2745_;
}
}
case 1:
{
lean_dec_ref_known(v_a_2867_, 0);
lean_dec_ref_known(v_mod_x3f_2484_, 1);
lean_dec(v_term_2485_);
lean_dec(v_p_2483_);
lean_dec_ref(v_params_2482_);
v___y_2832_ = v_a_2487_;
v___y_2833_ = v_a_2488_;
v___y_2834_ = v_a_2489_;
v___y_2835_ = v_a_2490_;
v___y_2836_ = v___x_2863_;
v___y_2837_ = v_a_2492_;
goto v___jp_2831_;
}
case 3:
{
v___y_2849_ = v_a_2487_;
v___y_2850_ = v_a_2488_;
v___y_2851_ = v_a_2489_;
v___y_2852_ = v_a_2490_;
v___y_2853_ = v___x_2863_;
v___y_2854_ = v_a_2492_;
goto v___jp_2848_;
}
case 5:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec_ref_known(v_a_2867_, 1);
lean_dec_ref_known(v_mod_x3f_2484_, 1);
lean_dec(v_term_2485_);
lean_dec(v_p_2483_);
lean_dec_ref(v_params_2482_);
v___x_2869_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2870_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2869_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v___x_2863_, v_a_2492_);
lean_dec_ref_known(v___x_2863_, 3);
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2870_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2870_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
case 8:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec_ref_known(v_a_2867_, 0);
lean_dec_ref_known(v_mod_x3f_2484_, 1);
lean_dec(v_term_2485_);
lean_dec(v_p_2483_);
lean_dec_ref(v_params_2482_);
v___x_2879_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2880_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2879_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v___x_2863_, v_a_2492_);
lean_dec_ref_known(v___x_2863_, 3);
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2880_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2880_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
case 10:
{
lean_dec_ref_known(v_a_2867_, 0);
lean_dec_ref_known(v_mod_x3f_2484_, 1);
lean_dec(v_term_2485_);
lean_dec(v_p_2483_);
lean_dec_ref(v_params_2482_);
v___y_2832_ = v_a_2487_;
v___y_2833_ = v_a_2488_;
v___y_2834_ = v_a_2489_;
v___y_2835_ = v_a_2490_;
v___y_2836_ = v___x_2863_;
v___y_2837_ = v_a_2492_;
goto v___jp_2831_;
}
default: 
{
lean_dec(v_a_2867_);
lean_dec_ref_known(v_mod_x3f_2484_, 1);
lean_dec(v_term_2485_);
lean_dec(v_p_2483_);
lean_dec_ref(v_params_2482_);
v___y_2815_ = v_a_2487_;
v___y_2816_ = v_a_2488_;
v___y_2817_ = v_a_2489_;
v___y_2818_ = v_a_2490_;
v___y_2819_ = v___x_2863_;
v___y_2820_ = v_a_2492_;
goto v___jp_2814_;
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec_ref_known(v_mod_x3f_2484_, 1);
lean_dec_ref_known(v___x_2863_, 3);
lean_dec(v_term_2485_);
lean_dec(v_p_2483_);
lean_dec_ref(v_params_2482_);
v_a_2889_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2866_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2866_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
else
{
v___y_2849_ = v_a_2487_;
v___y_2850_ = v_a_2488_;
v___y_2851_ = v_a_2489_;
v___y_2852_ = v_a_2490_;
v___y_2853_ = v___x_2863_;
v___y_2854_ = v_a_2492_;
goto v___jp_2848_;
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref_known(v___x_2863_, 3);
lean_dec(v_term_2485_);
lean_dec(v_mod_x3f_2484_);
lean_dec(v_p_2483_);
lean_dec_ref(v_params_2482_);
v_a_2897_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2864_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2864_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
v___jp_2494_:
{
lean_object* v_config_2496_; lean_object* v_extensions_2497_; lean_object* v_extra_2498_; lean_object* v_extraInj_2499_; lean_object* v_extraFacts_2500_; lean_object* v_symPrios_2501_; lean_object* v_norm_2502_; lean_object* v_normProcs_2503_; lean_object* v_anchorRefs_x3f_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2513_; 
v_config_2496_ = lean_ctor_get(v_params_2482_, 0);
v_extensions_2497_ = lean_ctor_get(v_params_2482_, 1);
v_extra_2498_ = lean_ctor_get(v_params_2482_, 2);
v_extraInj_2499_ = lean_ctor_get(v_params_2482_, 3);
v_extraFacts_2500_ = lean_ctor_get(v_params_2482_, 4);
v_symPrios_2501_ = lean_ctor_get(v_params_2482_, 5);
v_norm_2502_ = lean_ctor_get(v_params_2482_, 6);
v_normProcs_2503_ = lean_ctor_get(v_params_2482_, 7);
v_anchorRefs_x3f_2504_ = lean_ctor_get(v_params_2482_, 8);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_params_2482_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2506_ = v_params_2482_;
v_isShared_2507_ = v_isSharedCheck_2513_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_anchorRefs_x3f_2504_);
lean_inc(v_normProcs_2503_);
lean_inc(v_norm_2502_);
lean_inc(v_symPrios_2501_);
lean_inc(v_extraFacts_2500_);
lean_inc(v_extraInj_2499_);
lean_inc(v_extra_2498_);
lean_inc(v_extensions_2497_);
lean_inc(v_config_2496_);
lean_dec(v_params_2482_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2513_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2508_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2500_, v___y_2495_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 4, v___x_2508_);
v___x_2510_ = v___x_2506_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_config_2496_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_extensions_2497_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_extra_2498_);
lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_extraInj_2499_);
lean_ctor_set(v_reuseFailAlloc_2512_, 4, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2512_, 5, v_symPrios_2501_);
lean_ctor_set(v_reuseFailAlloc_2512_, 6, v_norm_2502_);
lean_ctor_set(v_reuseFailAlloc_2512_, 7, v_normProcs_2503_);
lean_ctor_set(v_reuseFailAlloc_2512_, 8, v_anchorRefs_x3f_2504_);
v___x_2510_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
return v___x_2511_;
}
}
}
v___jp_2514_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2524_ = lean_array_get_size(v___y_2516_);
lean_dec_ref(v___y_2516_);
v___x_2525_ = lean_unsigned_to_nat(0u);
v___x_2526_ = lean_nat_dec_eq(v___x_2524_, v___x_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v___y_2515_);
lean_dec_ref(v_params_2482_);
v___x_2527_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2528_ = l_Lean_indentExpr(v___y_2517_);
v___x_2529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2529_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec_ref(v___y_2522_);
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
else
{
lean_dec_ref(v___y_2522_);
lean_dec_ref(v___y_2517_);
v___y_2495_ = v___y_2515_;
goto v___jp_2494_;
}
}
v___jp_2539_:
{
if (lean_obj_tag(v_mod_x3f_2484_) == 0)
{
v___y_2515_ = v___y_2542_;
v___y_2516_ = v___y_2543_;
v___y_2517_ = v___y_2545_;
v___y_2518_ = v___y_2547_;
v___y_2519_ = v___y_2548_;
v___y_2520_ = v___y_2544_;
v___y_2521_ = v___y_2541_;
v___y_2522_ = v___y_2540_;
v___y_2523_ = v___y_2546_;
goto v___jp_2514_;
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref_known(v_mod_x3f_2484_, 1);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec_ref(v_params_2482_);
v___x_2549_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2550_ = l_Lean_indentExpr(v___y_2545_);
v___x_2551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2551_, v___y_2547_, v___y_2548_, v___y_2544_, v___y_2541_, v___y_2540_, v___y_2546_);
lean_dec_ref(v___y_2540_);
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
v___jp_2561_:
{
lean_object* v___x_2578_; 
lean_inc(v___y_2577_);
lean_inc(v___y_2575_);
lean_inc_ref(v___y_2574_);
v___x_2578_ = lean_apply_7(v___y_2567_, v___y_2562_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, lean_box(0));
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2588_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2588_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2588_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2583_ = l_Lean_PersistentArray_push___redArg(v___y_2569_, v_a_2579_);
v___x_2584_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2584_, 0, v___y_2568_);
lean_ctor_set(v___x_2584_, 1, v___y_2571_);
lean_ctor_set(v___x_2584_, 2, v___x_2583_);
lean_ctor_set(v___x_2584_, 3, v___y_2564_);
lean_ctor_set(v___x_2584_, 4, v___y_2563_);
lean_ctor_set(v___x_2584_, 5, v___y_2566_);
lean_ctor_set(v___x_2584_, 6, v___y_2570_);
lean_ctor_set(v___x_2584_, 7, v___y_2565_);
lean_ctor_set(v___x_2584_, 8, v___y_2572_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2584_);
v___x_2586_ = v___x_2581_;
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
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v___y_2563_);
v_a_2589_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2578_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2578_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
v___jp_2597_:
{
lean_object* v___x_2614_; 
v___x_2614_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2486_, v___y_2611_, v___y_2599_, v___y_2598_, v___y_2613_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_dec_ref_known(v___x_2614_, 1);
v___y_2562_ = v___y_2602_;
v___y_2563_ = v___y_2603_;
v___y_2564_ = v___y_2604_;
v___y_2565_ = v___y_2605_;
v___y_2566_ = v___y_2606_;
v___y_2567_ = v___y_2607_;
v___y_2568_ = v___y_2608_;
v___y_2569_ = v___y_2600_;
v___y_2570_ = v___y_2610_;
v___y_2571_ = v___y_2609_;
v___y_2572_ = v___y_2612_;
v___y_2573_ = v___y_2601_;
v___y_2574_ = v___y_2611_;
v___y_2575_ = v___y_2599_;
v___y_2576_ = v___y_2598_;
v___y_2577_ = v___y_2613_;
goto v___jp_2561_;
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec_ref(v___y_2598_);
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
v___jp_2623_:
{
if (v___y_2635_ == 0)
{
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2625_);
v___y_2540_ = v___y_2624_;
v___y_2541_ = v___y_2626_;
v___y_2542_ = v___y_2627_;
v___y_2543_ = v___y_2629_;
v___y_2544_ = v___y_2630_;
v___y_2545_ = v___y_2633_;
v___y_2546_ = v___y_2632_;
v___y_2547_ = v___y_2631_;
v___y_2548_ = v___y_2634_;
goto v___jp_2539_;
}
else
{
lean_object* v_extra_2636_; 
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___y_2629_);
lean_dec_ref(v___y_2627_);
lean_dec(v_mod_x3f_2484_);
v_extra_2636_ = lean_ctor_get(v_params_2482_, 2);
lean_inc_ref(v_extra_2636_);
if (lean_obj_tag(v___y_2625_) == 2)
{
lean_object* v_config_2637_; lean_object* v_extensions_2638_; lean_object* v_extraInj_2639_; lean_object* v_extraFacts_2640_; lean_object* v_symPrios_2641_; lean_object* v_norm_2642_; lean_object* v_normProcs_2643_; lean_object* v_anchorRefs_x3f_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2699_; 
v_config_2637_ = lean_ctor_get(v_params_2482_, 0);
v_extensions_2638_ = lean_ctor_get(v_params_2482_, 1);
v_extraInj_2639_ = lean_ctor_get(v_params_2482_, 3);
v_extraFacts_2640_ = lean_ctor_get(v_params_2482_, 4);
v_symPrios_2641_ = lean_ctor_get(v_params_2482_, 5);
v_norm_2642_ = lean_ctor_get(v_params_2482_, 6);
v_normProcs_2643_ = lean_ctor_get(v_params_2482_, 7);
v_anchorRefs_x3f_2644_ = lean_ctor_get(v_params_2482_, 8);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_params_2482_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v_params_2482_, 2);
lean_dec(v_unused_2700_);
v___x_2646_ = v_params_2482_;
v_isShared_2647_ = v_isSharedCheck_2699_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_anchorRefs_x3f_2644_);
lean_inc(v_normProcs_2643_);
lean_inc(v_norm_2642_);
lean_inc(v_symPrios_2641_);
lean_inc(v_extraFacts_2640_);
lean_inc(v_extraInj_2639_);
lean_inc(v_extensions_2638_);
lean_inc(v_config_2637_);
lean_dec(v_params_2482_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2699_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v_size_2648_; uint8_t v_gen_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2698_; 
v_size_2648_ = lean_ctor_get(v_extra_2636_, 2);
v_gen_2649_ = lean_ctor_get_uint8(v___y_2625_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___y_2625_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2651_ = v___y_2625_;
v_isShared_2652_ = v_isSharedCheck_2698_;
goto v_resetjp_2650_;
}
else
{
lean_dec(v___y_2625_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2698_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; 
v___x_2653_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2486_, v___y_2630_, v___y_2626_, v___y_2624_, v___y_2632_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v___x_2655_; 
lean_dec_ref_known(v___x_2653_, 1);
if (v_isShared_2652_ == 0)
{
lean_ctor_set_tag(v___x_2651_, 0);
v___x_2655_ = v___x_2651_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2689_, 0, v_gen_2649_);
v___x_2655_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2656_; 
lean_inc_ref(v___y_2628_);
lean_inc(v___y_2632_);
lean_inc_ref(v___y_2624_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2630_);
lean_inc(v_size_2648_);
v___x_2656_ = lean_apply_7(v___y_2628_, v___x_2655_, v_size_2648_, v___y_2630_, v___y_2626_, v___y_2624_, v___y_2632_, lean_box(0));
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2658_, 0, v_gen_2649_);
lean_inc(v___y_2632_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2630_);
lean_inc(v_size_2648_);
v___x_2659_ = lean_apply_7(v___y_2628_, v___x_2658_, v_size_2648_, v___y_2630_, v___y_2626_, v___y_2624_, v___y_2632_, lean_box(0));
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2672_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2672_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2672_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2664_ = l_Lean_PersistentArray_push___redArg(v_extra_2636_, v_a_2657_);
v___x_2665_ = l_Lean_PersistentArray_push___redArg(v___x_2664_, v_a_2660_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 2, v___x_2665_);
v___x_2667_ = v___x_2646_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_config_2637_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_extensions_2638_);
lean_ctor_set(v_reuseFailAlloc_2671_, 2, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2671_, 3, v_extraInj_2639_);
lean_ctor_set(v_reuseFailAlloc_2671_, 4, v_extraFacts_2640_);
lean_ctor_set(v_reuseFailAlloc_2671_, 5, v_symPrios_2641_);
lean_ctor_set(v_reuseFailAlloc_2671_, 6, v_norm_2642_);
lean_ctor_set(v_reuseFailAlloc_2671_, 7, v_normProcs_2643_);
lean_ctor_set(v_reuseFailAlloc_2671_, 8, v_anchorRefs_x3f_2644_);
v___x_2667_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2669_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2667_);
v___x_2669_ = v___x_2662_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec(v_a_2657_);
lean_del_object(v___x_2646_);
lean_dec(v_anchorRefs_x3f_2644_);
lean_dec_ref(v_normProcs_2643_);
lean_dec_ref(v_norm_2642_);
lean_dec_ref(v_symPrios_2641_);
lean_dec_ref(v_extraFacts_2640_);
lean_dec_ref(v_extraInj_2639_);
lean_dec_ref(v_extensions_2638_);
lean_dec_ref(v_config_2637_);
lean_dec_ref(v_extra_2636_);
v_a_2673_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2659_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2659_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_del_object(v___x_2646_);
lean_dec(v_anchorRefs_x3f_2644_);
lean_dec_ref(v_normProcs_2643_);
lean_dec_ref(v_norm_2642_);
lean_dec_ref(v_symPrios_2641_);
lean_dec_ref(v_extraFacts_2640_);
lean_dec_ref(v_extraInj_2639_);
lean_dec_ref(v_extensions_2638_);
lean_dec_ref(v_config_2637_);
lean_dec_ref(v_extra_2636_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___y_2624_);
v_a_2681_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2656_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2656_);
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
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_del_object(v___x_2651_);
lean_del_object(v___x_2646_);
lean_dec(v_anchorRefs_x3f_2644_);
lean_dec_ref(v_normProcs_2643_);
lean_dec_ref(v_norm_2642_);
lean_dec_ref(v_symPrios_2641_);
lean_dec_ref(v_extraFacts_2640_);
lean_dec_ref(v_extraInj_2639_);
lean_dec_ref(v_extensions_2638_);
lean_dec_ref(v_config_2637_);
lean_dec_ref(v_extra_2636_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___y_2624_);
v_a_2690_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2653_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2653_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
}
else
{
switch(lean_obj_tag(v___y_2625_))
{
case 0:
{
lean_object* v_config_2701_; lean_object* v_extensions_2702_; lean_object* v_extraInj_2703_; lean_object* v_extraFacts_2704_; lean_object* v_symPrios_2705_; lean_object* v_norm_2706_; lean_object* v_normProcs_2707_; lean_object* v_anchorRefs_x3f_2708_; lean_object* v_size_2709_; 
v_config_2701_ = lean_ctor_get(v_params_2482_, 0);
lean_inc_ref(v_config_2701_);
v_extensions_2702_ = lean_ctor_get(v_params_2482_, 1);
lean_inc_ref(v_extensions_2702_);
v_extraInj_2703_ = lean_ctor_get(v_params_2482_, 3);
lean_inc_ref(v_extraInj_2703_);
v_extraFacts_2704_ = lean_ctor_get(v_params_2482_, 4);
lean_inc_ref(v_extraFacts_2704_);
v_symPrios_2705_ = lean_ctor_get(v_params_2482_, 5);
lean_inc_ref(v_symPrios_2705_);
v_norm_2706_ = lean_ctor_get(v_params_2482_, 6);
lean_inc_ref(v_norm_2706_);
v_normProcs_2707_ = lean_ctor_get(v_params_2482_, 7);
lean_inc_ref(v_normProcs_2707_);
v_anchorRefs_x3f_2708_ = lean_ctor_get(v_params_2482_, 8);
lean_inc(v_anchorRefs_x3f_2708_);
lean_dec_ref(v_params_2482_);
v_size_2709_ = lean_ctor_get(v_extra_2636_, 2);
lean_inc(v_size_2709_);
v___y_2598_ = v___y_2624_;
v___y_2599_ = v___y_2626_;
v___y_2600_ = v_extra_2636_;
v___y_2601_ = v_size_2709_;
v___y_2602_ = v___y_2625_;
v___y_2603_ = v_extraFacts_2704_;
v___y_2604_ = v_extraInj_2703_;
v___y_2605_ = v_normProcs_2707_;
v___y_2606_ = v_symPrios_2705_;
v___y_2607_ = v___y_2628_;
v___y_2608_ = v_config_2701_;
v___y_2609_ = v_extensions_2702_;
v___y_2610_ = v_norm_2706_;
v___y_2611_ = v___y_2630_;
v___y_2612_ = v_anchorRefs_x3f_2708_;
v___y_2613_ = v___y_2632_;
goto v___jp_2597_;
}
case 1:
{
lean_object* v_config_2710_; lean_object* v_extensions_2711_; lean_object* v_extraInj_2712_; lean_object* v_extraFacts_2713_; lean_object* v_symPrios_2714_; lean_object* v_norm_2715_; lean_object* v_normProcs_2716_; lean_object* v_anchorRefs_x3f_2717_; lean_object* v_size_2718_; 
v_config_2710_ = lean_ctor_get(v_params_2482_, 0);
lean_inc_ref(v_config_2710_);
v_extensions_2711_ = lean_ctor_get(v_params_2482_, 1);
lean_inc_ref(v_extensions_2711_);
v_extraInj_2712_ = lean_ctor_get(v_params_2482_, 3);
lean_inc_ref(v_extraInj_2712_);
v_extraFacts_2713_ = lean_ctor_get(v_params_2482_, 4);
lean_inc_ref(v_extraFacts_2713_);
v_symPrios_2714_ = lean_ctor_get(v_params_2482_, 5);
lean_inc_ref(v_symPrios_2714_);
v_norm_2715_ = lean_ctor_get(v_params_2482_, 6);
lean_inc_ref(v_norm_2715_);
v_normProcs_2716_ = lean_ctor_get(v_params_2482_, 7);
lean_inc_ref(v_normProcs_2716_);
v_anchorRefs_x3f_2717_ = lean_ctor_get(v_params_2482_, 8);
lean_inc(v_anchorRefs_x3f_2717_);
lean_dec_ref(v_params_2482_);
v_size_2718_ = lean_ctor_get(v_extra_2636_, 2);
lean_inc(v_size_2718_);
v___y_2598_ = v___y_2624_;
v___y_2599_ = v___y_2626_;
v___y_2600_ = v_extra_2636_;
v___y_2601_ = v_size_2718_;
v___y_2602_ = v___y_2625_;
v___y_2603_ = v_extraFacts_2713_;
v___y_2604_ = v_extraInj_2712_;
v___y_2605_ = v_normProcs_2716_;
v___y_2606_ = v_symPrios_2714_;
v___y_2607_ = v___y_2628_;
v___y_2608_ = v_config_2710_;
v___y_2609_ = v_extensions_2711_;
v___y_2610_ = v_norm_2715_;
v___y_2611_ = v___y_2630_;
v___y_2612_ = v_anchorRefs_x3f_2717_;
v___y_2613_ = v___y_2632_;
goto v___jp_2597_;
}
default: 
{
lean_object* v_config_2719_; lean_object* v_extensions_2720_; lean_object* v_extraInj_2721_; lean_object* v_extraFacts_2722_; lean_object* v_symPrios_2723_; lean_object* v_norm_2724_; lean_object* v_normProcs_2725_; lean_object* v_anchorRefs_x3f_2726_; lean_object* v_size_2727_; 
v_config_2719_ = lean_ctor_get(v_params_2482_, 0);
lean_inc_ref(v_config_2719_);
v_extensions_2720_ = lean_ctor_get(v_params_2482_, 1);
lean_inc_ref(v_extensions_2720_);
v_extraInj_2721_ = lean_ctor_get(v_params_2482_, 3);
lean_inc_ref(v_extraInj_2721_);
v_extraFacts_2722_ = lean_ctor_get(v_params_2482_, 4);
lean_inc_ref(v_extraFacts_2722_);
v_symPrios_2723_ = lean_ctor_get(v_params_2482_, 5);
lean_inc_ref(v_symPrios_2723_);
v_norm_2724_ = lean_ctor_get(v_params_2482_, 6);
lean_inc_ref(v_norm_2724_);
v_normProcs_2725_ = lean_ctor_get(v_params_2482_, 7);
lean_inc_ref(v_normProcs_2725_);
v_anchorRefs_x3f_2726_ = lean_ctor_get(v_params_2482_, 8);
lean_inc(v_anchorRefs_x3f_2726_);
lean_dec_ref(v_params_2482_);
v_size_2727_ = lean_ctor_get(v_extra_2636_, 2);
lean_inc(v_size_2727_);
v___y_2562_ = v___y_2625_;
v___y_2563_ = v_extraFacts_2722_;
v___y_2564_ = v_extraInj_2721_;
v___y_2565_ = v_normProcs_2725_;
v___y_2566_ = v_symPrios_2723_;
v___y_2567_ = v___y_2628_;
v___y_2568_ = v_config_2719_;
v___y_2569_ = v_extra_2636_;
v___y_2570_ = v_norm_2724_;
v___y_2571_ = v_extensions_2720_;
v___y_2572_ = v_anchorRefs_x3f_2726_;
v___y_2573_ = v_size_2727_;
v___y_2574_ = v___y_2630_;
v___y_2575_ = v___y_2626_;
v___y_2576_ = v___y_2624_;
v___y_2577_ = v___y_2632_;
goto v___jp_2561_;
}
}
}
}
}
v___jp_2728_:
{
uint8_t v___x_2741_; 
v___x_2741_ = l_Lean_Expr_isForall(v___y_2734_);
if (v___x_2741_ == 0)
{
v___y_2624_ = v___y_2739_;
v___y_2625_ = v___y_2729_;
v___y_2626_ = v___y_2738_;
v___y_2627_ = v___y_2730_;
v___y_2628_ = v___y_2731_;
v___y_2629_ = v___y_2732_;
v___y_2630_ = v___y_2737_;
v___y_2631_ = v___y_2735_;
v___y_2632_ = v___y_2740_;
v___y_2633_ = v___y_2734_;
v___y_2634_ = v___y_2736_;
v___y_2635_ = v___x_2741_;
goto v___jp_2623_;
}
else
{
if (v___y_2733_ == 0)
{
v___y_2624_ = v___y_2739_;
v___y_2625_ = v___y_2729_;
v___y_2626_ = v___y_2738_;
v___y_2627_ = v___y_2730_;
v___y_2628_ = v___y_2731_;
v___y_2629_ = v___y_2732_;
v___y_2630_ = v___y_2737_;
v___y_2631_ = v___y_2735_;
v___y_2632_ = v___y_2740_;
v___y_2633_ = v___y_2734_;
v___y_2634_ = v___y_2736_;
v___y_2635_ = v___x_2741_;
goto v___jp_2623_;
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; 
v___x_2742_ = lean_array_get_size(v___y_2732_);
v___x_2743_ = lean_unsigned_to_nat(0u);
v___x_2744_ = lean_nat_dec_eq(v___x_2742_, v___x_2743_);
if (v___x_2744_ == 0)
{
v___y_2624_ = v___y_2739_;
v___y_2625_ = v___y_2729_;
v___y_2626_ = v___y_2738_;
v___y_2627_ = v___y_2730_;
v___y_2628_ = v___y_2731_;
v___y_2629_ = v___y_2732_;
v___y_2630_ = v___y_2737_;
v___y_2631_ = v___y_2735_;
v___y_2632_ = v___y_2740_;
v___y_2633_ = v___y_2734_;
v___y_2634_ = v___y_2736_;
v___y_2635_ = v___x_2741_;
goto v___jp_2623_;
}
else
{
if (lean_obj_tag(v_mod_x3f_2484_) == 0)
{
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2729_);
v___y_2540_ = v___y_2739_;
v___y_2541_ = v___y_2738_;
v___y_2542_ = v___y_2730_;
v___y_2543_ = v___y_2732_;
v___y_2544_ = v___y_2737_;
v___y_2545_ = v___y_2734_;
v___y_2546_ = v___y_2740_;
v___y_2547_ = v___y_2735_;
v___y_2548_ = v___y_2736_;
goto v___jp_2539_;
}
else
{
v___y_2624_ = v___y_2739_;
v___y_2625_ = v___y_2729_;
v___y_2626_ = v___y_2738_;
v___y_2627_ = v___y_2730_;
v___y_2628_ = v___y_2731_;
v___y_2629_ = v___y_2732_;
v___y_2630_ = v___y_2737_;
v___y_2631_ = v___y_2735_;
v___y_2632_ = v___y_2740_;
v___y_2633_ = v___y_2734_;
v___y_2634_ = v___y_2736_;
v___y_2635_ = v___x_2741_;
goto v___jp_2623_;
}
}
}
}
}
v___jp_2745_:
{
lean_object* v___x_2753_; uint8_t v___x_2754_; lean_object* v___x_2755_; lean_object* v___f_2756_; lean_object* v___x_2757_; 
v___x_2753_ = lean_box(0);
v___x_2754_ = 1;
v___x_2755_ = lean_box(v___x_2754_);
lean_inc(v_p_2483_);
v___f_2756_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2756_, 0, v_p_2483_);
lean_closure_set(v___f_2756_, 1, v_term_2485_);
lean_closure_set(v___f_2756_, 2, v___x_2753_);
lean_closure_set(v___f_2756_, 3, v___x_2755_);
v___x_2757_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2756_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2805_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2805_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2805_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
if (lean_obj_tag(v_a_2758_) == 1)
{
lean_object* v_val_2762_; lean_object* v_snd_2763_; lean_object* v_fst_2764_; lean_object* v_fst_2765_; lean_object* v_snd_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___f_2769_; lean_object* v___x_2770_; 
lean_del_object(v___x_2760_);
v_val_2762_ = lean_ctor_get(v_a_2758_, 0);
lean_inc(v_val_2762_);
lean_dec_ref_known(v_a_2758_, 1);
v_snd_2763_ = lean_ctor_get(v_val_2762_, 1);
lean_inc(v_snd_2763_);
v_fst_2764_ = lean_ctor_get(v_val_2762_, 0);
lean_inc_n(v_fst_2764_, 2);
lean_dec(v_val_2762_);
v_fst_2765_ = lean_ctor_get(v_snd_2763_, 0);
lean_inc_n(v_fst_2765_, 3);
v_snd_2766_ = lean_ctor_get(v_snd_2763_, 1);
lean_inc(v_snd_2766_);
lean_dec(v_snd_2763_);
v___x_2767_ = lean_box(v___x_2754_);
v___x_2768_ = lean_box(v_minIndexable_2486_);
lean_inc_ref(v_params_2482_);
v___f_2769_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__2___boxed), 13, 6);
lean_closure_set(v___f_2769_, 0, v_params_2482_);
lean_closure_set(v___f_2769_, 1, v_p_2483_);
lean_closure_set(v___f_2769_, 2, v_fst_2764_);
lean_closure_set(v___f_2769_, 3, v_fst_2765_);
lean_closure_set(v___f_2769_, 4, v___x_2767_);
lean_closure_set(v___f_2769_, 5, v___x_2768_);
lean_inc(v___y_2752_);
lean_inc_ref(v___y_2751_);
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2749_);
v___x_2770_ = lean_infer_type(v_fst_2765_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2772_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc_n(v_a_2771_, 2);
lean_dec_ref_known(v___x_2770_, 1);
v___x_2772_ = l_Lean_Meta_isProp(v_a_2771_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; uint8_t v___x_2774_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2772_, 1);
v___x_2774_ = lean_unbox(v_a_2773_);
lean_dec(v_a_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v_a_2771_);
lean_dec_ref(v___f_2769_);
lean_dec(v_snd_2766_);
lean_dec(v_fst_2765_);
lean_dec(v_fst_2764_);
lean_dec(v_kind_2746_);
lean_dec(v_mod_x3f_2484_);
lean_dec_ref(v_params_2482_);
v___x_2775_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2776_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2775_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec_ref(v___y_2751_);
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
else
{
uint8_t v___x_2785_; 
v___x_2785_ = lean_unbox(v_snd_2766_);
lean_dec(v_snd_2766_);
v___y_2729_ = v_kind_2746_;
v___y_2730_ = v_fst_2765_;
v___y_2731_ = v___f_2769_;
v___y_2732_ = v_fst_2764_;
v___y_2733_ = v___x_2785_;
v___y_2734_ = v_a_2771_;
v___y_2735_ = v___y_2747_;
v___y_2736_ = v___y_2748_;
v___y_2737_ = v___y_2749_;
v___y_2738_ = v___y_2750_;
v___y_2739_ = v___y_2751_;
v___y_2740_ = v___y_2752_;
goto v___jp_2728_;
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec(v_a_2771_);
lean_dec_ref(v___f_2769_);
lean_dec(v_snd_2766_);
lean_dec(v_fst_2765_);
lean_dec(v_fst_2764_);
lean_dec_ref(v___y_2751_);
lean_dec(v_kind_2746_);
lean_dec(v_mod_x3f_2484_);
lean_dec_ref(v_params_2482_);
v_a_2786_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2772_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2772_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec_ref(v___f_2769_);
lean_dec(v_snd_2766_);
lean_dec(v_fst_2765_);
lean_dec(v_fst_2764_);
lean_dec_ref(v___y_2751_);
lean_dec(v_kind_2746_);
lean_dec(v_mod_x3f_2484_);
lean_dec_ref(v_params_2482_);
v_a_2794_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2770_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2770_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
else
{
lean_object* v___x_2803_; 
lean_dec(v_a_2758_);
lean_dec_ref(v___y_2751_);
lean_dec(v_kind_2746_);
lean_dec(v_mod_x3f_2484_);
lean_dec(v_p_2483_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v_params_2482_);
v___x_2803_ = v___x_2760_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_params_2482_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec_ref(v___y_2751_);
lean_dec(v_kind_2746_);
lean_dec(v_mod_x3f_2484_);
lean_dec(v_p_2483_);
lean_dec_ref(v_params_2482_);
v_a_2806_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2757_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2757_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
v___jp_2814_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
v___x_2821_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2822_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2821_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
lean_dec_ref(v___y_2819_);
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
v___jp_2831_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
v___x_2838_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7);
v___x_2839_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_2838_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec_ref(v___y_2836_);
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
v___jp_2848_:
{
lean_object* v___x_2855_; 
v___x_2855_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_kind_2746_ = v___x_2855_;
v___y_2747_ = v___y_2849_;
v___y_2748_ = v___y_2850_;
v___y_2749_ = v___y_2851_;
v___y_2750_ = v___y_2852_;
v___y_2751_ = v___y_2853_;
v___y_2752_ = v___y_2854_;
goto v___jp_2745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2905_, lean_object* v_p_2906_, lean_object* v_mod_x3f_2907_, lean_object* v_term_2908_, lean_object* v_minIndexable_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
uint8_t v_minIndexable_boxed_2917_; lean_object* v_res_2918_; 
v_minIndexable_boxed_2917_ = lean_unbox(v_minIndexable_2909_);
v_res_2918_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2905_, v_p_2906_, v_mod_x3f_2907_, v_term_2908_, v_minIndexable_boxed_2917_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_);
lean_dec(v_a_2915_);
lean_dec_ref(v_a_2914_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(uint8_t v___x_2919_, uint8_t v___x_2920_, lean_object* v_as_2921_, size_t v_i_2922_, size_t v_stop_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2919_, v___x_2920_, v_as_2921_, v_i_2922_, v_stop_2923_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v___x_2932_, lean_object* v___x_2933_, lean_object* v_as_2934_, lean_object* v_i_2935_, lean_object* v_stop_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
uint8_t v___x_16091__boxed_2944_; uint8_t v___x_16092__boxed_2945_; size_t v_i_boxed_2946_; size_t v_stop_boxed_2947_; lean_object* v_res_2948_; 
v___x_16091__boxed_2944_ = lean_unbox(v___x_2932_);
v___x_16092__boxed_2945_ = lean_unbox(v___x_2933_);
v_i_boxed_2946_ = lean_unbox_usize(v_i_2935_);
lean_dec(v_i_2935_);
v_stop_boxed_2947_ = lean_unbox_usize(v_stop_2936_);
lean_dec(v_stop_2936_);
v_res_2948_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v___x_16091__boxed_2944_, v___x_16092__boxed_2945_, v_as_2934_, v_i_boxed_2946_, v_stop_boxed_2947_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec_ref(v_as_2934_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(lean_object* v_00_u03b1_2949_, lean_object* v_msg_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___boxed(lean_object* v_00_u03b1_2959_, lean_object* v_msg_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2(v_00_u03b1_2959_, v_msg_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(lean_object* v_msgData_2969_, lean_object* v_macroStack_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___redArg(v_msgData_2969_, v_macroStack_2970_, v___y_2975_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2___boxed(lean_object* v_msgData_2979_, lean_object* v_macroStack_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2_spec__2(v_msgData_2979_, v_macroStack_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2989_, lean_object* v_val_2990_, lean_object* v___x_2991_, uint8_t v___y_2992_, lean_object* v_____r_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v___x_3001_; lean_object* v_ext_3002_; lean_object* v_toEnvExtension_3003_; lean_object* v_env_3004_; lean_object* v_config_3005_; lean_object* v_extensions_3006_; lean_object* v_extra_3007_; lean_object* v_extraInj_3008_; lean_object* v_extraFacts_3009_; lean_object* v_symPrios_3010_; lean_object* v_norm_3011_; lean_object* v_normProcs_3012_; lean_object* v_anchorRefs_x3f_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3025_; 
v___x_3001_ = lean_st_ref_get(v___y_2999_);
v_ext_3002_ = lean_ctor_get(v_val_2990_, 1);
v_toEnvExtension_3003_ = lean_ctor_get(v_ext_3002_, 0);
v_env_3004_ = lean_ctor_get(v___x_3001_, 0);
lean_inc_ref(v_env_3004_);
lean_dec(v___x_3001_);
v_config_3005_ = lean_ctor_get(v_params_2989_, 0);
v_extensions_3006_ = lean_ctor_get(v_params_2989_, 1);
v_extra_3007_ = lean_ctor_get(v_params_2989_, 2);
v_extraInj_3008_ = lean_ctor_get(v_params_2989_, 3);
v_extraFacts_3009_ = lean_ctor_get(v_params_2989_, 4);
v_symPrios_3010_ = lean_ctor_get(v_params_2989_, 5);
v_norm_3011_ = lean_ctor_get(v_params_2989_, 6);
v_normProcs_3012_ = lean_ctor_get(v_params_2989_, 7);
v_anchorRefs_x3f_3013_ = lean_ctor_get(v_params_2989_, 8);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_params_2989_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3015_ = v_params_2989_;
v_isShared_3016_ = v_isSharedCheck_3025_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_anchorRefs_x3f_3013_);
lean_inc(v_normProcs_3012_);
lean_inc(v_norm_3011_);
lean_inc(v_symPrios_3010_);
lean_inc(v_extraFacts_3009_);
lean_inc(v_extraInj_3008_);
lean_inc(v_extra_3007_);
lean_inc(v_extensions_3006_);
lean_inc(v_config_3005_);
lean_dec(v_params_2989_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3025_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v_asyncMode_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
v_asyncMode_3017_ = lean_ctor_get(v_toEnvExtension_3003_, 2);
v___x_3018_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2991_, v_val_2990_, v_env_3004_, v_asyncMode_3017_, v___y_2992_);
v___x_3019_ = lean_array_push(v_extensions_3006_, v___x_3018_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 1, v___x_3019_);
v___x_3021_ = v___x_3015_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_config_3005_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3024_, 2, v_extra_3007_);
lean_ctor_set(v_reuseFailAlloc_3024_, 3, v_extraInj_3008_);
lean_ctor_set(v_reuseFailAlloc_3024_, 4, v_extraFacts_3009_);
lean_ctor_set(v_reuseFailAlloc_3024_, 5, v_symPrios_3010_);
lean_ctor_set(v_reuseFailAlloc_3024_, 6, v_norm_3011_);
lean_ctor_set(v_reuseFailAlloc_3024_, 7, v_normProcs_3012_);
lean_ctor_set(v_reuseFailAlloc_3024_, 8, v_anchorRefs_x3f_3013_);
v___x_3021_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
return v___x_3023_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_3026_, lean_object* v_val_3027_, lean_object* v___x_3028_, lean_object* v___y_3029_, lean_object* v_____r_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
uint8_t v___y_31659__boxed_3038_; lean_object* v_res_3039_; 
v___y_31659__boxed_3038_ = lean_unbox(v___y_3029_);
v_res_3039_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3026_, v_val_3027_, v___x_3028_, v___y_31659__boxed_3038_, v_____r_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec_ref(v___x_3028_);
lean_dec_ref(v_val_3027_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_3040_, lean_object* v_id_3041_, uint8_t v_minIndexable_3042_, lean_object* v_as_x27_3043_, lean_object* v_b_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
if (lean_obj_tag(v_as_x27_3043_) == 0)
{
lean_object* v___x_3050_; 
lean_dec(v_id_3041_);
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v_b_3044_);
return v___x_3050_;
}
else
{
lean_object* v_head_3051_; lean_object* v_tail_3052_; lean_object* v_toCold_3053_; lean_object* v_currRecDepth_3054_; lean_object* v_ref_3055_; uint16_t v_optionFlags_3056_; uint8_t v_suppressElabErrors_3057_; uint8_t v_isRecordingDeps_3058_; uint8_t v___x_3059_; lean_object* v___x_3060_; lean_object* v_ref_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_head_3051_ = lean_ctor_get(v_as_x27_3043_, 0);
v_tail_3052_ = lean_ctor_get(v_as_x27_3043_, 1);
v_toCold_3053_ = lean_ctor_get(v___y_3047_, 0);
v_currRecDepth_3054_ = lean_ctor_get(v___y_3047_, 1);
v_ref_3055_ = lean_ctor_get(v___y_3047_, 2);
v_optionFlags_3056_ = lean_ctor_get_uint16(v___y_3047_, sizeof(void*)*3);
v_suppressElabErrors_3057_ = lean_ctor_get_uint8(v___y_3047_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3058_ = lean_ctor_get_uint8(v___y_3047_, sizeof(void*)*3 + 3);
v___x_3059_ = 0;
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_ref_3061_ = l_Lean_replaceRef(v_p_3040_, v_ref_3055_);
lean_inc(v_currRecDepth_3054_);
lean_inc_ref(v_toCold_3053_);
v___x_3062_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3062_, 0, v_toCold_3053_);
lean_ctor_set(v___x_3062_, 1, v_currRecDepth_3054_);
lean_ctor_set(v___x_3062_, 2, v_ref_3061_);
lean_ctor_set_uint16(v___x_3062_, sizeof(void*)*3, v_optionFlags_3056_);
lean_ctor_set_uint8(v___x_3062_, sizeof(void*)*3 + 2, v_suppressElabErrors_3057_);
lean_ctor_set_uint8(v___x_3062_, sizeof(void*)*3 + 3, v_isRecordingDeps_3058_);
lean_inc(v_head_3051_);
lean_inc(v_id_3041_);
v___x_3063_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_3044_, v_id_3041_, v_head_3051_, v___x_3060_, v_minIndexable_3042_, v___x_3059_, v___x_3059_, v___y_3045_, v___y_3046_, v___x_3062_, v___y_3048_);
lean_dec_ref_known(v___x_3062_, 3);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
lean_dec_ref_known(v___x_3063_, 1);
v_as_x27_3043_ = v_tail_3052_;
v_b_3044_ = v_a_3064_;
goto _start;
}
else
{
lean_dec(v_id_3041_);
return v___x_3063_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_3066_, lean_object* v_id_3067_, lean_object* v_minIndexable_3068_, lean_object* v_as_x27_3069_, lean_object* v_b_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
uint8_t v_minIndexable_boxed_3076_; lean_object* v_res_3077_; 
v_minIndexable_boxed_3076_ = lean_unbox(v_minIndexable_3068_);
v_res_3077_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3066_, v_id_3067_, v_minIndexable_boxed_3076_, v_as_x27_3069_, v_b_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v_as_x27_3069_);
lean_dec(v_p_3066_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
if (lean_obj_tag(v_a_3079_) == 0)
{
lean_object* v___x_3081_; 
v___x_3081_ = l_List_reverse___redArg(v_a_3080_);
return v___x_3081_;
}
else
{
lean_object* v_head_3082_; lean_object* v_tail_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3094_; 
v_head_3082_ = lean_ctor_get(v_a_3079_, 0);
v_tail_3083_ = lean_ctor_get(v_a_3079_, 1);
v_isSharedCheck_3094_ = !lean_is_exclusive(v_a_3079_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3085_ = v_a_3079_;
v_isShared_3086_ = v_isSharedCheck_3094_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_tail_3083_);
lean_inc(v_head_3082_);
lean_dec(v_a_3079_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3094_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v_kind_3087_; uint8_t v___x_3088_; 
v_kind_3087_ = lean_ctor_get(v_head_3082_, 6);
v___x_3088_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_3087_, v_k_3078_);
if (v___x_3088_ == 0)
{
lean_del_object(v___x_3085_);
lean_dec(v_head_3082_);
v_a_3079_ = v_tail_3083_;
goto _start;
}
else
{
lean_object* v___x_3091_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 1, v_a_3080_);
v___x_3091_ = v___x_3085_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_head_3082_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_a_3080_);
v___x_3091_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
v_a_3079_ = v_tail_3083_;
v_a_3080_ = v___x_3091_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_3095_, v_a_3096_, v_a_3097_);
lean_dec(v_k_3095_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_3099_, lean_object* v_msg_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v_toCold_3108_; lean_object* v_currRecDepth_3109_; lean_object* v_ref_3110_; uint16_t v_optionFlags_3111_; uint8_t v_suppressElabErrors_3112_; uint8_t v_isRecordingDeps_3113_; lean_object* v_ref_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v_toCold_3108_ = lean_ctor_get(v___y_3105_, 0);
v_currRecDepth_3109_ = lean_ctor_get(v___y_3105_, 1);
v_ref_3110_ = lean_ctor_get(v___y_3105_, 2);
v_optionFlags_3111_ = lean_ctor_get_uint16(v___y_3105_, sizeof(void*)*3);
v_suppressElabErrors_3112_ = lean_ctor_get_uint8(v___y_3105_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3113_ = lean_ctor_get_uint8(v___y_3105_, sizeof(void*)*3 + 3);
v_ref_3114_ = l_Lean_replaceRef(v_ref_3099_, v_ref_3110_);
lean_inc(v_currRecDepth_3109_);
lean_inc_ref(v_toCold_3108_);
v___x_3115_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3115_, 0, v_toCold_3108_);
lean_ctor_set(v___x_3115_, 1, v_currRecDepth_3109_);
lean_ctor_set(v___x_3115_, 2, v_ref_3114_);
lean_ctor_set_uint16(v___x_3115_, sizeof(void*)*3, v_optionFlags_3111_);
lean_ctor_set_uint8(v___x_3115_, sizeof(void*)*3 + 2, v_suppressElabErrors_3112_);
lean_ctor_set_uint8(v___x_3115_, sizeof(void*)*3 + 3, v_isRecordingDeps_3113_);
v___x_3116_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v_msg_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___x_3115_, v___y_3106_);
lean_dec_ref_known(v___x_3115_, 3);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_3117_, lean_object* v_msg_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_3117_, v_msg_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v_ref_3117_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_3127_, lean_object* v_id_3128_, uint8_t v_minIndexable_3129_, lean_object* v_as_x27_3130_, lean_object* v_b_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
if (lean_obj_tag(v_as_x27_3130_) == 0)
{
lean_object* v___x_3137_; 
lean_dec(v_id_3128_);
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v_b_3131_);
return v___x_3137_;
}
else
{
lean_object* v_head_3138_; lean_object* v_tail_3139_; lean_object* v_toCold_3140_; lean_object* v_currRecDepth_3141_; lean_object* v_ref_3142_; uint16_t v_optionFlags_3143_; uint8_t v_suppressElabErrors_3144_; uint8_t v_isRecordingDeps_3145_; uint8_t v___x_3146_; uint8_t v___x_3147_; lean_object* v___x_3148_; lean_object* v_ref_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v_head_3138_ = lean_ctor_get(v_as_x27_3130_, 0);
v_tail_3139_ = lean_ctor_get(v_as_x27_3130_, 1);
v_toCold_3140_ = lean_ctor_get(v___y_3134_, 0);
v_currRecDepth_3141_ = lean_ctor_get(v___y_3134_, 1);
v_ref_3142_ = lean_ctor_get(v___y_3134_, 2);
v_optionFlags_3143_ = lean_ctor_get_uint16(v___y_3134_, sizeof(void*)*3);
v_suppressElabErrors_3144_ = lean_ctor_get_uint8(v___y_3134_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3145_ = lean_ctor_get_uint8(v___y_3134_, sizeof(void*)*3 + 3);
v___x_3146_ = 0;
v___x_3147_ = 1;
v___x_3148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_ref_3149_ = l_Lean_replaceRef(v_p_3127_, v_ref_3142_);
lean_inc(v_currRecDepth_3141_);
lean_inc_ref(v_toCold_3140_);
v___x_3150_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3150_, 0, v_toCold_3140_);
lean_ctor_set(v___x_3150_, 1, v_currRecDepth_3141_);
lean_ctor_set(v___x_3150_, 2, v_ref_3149_);
lean_ctor_set_uint16(v___x_3150_, sizeof(void*)*3, v_optionFlags_3143_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*3 + 2, v_suppressElabErrors_3144_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*3 + 3, v_isRecordingDeps_3145_);
lean_inc(v_head_3138_);
lean_inc(v_id_3128_);
v___x_3151_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_3131_, v_id_3128_, v_head_3138_, v___x_3148_, v_minIndexable_3129_, v___x_3146_, v___x_3147_, v___y_3132_, v___y_3133_, v___x_3150_, v___y_3135_);
lean_dec_ref_known(v___x_3150_, 3);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
v_as_x27_3130_ = v_tail_3139_;
v_b_3131_ = v_a_3152_;
goto _start;
}
else
{
lean_dec(v_id_3128_);
return v___x_3151_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_3154_, lean_object* v_id_3155_, lean_object* v_minIndexable_3156_, lean_object* v_as_x27_3157_, lean_object* v_b_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v_minIndexable_boxed_3164_; lean_object* v_res_3165_; 
v_minIndexable_boxed_3164_ = lean_unbox(v_minIndexable_3156_);
v_res_3165_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3154_, v_id_3155_, v_minIndexable_boxed_3164_, v_as_x27_3157_, v_b_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v_as_x27_3157_);
lean_dec(v_p_3154_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_3166_){
_start:
{
if (lean_obj_tag(v_x_3166_) == 0)
{
lean_object* v___x_3167_; 
v___x_3167_ = lean_box(0);
return v___x_3167_;
}
else
{
lean_object* v_head_3168_; lean_object* v_tail_3169_; lean_object* v_fst_3170_; uint8_t v___x_3171_; 
v_head_3168_ = lean_ctor_get(v_x_3166_, 0);
v_tail_3169_ = lean_ctor_get(v_x_3166_, 1);
v_fst_3170_ = lean_ctor_get(v_head_3168_, 0);
v___x_3171_ = l_Lean_isPrivateName(v_fst_3170_);
if (v___x_3171_ == 0)
{
v_x_3166_ = v_tail_3169_;
goto _start;
}
else
{
lean_object* v___x_3173_; 
lean_inc(v_head_3168_);
v___x_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3173_, 0, v_head_3168_);
return v___x_3173_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_3174_);
lean_dec(v_x_3174_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_3176_, lean_object* v_msgData_3177_, uint8_t v_severity_3178_, uint8_t v_isSilent_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; uint8_t v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; uint8_t v___y_3192_; lean_object* v_toCold_3193_; lean_object* v___y_3194_; lean_object* v___y_3223_; lean_object* v___y_3224_; uint8_t v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; uint8_t v___y_3228_; uint8_t v___y_3229_; lean_object* v___y_3230_; uint8_t v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; uint8_t v___y_3254_; uint8_t v___y_3255_; lean_object* v___y_3256_; uint8_t v___y_3260_; uint8_t v___y_3261_; uint8_t v___y_3262_; uint8_t v___x_3273_; uint8_t v___y_3275_; uint8_t v___y_3276_; uint8_t v___y_3277_; uint8_t v___y_3279_; uint8_t v___x_3287_; 
v___x_3273_ = 2;
v___x_3287_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3178_, v___x_3273_);
if (v___x_3287_ == 0)
{
v___y_3279_ = v___x_3287_;
goto v___jp_3278_;
}
else
{
uint8_t v___x_3288_; 
lean_inc_ref(v_msgData_3177_);
v___x_3288_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3177_);
v___y_3279_ = v___x_3288_;
goto v___jp_3278_;
}
v___jp_3185_:
{
lean_object* v_currNamespace_3195_; lean_object* v_openDecls_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v_env_3201_; lean_object* v_nextMacroScope_3202_; lean_object* v_ngen_3203_; lean_object* v_auxDeclNGen_3204_; lean_object* v_traceState_3205_; lean_object* v_cache_3206_; lean_object* v_recordedDeps_3207_; lean_object* v_messages_3208_; lean_object* v_infoState_3209_; lean_object* v_snapshotTasks_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3221_; 
v_currNamespace_3195_ = lean_ctor_get(v_toCold_3193_, 4);
v_openDecls_3196_ = lean_ctor_get(v_toCold_3193_, 5);
lean_inc(v_openDecls_3196_);
lean_inc(v_currNamespace_3195_);
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v_currNamespace_3195_);
lean_ctor_set(v___x_3197_, 1, v_openDecls_3196_);
v___x_3198_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
lean_ctor_set(v___x_3198_, 1, v___y_3188_);
lean_inc_ref(v___y_3190_);
lean_inc_ref(v___y_3187_);
v___x_3199_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3199_, 0, v___y_3187_);
lean_ctor_set(v___x_3199_, 1, v___y_3186_);
lean_ctor_set(v___x_3199_, 2, v___y_3191_);
lean_ctor_set(v___x_3199_, 3, v___y_3190_);
lean_ctor_set(v___x_3199_, 4, v___x_3198_);
lean_ctor_set_uint8(v___x_3199_, sizeof(void*)*5, v___y_3189_);
lean_ctor_set_uint8(v___x_3199_, sizeof(void*)*5 + 1, v___y_3192_);
lean_ctor_set_uint8(v___x_3199_, sizeof(void*)*5 + 2, v_isSilent_3179_);
v___x_3200_ = lean_st_ref_take(v___y_3194_);
v_env_3201_ = lean_ctor_get(v___x_3200_, 0);
v_nextMacroScope_3202_ = lean_ctor_get(v___x_3200_, 1);
v_ngen_3203_ = lean_ctor_get(v___x_3200_, 2);
v_auxDeclNGen_3204_ = lean_ctor_get(v___x_3200_, 3);
v_traceState_3205_ = lean_ctor_get(v___x_3200_, 4);
v_cache_3206_ = lean_ctor_get(v___x_3200_, 5);
v_recordedDeps_3207_ = lean_ctor_get(v___x_3200_, 6);
v_messages_3208_ = lean_ctor_get(v___x_3200_, 7);
v_infoState_3209_ = lean_ctor_get(v___x_3200_, 8);
v_snapshotTasks_3210_ = lean_ctor_get(v___x_3200_, 9);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3212_ = v___x_3200_;
v_isShared_3213_ = v_isSharedCheck_3221_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_snapshotTasks_3210_);
lean_inc(v_infoState_3209_);
lean_inc(v_messages_3208_);
lean_inc(v_recordedDeps_3207_);
lean_inc(v_cache_3206_);
lean_inc(v_traceState_3205_);
lean_inc(v_auxDeclNGen_3204_);
lean_inc(v_ngen_3203_);
lean_inc(v_nextMacroScope_3202_);
lean_inc(v_env_3201_);
lean_dec(v___x_3200_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3221_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3214_ = lean_box(0);
v___x_3215_ = l_Lean_MessageLog_add(v___x_3199_, v_messages_3208_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 7, v___x_3215_);
v___x_3217_ = v___x_3212_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_env_3201_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_nextMacroScope_3202_);
lean_ctor_set(v_reuseFailAlloc_3220_, 2, v_ngen_3203_);
lean_ctor_set(v_reuseFailAlloc_3220_, 3, v_auxDeclNGen_3204_);
lean_ctor_set(v_reuseFailAlloc_3220_, 4, v_traceState_3205_);
lean_ctor_set(v_reuseFailAlloc_3220_, 5, v_cache_3206_);
lean_ctor_set(v_reuseFailAlloc_3220_, 6, v_recordedDeps_3207_);
lean_ctor_set(v_reuseFailAlloc_3220_, 7, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3220_, 8, v_infoState_3209_);
lean_ctor_set(v_reuseFailAlloc_3220_, 9, v_snapshotTasks_3210_);
v___x_3217_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = lean_st_ref_put(v___y_3194_, v___x_3217_);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3214_);
return v___x_3219_;
}
}
}
v___jp_3222_:
{
lean_object* v_fileName_3231_; lean_object* v_fileMap_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3248_; 
v_fileName_3231_ = lean_ctor_get(v___y_3227_, 0);
v_fileMap_3232_ = lean_ctor_get(v___y_3227_, 1);
v___x_3233_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3177_);
v___x_3234_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_3233_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3248_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3248_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
lean_inc_ref_n(v_fileMap_3232_, 2);
v___x_3239_ = l_Lean_FileMap_toPosition(v_fileMap_3232_, v___y_3226_);
lean_dec(v___y_3226_);
v___x_3240_ = l_Lean_FileMap_toPosition(v_fileMap_3232_, v___y_3230_);
lean_dec(v___y_3230_);
v___x_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
v___x_3242_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_3225_ == 0)
{
lean_del_object(v___x_3237_);
lean_dec_ref(v___y_3224_);
v___y_3186_ = v___x_3239_;
v___y_3187_ = v_fileName_3231_;
v___y_3188_ = v_a_3235_;
v___y_3189_ = v___y_3228_;
v___y_3190_ = v___x_3242_;
v___y_3191_ = v___x_3241_;
v___y_3192_ = v___y_3229_;
v_toCold_3193_ = v___y_3223_;
v___y_3194_ = v___y_3183_;
goto v___jp_3185_;
}
else
{
uint8_t v___x_3243_; 
lean_inc(v_a_3235_);
v___x_3243_ = l_Lean_MessageData_hasTag(v___y_3224_, v_a_3235_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3246_; 
lean_dec_ref_known(v___x_3241_, 1);
lean_dec_ref(v___x_3239_);
lean_dec(v_a_3235_);
v___x_3244_ = lean_box(0);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3244_);
v___x_3246_ = v___x_3237_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
else
{
lean_del_object(v___x_3237_);
v___y_3186_ = v___x_3239_;
v___y_3187_ = v_fileName_3231_;
v___y_3188_ = v_a_3235_;
v___y_3189_ = v___y_3228_;
v___y_3190_ = v___x_3242_;
v___y_3191_ = v___x_3241_;
v___y_3192_ = v___y_3229_;
v_toCold_3193_ = v___y_3223_;
v___y_3194_ = v___y_3183_;
goto v___jp_3185_;
}
}
}
}
v___jp_3249_:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lean_Syntax_getTailPos_x3f(v___y_3253_, v___y_3254_);
lean_dec(v___y_3253_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_inc(v___y_3256_);
v___y_3223_ = v___y_3251_;
v___y_3224_ = v___y_3252_;
v___y_3225_ = v___y_3250_;
v___y_3226_ = v___y_3256_;
v___y_3227_ = v___y_3251_;
v___y_3228_ = v___y_3254_;
v___y_3229_ = v___y_3255_;
v___y_3230_ = v___y_3256_;
goto v___jp_3222_;
}
else
{
lean_object* v_val_3258_; 
v_val_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_val_3258_);
lean_dec_ref_known(v___x_3257_, 1);
v___y_3223_ = v___y_3251_;
v___y_3224_ = v___y_3252_;
v___y_3225_ = v___y_3250_;
v___y_3226_ = v___y_3256_;
v___y_3227_ = v___y_3251_;
v___y_3228_ = v___y_3254_;
v___y_3229_ = v___y_3255_;
v___y_3230_ = v_val_3258_;
goto v___jp_3222_;
}
}
v___jp_3259_:
{
lean_object* v_toCold_3263_; lean_object* v_ref_3264_; uint8_t v_suppressElabErrors_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___f_3268_; lean_object* v_ref_3269_; lean_object* v___x_3270_; 
v_toCold_3263_ = lean_ctor_get(v___y_3182_, 0);
v_ref_3264_ = lean_ctor_get(v___y_3182_, 2);
v_suppressElabErrors_3265_ = lean_ctor_get_uint8(v___y_3182_, sizeof(void*)*3 + 2);
v___x_3266_ = lean_box(v_suppressElabErrors_3265_);
v___x_3267_ = lean_box(v___y_3260_);
v___f_3268_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3268_, 0, v___x_3266_);
lean_closure_set(v___f_3268_, 1, v___x_3267_);
v_ref_3269_ = l_Lean_replaceRef(v_ref_3176_, v_ref_3264_);
v___x_3270_ = l_Lean_Syntax_getPos_x3f(v_ref_3269_, v___y_3261_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_unsigned_to_nat(0u);
v___y_3250_ = v_suppressElabErrors_3265_;
v___y_3251_ = v_toCold_3263_;
v___y_3252_ = v___f_3268_;
v___y_3253_ = v_ref_3269_;
v___y_3254_ = v___y_3261_;
v___y_3255_ = v___y_3262_;
v___y_3256_ = v___x_3271_;
goto v___jp_3249_;
}
else
{
lean_object* v_val_3272_; 
v_val_3272_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_val_3272_);
lean_dec_ref_known(v___x_3270_, 1);
v___y_3250_ = v_suppressElabErrors_3265_;
v___y_3251_ = v_toCold_3263_;
v___y_3252_ = v___f_3268_;
v___y_3253_ = v_ref_3269_;
v___y_3254_ = v___y_3261_;
v___y_3255_ = v___y_3262_;
v___y_3256_ = v_val_3272_;
goto v___jp_3249_;
}
}
v___jp_3274_:
{
if (v___y_3277_ == 0)
{
v___y_3260_ = v___y_3275_;
v___y_3261_ = v___y_3276_;
v___y_3262_ = v_severity_3178_;
goto v___jp_3259_;
}
else
{
v___y_3260_ = v___y_3275_;
v___y_3261_ = v___y_3276_;
v___y_3262_ = v___x_3273_;
goto v___jp_3259_;
}
}
v___jp_3278_:
{
if (v___y_3279_ == 0)
{
uint8_t v___x_3280_; uint8_t v___x_3281_; 
v___x_3280_ = 1;
v___x_3281_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3178_, v___x_3280_);
if (v___x_3281_ == 0)
{
v___y_3275_ = v___y_3279_;
v___y_3276_ = v___y_3279_;
v___y_3277_ = v___x_3281_;
goto v___jp_3274_;
}
else
{
lean_object* v___x_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
v___x_3282_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3182_);
v___x_3283_ = l_Lean_warningAsError;
v___x_3284_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3282_, v___x_3283_);
lean_dec_ref(v___x_3282_);
v___y_3275_ = v___y_3279_;
v___y_3276_ = v___y_3279_;
v___y_3277_ = v___x_3284_;
goto v___jp_3274_;
}
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
lean_dec_ref(v_msgData_3177_);
v___x_3285_ = lean_box(0);
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
return v___x_3286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_3289_, lean_object* v_msgData_3290_, lean_object* v_severity_3291_, lean_object* v_isSilent_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
uint8_t v_severity_boxed_3298_; uint8_t v_isSilent_boxed_3299_; lean_object* v_res_3300_; 
v_severity_boxed_3298_ = lean_unbox(v_severity_3291_);
v_isSilent_boxed_3299_ = lean_unbox(v_isSilent_3292_);
v_res_3300_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3289_, v_msgData_3290_, v_severity_boxed_3298_, v_isSilent_boxed_3299_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v_ref_3289_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_3301_, uint8_t v_severity_3302_, uint8_t v_isSilent_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_ref_3311_; lean_object* v___x_3312_; 
v_ref_3311_ = lean_ctor_get(v___y_3308_, 2);
v___x_3312_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3311_, v_msgData_3301_, v_severity_3302_, v_isSilent_3303_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_3313_, lean_object* v_severity_3314_, lean_object* v_isSilent_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
uint8_t v_severity_boxed_3323_; uint8_t v_isSilent_boxed_3324_; lean_object* v_res_3325_; 
v_severity_boxed_3323_ = lean_unbox(v_severity_3314_);
v_isSilent_boxed_3324_ = lean_unbox(v_isSilent_3315_);
v_res_3325_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3313_, v_severity_boxed_3323_, v_isSilent_boxed_3324_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
uint8_t v___x_3334_; uint8_t v___x_3335_; lean_object* v___x_3336_; 
v___x_3334_ = 1;
v___x_3335_ = 0;
v___x_3336_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3326_, v___x_3334_, v___x_3335_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v___x_3349_; uint8_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3349_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3347_);
v___x_3350_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v___x_3349_, v_opt_3346_);
lean_dec_ref(v___x_3349_);
v___x_3351_ = lean_box(v___x_3350_);
v___x_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3353_, v___y_3354_);
lean_dec_ref(v___y_3354_);
lean_dec_ref(v_opt_3353_);
return v_res_3356_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3359_ = l_Lean_stringToMessageData(v___x_3358_);
return v___x_3359_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3362_ = l_Lean_stringToMessageData(v___x_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v___x_3371_; lean_object* v_env_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3394_; 
v___x_3371_ = lean_st_ref_get(v___y_3369_);
v_env_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc_ref(v_env_3372_);
lean_dec(v___x_3371_);
v___x_3373_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3374_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3373_, v___y_3368_);
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3377_ = v___x_3374_;
v_isShared_3378_ = v_isSharedCheck_3394_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3374_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3394_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
uint8_t v_isExporting_3384_; 
v_isExporting_3384_ = lean_ctor_get_uint8(v_env_3372_, sizeof(void*)*13);
lean_dec_ref(v_env_3372_);
if (v_isExporting_3384_ == 0)
{
lean_dec(v_a_3375_);
lean_dec(v_id_3363_);
goto v___jp_3379_;
}
else
{
uint8_t v___x_3385_; 
v___x_3385_ = l_Lean_isPrivateName(v_id_3363_);
if (v___x_3385_ == 0)
{
lean_dec(v_a_3375_);
lean_dec(v_id_3363_);
goto v___jp_3379_;
}
else
{
uint8_t v___x_3386_; 
v___x_3386_ = lean_unbox(v_a_3375_);
lean_dec(v_a_3375_);
if (v___x_3386_ == 0)
{
lean_dec(v_id_3363_);
goto v___jp_3379_;
}
else
{
lean_object* v___x_3387_; uint8_t v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
lean_del_object(v___x_3377_);
v___x_3387_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3388_ = 0;
v___x_3389_ = l_Lean_MessageData_ofConstName(v_id_3363_, v___x_3388_);
v___x_3390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3387_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3390_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3392_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
return v___x_3393_;
}
}
}
v___jp_3379_:
{
lean_object* v___x_3380_; lean_object* v___x_3382_; 
v___x_3380_ = lean_box(0);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 0, v___x_3380_);
v___x_3382_ = v___x_3377_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3404_, uint8_t v_enableLog_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; lean_object* v_toCold_3414_; lean_object* v_env_3415_; lean_object* v_currNamespace_3416_; lean_object* v_openDecls_3417_; lean_object* v___x_3418_; lean_object* v_res_3419_; lean_object* v___x_3420_; 
v___x_3413_ = lean_st_ref_get(v___y_3411_);
v_toCold_3414_ = lean_ctor_get(v___y_3410_, 0);
v_env_3415_ = lean_ctor_get(v___x_3413_, 0);
lean_inc_ref(v_env_3415_);
lean_dec(v___x_3413_);
v_currNamespace_3416_ = lean_ctor_get(v_toCold_3414_, 4);
v_openDecls_3417_ = lean_ctor_get(v_toCold_3414_, 5);
v___x_3418_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3410_);
lean_inc(v_openDecls_3417_);
lean_inc(v_currNamespace_3416_);
v_res_3419_ = l_Lean_ResolveName_resolveGlobalName(v_env_3415_, v___x_3418_, v_currNamespace_3416_, v_openDecls_3417_, v_id_3404_);
lean_dec_ref(v___x_3418_);
v___x_3420_ = lean_st_ref_get(v___y_3411_);
if (v_enableLog_3405_ == 0)
{
lean_object* v___x_3421_; 
lean_dec(v___x_3420_);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_res_3419_);
return v___x_3421_;
}
else
{
lean_object* v_env_3422_; uint8_t v_isExporting_3423_; 
v_env_3422_ = lean_ctor_get(v___x_3420_, 0);
lean_inc_ref(v_env_3422_);
lean_dec(v___x_3420_);
v_isExporting_3423_ = lean_ctor_get_uint8(v_env_3422_, sizeof(void*)*13);
lean_dec_ref(v_env_3422_);
if (v_isExporting_3423_ == 0)
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3424_, 0, v_res_3419_);
return v___x_3424_;
}
else
{
lean_object* v___x_3425_; 
v___x_3425_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3419_);
if (lean_obj_tag(v___x_3425_) == 1)
{
lean_object* v_val_3426_; lean_object* v_fst_3427_; lean_object* v___x_3428_; 
v_val_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_val_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v_fst_3427_ = lean_ctor_get(v_val_3426_, 0);
lean_inc(v_fst_3427_);
lean_dec(v_val_3426_);
v___x_3428_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3427_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v___x_3428_, 0);
lean_dec(v_unused_3436_);
v___x_3430_ = v___x_3428_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_dec(v___x_3428_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v_res_3419_);
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_res_3419_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec(v_res_3419_);
v_a_3437_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3428_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3428_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
else
{
lean_object* v___x_3445_; 
lean_dec(v___x_3425_);
v___x_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3445_, 0, v_res_3419_);
return v___x_3445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3446_, lean_object* v_enableLog_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
uint8_t v_enableLog_boxed_3455_; lean_object* v_res_3456_; 
v_enableLog_boxed_3455_ = lean_unbox(v_enableLog_3447_);
v_res_3456_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3446_, v_enableLog_boxed_3455_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
if (lean_obj_tag(v_a_3457_) == 0)
{
lean_object* v___x_3459_; 
v___x_3459_ = l_List_reverse___redArg(v_a_3458_);
return v___x_3459_;
}
else
{
lean_object* v_head_3460_; lean_object* v_tail_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3472_; 
v_head_3460_ = lean_ctor_get(v_a_3457_, 0);
v_tail_3461_ = lean_ctor_get(v_a_3457_, 1);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_a_3457_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3463_ = v_a_3457_;
v_isShared_3464_ = v_isSharedCheck_3472_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_tail_3461_);
lean_inc(v_head_3460_);
lean_dec(v_a_3457_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3472_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v_snd_3465_; uint8_t v___x_3466_; 
v_snd_3465_ = lean_ctor_get(v_head_3460_, 1);
v___x_3466_ = l_List_isEmpty___redArg(v_snd_3465_);
if (v___x_3466_ == 0)
{
lean_del_object(v___x_3463_);
lean_dec(v_head_3460_);
v_a_3457_ = v_tail_3461_;
goto _start;
}
else
{
lean_object* v___x_3469_; 
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v_a_3458_);
v___x_3469_ = v___x_3463_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_head_3460_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_a_3458_);
v___x_3469_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
v_a_3457_ = v_tail_3461_;
v_a_3458_ = v___x_3469_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3473_, lean_object* v_findLocalDecl_x3f_3474_, lean_object* v_n_3475_, lean_object* v_projs_3476_, uint8_t v_globalDeclFound_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v___y_3486_; lean_object* v___y_3487_; uint8_t v_globalDeclFoundNext_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v_imported_3497_; lean_object* v_ctx_3498_; lean_object* v_scopes_3499_; lean_object* v_givenNameView_3500_; uint8_t v___y_3502_; 
v_imported_3497_ = lean_ctor_get(v_view_3473_, 1);
v_ctx_3498_ = lean_ctor_get(v_view_3473_, 2);
v_scopes_3499_ = lean_ctor_get(v_view_3473_, 3);
lean_inc(v_scopes_3499_);
lean_inc(v_ctx_3498_);
lean_inc(v_imported_3497_);
lean_inc(v_n_3475_);
v_givenNameView_3500_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3500_, 0, v_n_3475_);
lean_ctor_set(v_givenNameView_3500_, 1, v_imported_3497_);
lean_ctor_set(v_givenNameView_3500_, 2, v_ctx_3498_);
lean_ctor_set(v_givenNameView_3500_, 3, v_scopes_3499_);
if (v_globalDeclFound_3477_ == 0)
{
v___y_3502_ = v_globalDeclFound_3477_;
goto v___jp_3501_;
}
else
{
uint8_t v___x_3537_; 
v___x_3537_ = l_List_isEmpty___redArg(v_projs_3476_);
if (v___x_3537_ == 0)
{
v___y_3502_ = v_globalDeclFound_3477_;
goto v___jp_3501_;
}
else
{
uint8_t v___x_3538_; 
v___x_3538_ = 0;
v___y_3502_ = v___x_3538_;
goto v___jp_3501_;
}
}
v___jp_3485_:
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___y_3486_);
lean_ctor_set(v___x_3495_, 1, v_projs_3476_);
v_n_3475_ = v___y_3487_;
v_projs_3476_ = v___x_3495_;
v_globalDeclFound_3477_ = v_globalDeclFoundNext_3488_;
v___y_3478_ = v___y_3489_;
v___y_3479_ = v___y_3490_;
v___y_3480_ = v___y_3491_;
v___y_3481_ = v___y_3492_;
v___y_3482_ = v___y_3493_;
v___y_3483_ = v___y_3494_;
goto _start;
}
v___jp_3501_:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = lean_box(v___y_3502_);
lean_inc_ref(v_findLocalDecl_x3f_3474_);
lean_inc_ref(v_givenNameView_3500_);
v___x_3504_ = lean_apply_2(v_findLocalDecl_x3f_3474_, v_givenNameView_3500_, v___x_3503_);
if (lean_obj_tag(v___x_3504_) == 0)
{
if (lean_obj_tag(v_n_3475_) == 1)
{
if (v_globalDeclFound_3477_ == 0)
{
lean_object* v_pre_3505_; lean_object* v_str_3506_; uint8_t v_globalDeclFoundNext_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v_pre_3505_ = lean_ctor_get(v_n_3475_, 0);
lean_inc(v_pre_3505_);
v_str_3506_ = lean_ctor_get(v_n_3475_, 1);
lean_inc_ref(v_str_3506_);
lean_dec_ref_known(v_n_3475_, 2);
v_globalDeclFoundNext_3507_ = 1;
v___x_3508_ = l_Lean_MacroScopesView_review(v_givenNameView_3500_);
v___x_3509_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3508_, v_globalDeclFound_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3511_; lean_object* v_r_3512_; uint8_t v___x_3513_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v___x_3511_ = lean_box(0);
v_r_3512_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3510_, v___x_3511_);
v___x_3513_ = l_List_isEmpty___redArg(v_r_3512_);
lean_dec(v_r_3512_);
if (v___x_3513_ == 0)
{
v___y_3486_ = v_str_3506_;
v___y_3487_ = v_pre_3505_;
v_globalDeclFoundNext_3488_ = v_globalDeclFoundNext_3507_;
v___y_3489_ = v___y_3478_;
v___y_3490_ = v___y_3479_;
v___y_3491_ = v___y_3480_;
v___y_3492_ = v___y_3481_;
v___y_3493_ = v___y_3482_;
v___y_3494_ = v___y_3483_;
goto v___jp_3485_;
}
else
{
v___y_3486_ = v_str_3506_;
v___y_3487_ = v_pre_3505_;
v_globalDeclFoundNext_3488_ = v_globalDeclFound_3477_;
v___y_3489_ = v___y_3478_;
v___y_3490_ = v___y_3479_;
v___y_3491_ = v___y_3480_;
v___y_3492_ = v___y_3481_;
v___y_3493_ = v___y_3482_;
v___y_3494_ = v___y_3483_;
goto v___jp_3485_;
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_dec_ref(v_str_3506_);
lean_dec(v_pre_3505_);
lean_dec(v_projs_3476_);
lean_dec_ref(v_findLocalDecl_x3f_3474_);
v_a_3514_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3509_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3509_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
else
{
lean_object* v_pre_3522_; lean_object* v_str_3523_; 
lean_dec_ref_known(v_givenNameView_3500_, 4);
v_pre_3522_ = lean_ctor_get(v_n_3475_, 0);
lean_inc(v_pre_3522_);
v_str_3523_ = lean_ctor_get(v_n_3475_, 1);
lean_inc_ref(v_str_3523_);
lean_dec_ref_known(v_n_3475_, 2);
v___y_3486_ = v_str_3523_;
v___y_3487_ = v_pre_3522_;
v_globalDeclFoundNext_3488_ = v_globalDeclFound_3477_;
v___y_3489_ = v___y_3478_;
v___y_3490_ = v___y_3479_;
v___y_3491_ = v___y_3480_;
v___y_3492_ = v___y_3481_;
v___y_3493_ = v___y_3482_;
v___y_3494_ = v___y_3483_;
goto v___jp_3485_;
}
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_dec_ref_known(v_givenNameView_3500_, 4);
lean_dec(v_projs_3476_);
lean_dec(v_n_3475_);
lean_dec_ref(v_findLocalDecl_x3f_3474_);
v___x_3524_ = lean_box(0);
v___x_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
return v___x_3525_;
}
}
else
{
lean_object* v_val_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3536_; 
lean_dec_ref_known(v_givenNameView_3500_, 4);
lean_dec(v_n_3475_);
lean_dec_ref(v_findLocalDecl_x3f_3474_);
v_val_3526_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3528_ = v___x_3504_;
v_isShared_3529_ = v_isSharedCheck_3536_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_val_3526_);
lean_dec(v___x_3504_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3536_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3533_; 
v___x_3530_ = l_Lean_LocalDecl_toExpr(v_val_3526_);
v___x_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
lean_ctor_set(v___x_3531_, 1, v_projs_3476_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3531_);
v___x_3533_ = v___x_3528_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
lean_object* v___x_3534_; 
v___x_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
return v___x_3534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3539_, lean_object* v_findLocalDecl_x3f_3540_, lean_object* v_n_3541_, lean_object* v_projs_3542_, lean_object* v_globalDeclFound_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
uint8_t v_globalDeclFound_boxed_3551_; lean_object* v_res_3552_; 
v_globalDeclFound_boxed_3551_ = lean_unbox(v_globalDeclFound_3543_);
v_res_3552_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3539_, v_findLocalDecl_x3f_3540_, v_n_3541_, v_projs_3542_, v_globalDeclFound_boxed_3551_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec_ref(v_view_3539_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3553_, lean_object* v_givenName_3554_, lean_object* v_as_3555_, lean_object* v_i_3556_){
_start:
{
lean_object* v_zero_3557_; uint8_t v_isZero_3558_; 
v_zero_3557_ = lean_unsigned_to_nat(0u);
v_isZero_3558_ = lean_nat_dec_eq(v_i_3556_, v_zero_3557_);
if (v_isZero_3558_ == 1)
{
lean_object* v___x_3559_; 
lean_dec(v_i_3556_);
v___x_3559_ = lean_box(0);
return v___x_3559_;
}
else
{
lean_object* v_one_3560_; lean_object* v_n_3561_; lean_object* v___y_3563_; lean_object* v___x_3565_; 
v_one_3560_ = lean_unsigned_to_nat(1u);
v_n_3561_ = lean_nat_sub(v_i_3556_, v_one_3560_);
lean_dec(v_i_3556_);
v___x_3565_ = lean_array_fget_borrowed(v_as_3555_, v_n_3561_);
if (lean_obj_tag(v___x_3565_) == 0)
{
v___y_3563_ = v___x_3565_;
goto v___jp_3562_;
}
else
{
lean_object* v_val_3566_; uint8_t v___x_3567_; 
v_val_3566_ = lean_ctor_get(v___x_3565_, 0);
v___x_3567_ = l_Lean_LocalDecl_isAuxDecl(v_val_3566_);
if (v___x_3567_ == 0)
{
v___y_3563_ = v_localDecl_x3f_3553_;
goto v___jp_3562_;
}
else
{
lean_object* v___x_3568_; uint8_t v___x_3569_; 
v___x_3568_ = l_Lean_LocalDecl_userName(v_val_3566_);
v___x_3569_ = lean_name_eq(v___x_3568_, v_givenName_3554_);
lean_dec(v___x_3568_);
if (v___x_3569_ == 0)
{
v_i_3556_ = v_n_3561_;
goto _start;
}
else
{
v___y_3563_ = v___x_3565_;
goto v___jp_3562_;
}
}
}
v___jp_3562_:
{
if (lean_obj_tag(v___y_3563_) == 0)
{
v_i_3556_ = v_n_3561_;
goto _start;
}
else
{
lean_dec(v_n_3561_);
lean_inc_ref(v___y_3563_);
return v___y_3563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3571_, lean_object* v_givenName_3572_, lean_object* v_as_3573_, lean_object* v_i_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3571_, v_givenName_3572_, v_as_3573_, v_i_3574_);
lean_dec_ref(v_as_3573_);
lean_dec(v_givenName_3572_);
lean_dec(v_localDecl_x3f_3571_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3576_, lean_object* v_givenName_3577_, lean_object* v_as_3578_, lean_object* v_i_3579_){
_start:
{
lean_object* v_zero_3580_; uint8_t v_isZero_3581_; 
v_zero_3580_ = lean_unsigned_to_nat(0u);
v_isZero_3581_ = lean_nat_dec_eq(v_i_3579_, v_zero_3580_);
if (v_isZero_3581_ == 1)
{
lean_object* v___x_3582_; 
lean_dec(v_i_3579_);
v___x_3582_ = lean_box(0);
return v___x_3582_;
}
else
{
lean_object* v_one_3583_; lean_object* v_n_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v_one_3583_ = lean_unsigned_to_nat(1u);
v_n_3584_ = lean_nat_sub(v_i_3579_, v_one_3583_);
lean_dec(v_i_3579_);
v___x_3585_ = lean_array_fget_borrowed(v_as_3578_, v_n_3584_);
v___x_3586_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3576_, v_givenName_3577_, v___x_3585_);
if (lean_obj_tag(v___x_3586_) == 0)
{
v_i_3579_ = v_n_3584_;
goto _start;
}
else
{
lean_dec(v_n_3584_);
return v___x_3586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3588_, lean_object* v_givenName_3589_, lean_object* v_x_3590_){
_start:
{
if (lean_obj_tag(v_x_3590_) == 0)
{
lean_object* v_cs_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v_cs_3591_ = lean_ctor_get(v_x_3590_, 0);
v___x_3592_ = lean_array_get_size(v_cs_3591_);
v___x_3593_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3588_, v_givenName_3589_, v_cs_3591_, v___x_3592_);
return v___x_3593_;
}
else
{
lean_object* v_vs_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v_vs_3594_ = lean_ctor_get(v_x_3590_, 0);
v___x_3595_ = lean_array_get_size(v_vs_3594_);
v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3588_, v_givenName_3589_, v_vs_3594_, v___x_3595_);
return v___x_3596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3597_, lean_object* v_givenName_3598_, lean_object* v_x_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3597_, v_givenName_3598_, v_x_3599_);
lean_dec_ref(v_x_3599_);
lean_dec(v_givenName_3598_);
lean_dec(v_localDecl_x3f_3597_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3601_, lean_object* v_givenName_3602_, lean_object* v_as_3603_, lean_object* v_i_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3601_, v_givenName_3602_, v_as_3603_, v_i_3604_);
lean_dec_ref(v_as_3603_);
lean_dec(v_givenName_3602_);
lean_dec(v_localDecl_x3f_3601_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3606_, lean_object* v_givenName_3607_, lean_object* v_t_3608_){
_start:
{
lean_object* v_root_3609_; lean_object* v_tail_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v_root_3609_ = lean_ctor_get(v_t_3608_, 0);
v_tail_3610_ = lean_ctor_get(v_t_3608_, 1);
v___x_3611_ = lean_array_get_size(v_tail_3610_);
v___x_3612_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3606_, v_givenName_3607_, v_tail_3610_, v___x_3611_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3606_, v_givenName_3607_, v_root_3609_);
return v___x_3613_;
}
else
{
return v___x_3612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3614_, lean_object* v_givenName_3615_, lean_object* v_t_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3614_, v_givenName_3615_, v_t_3616_);
lean_dec_ref(v_t_3616_);
lean_dec(v_givenName_3615_);
lean_dec(v_localDecl_x3f_3614_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3618_, lean_object* v_k_3619_){
_start:
{
if (lean_obj_tag(v_t_3618_) == 0)
{
lean_object* v_k_3620_; lean_object* v_v_3621_; lean_object* v_l_3622_; lean_object* v_r_3623_; uint8_t v___x_3624_; 
v_k_3620_ = lean_ctor_get(v_t_3618_, 1);
v_v_3621_ = lean_ctor_get(v_t_3618_, 2);
v_l_3622_ = lean_ctor_get(v_t_3618_, 3);
v_r_3623_ = lean_ctor_get(v_t_3618_, 4);
v___x_3624_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3619_, v_k_3620_);
switch(v___x_3624_)
{
case 0:
{
v_t_3618_ = v_l_3622_;
goto _start;
}
case 1:
{
lean_object* v___x_3626_; 
lean_inc(v_v_3621_);
v___x_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3626_, 0, v_v_3621_);
return v___x_3626_;
}
default: 
{
v_t_3618_ = v_r_3623_;
goto _start;
}
}
}
else
{
lean_object* v___x_3628_; 
v___x_3628_ = lean_box(0);
return v___x_3628_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3629_, lean_object* v_k_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3629_, v_k_3630_);
lean_dec(v_k_3630_);
lean_dec(v_t_3629_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3632_, lean_object* v_givenName_3633_){
_start:
{
lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3634_ = l_Lean_LocalDecl_userName(v_localDecl_3632_);
v___x_3635_ = lean_name_eq(v___x_3634_, v_givenName_3633_);
lean_dec(v___x_3634_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; 
lean_dec_ref(v_localDecl_3632_);
v___x_3636_ = lean_box(0);
return v___x_3636_;
}
else
{
lean_object* v___x_3637_; 
v___x_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3637_, 0, v_localDecl_3632_);
return v___x_3637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3638_, lean_object* v_givenName_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3638_, v_givenName_3639_);
lean_dec(v_givenName_3639_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3641_, uint8_t v_skipAuxDecl_3642_, lean_object* v_auxDeclToFullName_3643_, lean_object* v___x_3644_, lean_object* v_givenNameView_3645_, lean_object* v_as_3646_, lean_object* v_i_3647_){
_start:
{
lean_object* v_zero_3648_; uint8_t v_isZero_3649_; 
v_zero_3648_ = lean_unsigned_to_nat(0u);
v_isZero_3649_ = lean_nat_dec_eq(v_i_3647_, v_zero_3648_);
if (v_isZero_3649_ == 1)
{
lean_object* v___x_3650_; 
lean_dec(v_i_3647_);
lean_dec_ref(v_givenNameView_3645_);
lean_dec(v___x_3644_);
v___x_3650_ = lean_box(0);
return v___x_3650_;
}
else
{
lean_object* v_one_3651_; lean_object* v_n_3652_; lean_object* v___y_3654_; lean_object* v___x_3656_; 
v_one_3651_ = lean_unsigned_to_nat(1u);
v_n_3652_ = lean_nat_sub(v_i_3647_, v_one_3651_);
lean_dec(v_i_3647_);
v___x_3656_ = lean_array_fget_borrowed(v_as_3646_, v_n_3652_);
if (lean_obj_tag(v___x_3656_) == 0)
{
v___y_3654_ = v___x_3656_;
goto v___jp_3653_;
}
else
{
lean_object* v_val_3657_; uint8_t v___x_3658_; 
v_val_3657_ = lean_ctor_get(v___x_3656_, 0);
v___x_3658_ = l_Lean_LocalDecl_isAuxDecl(v_val_3657_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; 
lean_inc(v_val_3657_);
v___x_3659_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3657_, v_givenName_3641_);
v___y_3654_ = v___x_3659_;
goto v___jp_3653_;
}
else
{
if (v_skipAuxDecl_3642_ == 0)
{
if (v___x_3658_ == 0)
{
v_i_3647_ = v_n_3652_;
goto _start;
}
else
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = l_Lean_LocalDecl_fvarId(v_val_3657_);
v___x_3662_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3643_, v___x_3661_);
lean_dec(v___x_3661_);
if (lean_obj_tag(v___x_3662_) == 1)
{
lean_object* v_val_3663_; lean_object* v_fullDeclView_3664_; lean_object* v___y_3666_; lean_object* v_name_3687_; lean_object* v___x_3688_; 
v_val_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_val_3663_);
lean_dec_ref_known(v___x_3662_, 1);
v_fullDeclView_3664_ = l_Lean_extractMacroScopes(v_val_3663_);
v_name_3687_ = lean_ctor_get(v_fullDeclView_3664_, 0);
lean_inc(v_name_3687_);
v___x_3688_ = l_Lean_privateToUserName_x3f(v_name_3687_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_inc(v_name_3687_);
v___y_3666_ = v_name_3687_;
goto v___jp_3665_;
}
else
{
lean_object* v_val_3689_; 
v_val_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_val_3689_);
lean_dec_ref_known(v___x_3688_, 1);
v___y_3666_ = v_val_3689_;
goto v___jp_3665_;
}
v___jp_3665_:
{
lean_object* v_imported_3667_; lean_object* v_ctx_3668_; lean_object* v_scopes_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3685_; 
v_imported_3667_ = lean_ctor_get(v_fullDeclView_3664_, 1);
v_ctx_3668_ = lean_ctor_get(v_fullDeclView_3664_, 2);
v_scopes_3669_ = lean_ctor_get(v_fullDeclView_3664_, 3);
v_isSharedCheck_3685_ = !lean_is_exclusive(v_fullDeclView_3664_);
if (v_isSharedCheck_3685_ == 0)
{
lean_object* v_unused_3686_; 
v_unused_3686_ = lean_ctor_get(v_fullDeclView_3664_, 0);
lean_dec(v_unused_3686_);
v___x_3671_ = v_fullDeclView_3664_;
v_isShared_3672_ = v_isSharedCheck_3685_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_scopes_3669_);
lean_inc(v_ctx_3668_);
lean_inc(v_imported_3667_);
lean_dec(v_fullDeclView_3664_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3685_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v_fullDeclView_3674_; 
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v___y_3666_);
v_fullDeclView_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___y_3666_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_imported_3667_);
lean_ctor_set(v_reuseFailAlloc_3684_, 2, v_ctx_3668_);
lean_ctor_set(v_reuseFailAlloc_3684_, 3, v_scopes_3669_);
v_fullDeclView_3674_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v_fullDeclName_3675_; uint8_t v___x_3676_; 
lean_inc_ref(v_fullDeclView_3674_);
v_fullDeclName_3675_ = l_Lean_MacroScopesView_review(v_fullDeclView_3674_);
v___x_3676_ = l_Lean_Name_isPrefixOf(v___x_3644_, v_fullDeclName_3675_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; 
lean_dec_ref(v_fullDeclView_3674_);
lean_inc(v___x_3644_);
lean_inc_ref(v_givenNameView_3645_);
lean_inc(v_val_3657_);
v___x_3677_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3657_, v_givenNameView_3645_, v_fullDeclName_3675_, v___x_3644_);
lean_dec(v_fullDeclName_3675_);
v___y_3654_ = v___x_3677_;
goto v___jp_3653_;
}
else
{
lean_object* v___x_3678_; lean_object* v_localDeclNameView_3679_; uint8_t v___x_3680_; 
lean_dec(v_fullDeclName_3675_);
v___x_3678_ = l_Lean_LocalDecl_userName(v_val_3657_);
v_localDeclNameView_3679_ = l_Lean_extractMacroScopes(v___x_3678_);
v___x_3680_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3679_, v_givenNameView_3645_);
lean_dec_ref(v_localDeclNameView_3679_);
if (v___x_3680_ == 0)
{
lean_dec_ref(v_fullDeclView_3674_);
v_i_3647_ = v_n_3652_;
goto _start;
}
else
{
uint8_t v___x_3682_; 
v___x_3682_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3645_, v_fullDeclView_3674_);
lean_dec_ref(v_fullDeclView_3674_);
if (v___x_3682_ == 0)
{
v_i_3647_ = v_n_3652_;
goto _start;
}
else
{
lean_inc_ref(v___x_3656_);
v___y_3654_ = v___x_3656_;
goto v___jp_3653_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3690_; 
lean_dec(v___x_3662_);
lean_inc(v_val_3657_);
v___x_3690_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3657_, v_givenName_3641_);
v___y_3654_ = v___x_3690_;
goto v___jp_3653_;
}
}
}
else
{
v_i_3647_ = v_n_3652_;
goto _start;
}
}
}
v___jp_3653_:
{
if (lean_obj_tag(v___y_3654_) == 0)
{
v_i_3647_ = v_n_3652_;
goto _start;
}
else
{
lean_dec(v_n_3652_);
lean_dec_ref(v_givenNameView_3645_);
lean_dec(v___x_3644_);
return v___y_3654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3692_, lean_object* v_skipAuxDecl_3693_, lean_object* v_auxDeclToFullName_3694_, lean_object* v___x_3695_, lean_object* v_givenNameView_3696_, lean_object* v_as_3697_, lean_object* v_i_3698_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3699_; lean_object* v_res_3700_; 
v_skipAuxDecl_boxed_3699_ = lean_unbox(v_skipAuxDecl_3693_);
v_res_3700_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3692_, v_skipAuxDecl_boxed_3699_, v_auxDeclToFullName_3694_, v___x_3695_, v_givenNameView_3696_, v_as_3697_, v_i_3698_);
lean_dec_ref(v_as_3697_);
lean_dec(v_auxDeclToFullName_3694_);
lean_dec(v_givenName_3692_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3701_, uint8_t v_skipAuxDecl_3702_, lean_object* v_auxDeclToFullName_3703_, lean_object* v___x_3704_, lean_object* v_givenNameView_3705_, lean_object* v_as_3706_, lean_object* v_i_3707_){
_start:
{
lean_object* v_zero_3708_; uint8_t v_isZero_3709_; 
v_zero_3708_ = lean_unsigned_to_nat(0u);
v_isZero_3709_ = lean_nat_dec_eq(v_i_3707_, v_zero_3708_);
if (v_isZero_3709_ == 1)
{
lean_object* v___x_3710_; 
lean_dec(v_i_3707_);
lean_dec_ref(v_givenNameView_3705_);
lean_dec(v___x_3704_);
v___x_3710_ = lean_box(0);
return v___x_3710_;
}
else
{
lean_object* v_one_3711_; lean_object* v_n_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v_one_3711_ = lean_unsigned_to_nat(1u);
v_n_3712_ = lean_nat_sub(v_i_3707_, v_one_3711_);
lean_dec(v_i_3707_);
v___x_3713_ = lean_array_fget_borrowed(v_as_3706_, v_n_3712_);
lean_inc_ref(v_givenNameView_3705_);
lean_inc(v___x_3704_);
v___x_3714_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3701_, v_skipAuxDecl_3702_, v_auxDeclToFullName_3703_, v___x_3704_, v_givenNameView_3705_, v___x_3713_);
if (lean_obj_tag(v___x_3714_) == 0)
{
v_i_3707_ = v_n_3712_;
goto _start;
}
else
{
lean_dec(v_n_3712_);
lean_dec_ref(v_givenNameView_3705_);
lean_dec(v___x_3704_);
return v___x_3714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3716_, uint8_t v_skipAuxDecl_3717_, lean_object* v_auxDeclToFullName_3718_, lean_object* v___x_3719_, lean_object* v_givenNameView_3720_, lean_object* v_x_3721_){
_start:
{
if (lean_obj_tag(v_x_3721_) == 0)
{
lean_object* v_cs_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v_cs_3722_ = lean_ctor_get(v_x_3721_, 0);
v___x_3723_ = lean_array_get_size(v_cs_3722_);
v___x_3724_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3716_, v_skipAuxDecl_3717_, v_auxDeclToFullName_3718_, v___x_3719_, v_givenNameView_3720_, v_cs_3722_, v___x_3723_);
return v___x_3724_;
}
else
{
lean_object* v_vs_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v_vs_3725_ = lean_ctor_get(v_x_3721_, 0);
v___x_3726_ = lean_array_get_size(v_vs_3725_);
v___x_3727_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3716_, v_skipAuxDecl_3717_, v_auxDeclToFullName_3718_, v___x_3719_, v_givenNameView_3720_, v_vs_3725_, v___x_3726_);
return v___x_3727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3728_, lean_object* v_skipAuxDecl_3729_, lean_object* v_auxDeclToFullName_3730_, lean_object* v___x_3731_, lean_object* v_givenNameView_3732_, lean_object* v_x_3733_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3734_; lean_object* v_res_3735_; 
v_skipAuxDecl_boxed_3734_ = lean_unbox(v_skipAuxDecl_3729_);
v_res_3735_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3728_, v_skipAuxDecl_boxed_3734_, v_auxDeclToFullName_3730_, v___x_3731_, v_givenNameView_3732_, v_x_3733_);
lean_dec_ref(v_x_3733_);
lean_dec(v_auxDeclToFullName_3730_);
lean_dec(v_givenName_3728_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3736_, lean_object* v_skipAuxDecl_3737_, lean_object* v_auxDeclToFullName_3738_, lean_object* v___x_3739_, lean_object* v_givenNameView_3740_, lean_object* v_as_3741_, lean_object* v_i_3742_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3743_; lean_object* v_res_3744_; 
v_skipAuxDecl_boxed_3743_ = lean_unbox(v_skipAuxDecl_3737_);
v_res_3744_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3736_, v_skipAuxDecl_boxed_3743_, v_auxDeclToFullName_3738_, v___x_3739_, v_givenNameView_3740_, v_as_3741_, v_i_3742_);
lean_dec_ref(v_as_3741_);
lean_dec(v_auxDeclToFullName_3738_);
lean_dec(v_givenName_3736_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3745_, uint8_t v_skipAuxDecl_3746_, lean_object* v_auxDeclToFullName_3747_, lean_object* v___x_3748_, lean_object* v_givenNameView_3749_, lean_object* v_t_3750_){
_start:
{
lean_object* v_root_3751_; lean_object* v_tail_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v_root_3751_ = lean_ctor_get(v_t_3750_, 0);
v_tail_3752_ = lean_ctor_get(v_t_3750_, 1);
v___x_3753_ = lean_array_get_size(v_tail_3752_);
lean_inc_ref(v_givenNameView_3749_);
lean_inc(v___x_3748_);
v___x_3754_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3745_, v_skipAuxDecl_3746_, v_auxDeclToFullName_3747_, v___x_3748_, v_givenNameView_3749_, v_tail_3752_, v___x_3753_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3745_, v_skipAuxDecl_3746_, v_auxDeclToFullName_3747_, v___x_3748_, v_givenNameView_3749_, v_root_3751_);
return v___x_3755_;
}
else
{
lean_dec_ref(v_givenNameView_3749_);
lean_dec(v___x_3748_);
return v___x_3754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3756_, lean_object* v_skipAuxDecl_3757_, lean_object* v_auxDeclToFullName_3758_, lean_object* v___x_3759_, lean_object* v_givenNameView_3760_, lean_object* v_t_3761_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3762_; lean_object* v_res_3763_; 
v_skipAuxDecl_boxed_3762_ = lean_unbox(v_skipAuxDecl_3757_);
v_res_3763_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3756_, v_skipAuxDecl_boxed_3762_, v_auxDeclToFullName_3758_, v___x_3759_, v_givenNameView_3760_, v_t_3761_);
lean_dec_ref(v_t_3761_);
lean_dec(v_auxDeclToFullName_3758_);
lean_dec(v_givenName_3756_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3764_, lean_object* v_currNamespace_3765_, lean_object* v_decls_3766_, lean_object* v_givenNameView_3767_, uint8_t v_skipAuxDecl_3768_){
_start:
{
lean_object* v_givenName_3769_; lean_object* v_localDecl_x3f_3770_; 
lean_inc_ref(v_givenNameView_3767_);
v_givenName_3769_ = l_Lean_MacroScopesView_review(v_givenNameView_3767_);
v_localDecl_x3f_3770_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3769_, v_skipAuxDecl_3768_, v_auxDeclToFullName_3764_, v_currNamespace_3765_, v_givenNameView_3767_, v_decls_3766_);
if (lean_obj_tag(v_localDecl_x3f_3770_) == 0)
{
if (v_skipAuxDecl_3768_ == 0)
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3770_, v_givenName_3769_, v_decls_3766_);
lean_dec(v_givenName_3769_);
return v___x_3771_;
}
else
{
lean_dec(v_givenName_3769_);
return v_localDecl_x3f_3770_;
}
}
else
{
lean_dec(v_givenName_3769_);
return v_localDecl_x3f_3770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3772_, lean_object* v_currNamespace_3773_, lean_object* v_decls_3774_, lean_object* v_givenNameView_3775_, lean_object* v_skipAuxDecl_3776_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3777_; lean_object* v_res_3778_; 
v_skipAuxDecl_boxed_3777_ = lean_unbox(v_skipAuxDecl_3776_);
v_res_3778_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3772_, v_currNamespace_3773_, v_decls_3774_, v_givenNameView_3775_, v_skipAuxDecl_boxed_3777_);
lean_dec_ref(v_decls_3774_);
lean_dec(v_auxDeclToFullName_3772_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_lctx_3787_; lean_object* v_toCold_3788_; lean_object* v_decls_3789_; lean_object* v_auxDeclToFullName_3790_; lean_object* v_currNamespace_3791_; lean_object* v_view_3792_; lean_object* v_name_3793_; lean_object* v_findLocalDecl_x3f_3794_; lean_object* v___x_3795_; uint8_t v___x_3796_; lean_object* v___x_3797_; 
v_lctx_3787_ = lean_ctor_get(v___y_3782_, 2);
v_toCold_3788_ = lean_ctor_get(v___y_3784_, 0);
v_decls_3789_ = lean_ctor_get(v_lctx_3787_, 1);
v_auxDeclToFullName_3790_ = lean_ctor_get(v_lctx_3787_, 2);
v_currNamespace_3791_ = lean_ctor_get(v_toCold_3788_, 4);
v_view_3792_ = l_Lean_extractMacroScopes(v_n_3779_);
v_name_3793_ = lean_ctor_get(v_view_3792_, 0);
lean_inc(v_name_3793_);
lean_inc_ref(v_decls_3789_);
lean_inc(v_currNamespace_3791_);
lean_inc(v_auxDeclToFullName_3790_);
v_findLocalDecl_x3f_3794_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3794_, 0, v_auxDeclToFullName_3790_);
lean_closure_set(v_findLocalDecl_x3f_3794_, 1, v_currNamespace_3791_);
lean_closure_set(v_findLocalDecl_x3f_3794_, 2, v_decls_3789_);
v___x_3795_ = lean_box(0);
v___x_3796_ = 0;
v___x_3797_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3792_, v_findLocalDecl_x3f_3794_, v_name_3793_, v___x_3795_, v___x_3796_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
lean_dec_ref(v_view_3792_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3807_, lean_object* v_b_3808_){
_start:
{
if (lean_obj_tag(v_as_x27_3807_) == 0)
{
lean_object* v___x_3810_; 
v___x_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3810_, 0, v_b_3808_);
return v___x_3810_;
}
else
{
lean_object* v_head_3811_; lean_object* v_tail_3812_; lean_object* v_config_3813_; lean_object* v_extensions_3814_; lean_object* v_extra_3815_; lean_object* v_extraInj_3816_; lean_object* v_extraFacts_3817_; lean_object* v_symPrios_3818_; lean_object* v_norm_3819_; lean_object* v_normProcs_3820_; lean_object* v_anchorRefs_x3f_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3830_; 
v_head_3811_ = lean_ctor_get(v_as_x27_3807_, 0);
v_tail_3812_ = lean_ctor_get(v_as_x27_3807_, 1);
v_config_3813_ = lean_ctor_get(v_b_3808_, 0);
v_extensions_3814_ = lean_ctor_get(v_b_3808_, 1);
v_extra_3815_ = lean_ctor_get(v_b_3808_, 2);
v_extraInj_3816_ = lean_ctor_get(v_b_3808_, 3);
v_extraFacts_3817_ = lean_ctor_get(v_b_3808_, 4);
v_symPrios_3818_ = lean_ctor_get(v_b_3808_, 5);
v_norm_3819_ = lean_ctor_get(v_b_3808_, 6);
v_normProcs_3820_ = lean_ctor_get(v_b_3808_, 7);
v_anchorRefs_x3f_3821_ = lean_ctor_get(v_b_3808_, 8);
v_isSharedCheck_3830_ = !lean_is_exclusive(v_b_3808_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3823_ = v_b_3808_;
v_isShared_3824_ = v_isSharedCheck_3830_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_anchorRefs_x3f_3821_);
lean_inc(v_normProcs_3820_);
lean_inc(v_norm_3819_);
lean_inc(v_symPrios_3818_);
lean_inc(v_extraFacts_3817_);
lean_inc(v_extraInj_3816_);
lean_inc(v_extra_3815_);
lean_inc(v_extensions_3814_);
lean_inc(v_config_3813_);
lean_dec(v_b_3808_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3830_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3825_; lean_object* v___x_3827_; 
lean_inc(v_head_3811_);
v___x_3825_ = l_Lean_PersistentArray_push___redArg(v_extra_3815_, v_head_3811_);
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 2, v___x_3825_);
v___x_3827_ = v___x_3823_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_config_3813_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_extensions_3814_);
lean_ctor_set(v_reuseFailAlloc_3829_, 2, v___x_3825_);
lean_ctor_set(v_reuseFailAlloc_3829_, 3, v_extraInj_3816_);
lean_ctor_set(v_reuseFailAlloc_3829_, 4, v_extraFacts_3817_);
lean_ctor_set(v_reuseFailAlloc_3829_, 5, v_symPrios_3818_);
lean_ctor_set(v_reuseFailAlloc_3829_, 6, v_norm_3819_);
lean_ctor_set(v_reuseFailAlloc_3829_, 7, v_normProcs_3820_);
lean_ctor_set(v_reuseFailAlloc_3829_, 8, v_anchorRefs_x3f_3821_);
v___x_3827_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
v_as_x27_3807_ = v_tail_3812_;
v_b_3808_ = v___x_3827_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3831_, lean_object* v_b_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3831_, v_b_3832_);
lean_dec(v_as_x27_3831_);
return v_res_3834_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3836_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3837_ = l_Lean_stringToMessageData(v___x_3836_);
return v___x_3837_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3839_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3840_ = l_Lean_stringToMessageData(v___x_3839_);
return v___x_3840_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3843_ = l_Lean_stringToMessageData(v___x_3842_);
return v___x_3843_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3846_ = l_Lean_stringToMessageData(v___x_3845_);
return v___x_3846_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3849_ = l_Lean_stringToMessageData(v___x_3848_);
return v___x_3849_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3852_ = l_Lean_stringToMessageData(v___x_3851_);
return v___x_3852_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3855_ = l_Lean_stringToMessageData(v___x_3854_);
return v___x_3855_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3858_ = l_Lean_stringToMessageData(v___x_3857_);
return v___x_3858_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3861_ = l_Lean_stringToMessageData(v___x_3860_);
return v___x_3861_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3864_ = l_Lean_stringToMessageData(v___x_3863_);
return v___x_3864_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3866_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3867_ = l_Lean_stringToMessageData(v___x_3866_);
return v___x_3867_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23(void){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22));
v___x_3870_ = l_Lean_stringToMessageData(v___x_3869_);
return v___x_3870_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25(void){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24));
v___x_3873_ = l_Lean_stringToMessageData(v___x_3872_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3874_, lean_object* v_p_3875_, lean_object* v_mod_x3f_3876_, lean_object* v_id_3877_, uint8_t v_minIndexable_3878_, uint8_t v_only_3879_, uint8_t v_incremental_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_){
_start:
{
uint8_t v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_4012_; uint8_t v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v_a_4064_; lean_object* v___y_4289_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4300_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4301_ = lean_box(0);
lean_inc(v_id_3877_);
v___x_4302_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3877_, v___x_4301_, v_a_3885_, v_a_3886_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4302_, 1);
v_a_4064_ = v_a_4303_;
goto v___jp_4063_;
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4378_; 
v_a_4304_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4306_ = v___x_4302_;
v_isShared_4307_ = v_isSharedCheck_4378_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4302_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4378_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
uint8_t v___y_4309_; uint8_t v___x_4376_; 
v___x_4376_ = l_Lean_Exception_isInterrupt(v_a_4304_);
if (v___x_4376_ == 0)
{
uint8_t v___x_4377_; 
lean_inc(v_a_4304_);
v___x_4377_ = l_Lean_Exception_isRuntime(v_a_4304_);
v___y_4309_ = v___x_4377_;
goto v___jp_4308_;
}
else
{
v___y_4309_ = v___x_4376_;
goto v___jp_4308_;
}
v___jp_4308_:
{
if (v___y_4309_ == 0)
{
lean_object* v___x_4310_; lean_object* v___x_4311_; 
lean_del_object(v___x_4306_);
v___x_4310_ = l_Lean_TSyntax_getId(v_id_3877_);
lean_inc(v___x_4310_);
v___x_4311_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4310_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4311_, 1);
if (lean_obj_tag(v_a_4312_) == 0)
{
lean_object* v___x_4313_; 
v___x_4313_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_4310_, v_a_3885_, v_a_3886_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4342_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4316_ = v___x_4313_;
v_isShared_4317_ = v_isSharedCheck_4342_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4313_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4342_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
if (lean_obj_tag(v_a_4314_) == 1)
{
lean_del_object(v___x_4316_);
lean_dec(v_a_4304_);
if (lean_obj_tag(v_mod_x3f_3876_) == 1)
{
lean_object* v_val_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec_ref_known(v_a_4314_, 1);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_val_4318_ = lean_ctor_get(v_mod_x3f_3876_, 0);
lean_inc(v_val_4318_);
lean_dec_ref_known(v_mod_x3f_3876_, 1);
v___x_4319_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4320_ = l_Lean_MessageData_ofName(v___x_4310_);
v___x_4321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4319_);
lean_ctor_set(v___x_4321_, 1, v___x_4320_);
v___x_4322_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4321_);
lean_ctor_set(v___x_4323_, 1, v___x_4322_);
v___x_4324_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4318_, v___x_4323_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
lean_dec(v_val_4318_);
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4324_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4324_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
else
{
lean_object* v_val_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
lean_dec(v___x_4310_);
v_val_4333_ = lean_ctor_get(v_a_4314_, 0);
lean_inc(v_val_4333_);
lean_dec_ref_known(v_a_4314_, 1);
v___x_4334_ = lean_box(0);
lean_inc_ref(v_params_3874_);
v___x_4335_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3874_, v_val_4333_, v___x_4300_, v___y_4309_, v___x_4334_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
lean_dec(v_val_4333_);
v___y_4289_ = v___x_4335_;
goto v___jp_4288_;
}
}
else
{
lean_object* v___x_4336_; uint8_t v___x_4337_; 
lean_dec(v_a_4314_);
v___x_4336_ = l_Lean_Name_getPrefix(v___x_4310_);
lean_dec(v___x_4310_);
v___x_4337_ = l_Lean_Name_isAnonymous(v___x_4336_);
lean_dec(v___x_4336_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; 
lean_del_object(v___x_4316_);
lean_dec(v_a_4304_);
v___x_4338_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3874_, v_p_3875_, v_mod_x3f_3876_, v_id_3877_, v_minIndexable_3878_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
return v___x_4338_;
}
else
{
lean_object* v___x_4340_; 
lean_dec(v_id_3877_);
lean_dec(v_mod_x3f_3876_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
if (v_isShared_4317_ == 0)
{
lean_ctor_set_tag(v___x_4316_, 1);
lean_ctor_set(v___x_4316_, 0, v_a_4304_);
v___x_4340_ = v___x_4316_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4304_);
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
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec(v___x_4310_);
lean_dec(v_a_4304_);
lean_dec(v_id_3877_);
lean_dec(v_mod_x3f_3876_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_a_4343_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4313_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4313_);
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
else
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec_ref_known(v_a_4312_, 1);
lean_dec(v___x_4310_);
lean_dec(v_a_4304_);
lean_dec(v_mod_x3f_3876_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v___x_4351_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23);
lean_inc(v_id_3877_);
v___x_4352_ = l_Lean_MessageData_ofSyntax(v_id_3877_);
v___x_4353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4351_);
lean_ctor_set(v___x_4353_, 1, v___x_4352_);
v___x_4354_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25);
v___x_4355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4353_);
lean_ctor_set(v___x_4355_, 1, v___x_4354_);
v___x_4356_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3877_, v___x_4355_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
lean_dec(v_id_3877_);
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4356_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4356_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
lean_dec(v___x_4310_);
lean_dec(v_a_4304_);
lean_dec(v_id_3877_);
lean_dec(v_mod_x3f_3876_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_a_4365_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4311_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4311_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
else
{
lean_object* v___x_4374_; 
lean_dec(v_id_3877_);
lean_dec(v_mod_x3f_3876_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
if (v_isShared_4307_ == 0)
{
v___x_4374_ = v___x_4306_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_a_4304_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
}
}
}
v___jp_3888_:
{
uint8_t v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = 0;
lean_inc(v___y_3890_);
v___x_3898_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3890_, v___x_3897_, v___y_3895_, v___y_3896_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref_known(v___x_3898_, 1);
if (lean_obj_tag(v_a_3899_) == 1)
{
lean_object* v_val_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
lean_dec(v___y_3890_);
v_val_3900_ = lean_ctor_get(v_a_3899_, 0);
lean_inc_n(v_val_3900_, 2);
lean_dec_ref_known(v_a_3899_, 1);
v___x_3901_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3874_, v_val_3900_, v___x_3897_);
v___x_3902_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3900_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3913_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3905_ = v___x_3902_;
v_isShared_3906_ = v_isSharedCheck_3913_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3913_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
if (lean_obj_tag(v_a_3903_) == 1)
{
lean_object* v_val_3907_; lean_object* v_ctors_3908_; lean_object* v___x_3909_; 
lean_del_object(v___x_3905_);
v_val_3907_ = lean_ctor_get(v_a_3903_, 0);
lean_inc(v_val_3907_);
lean_dec_ref_known(v_a_3903_, 1);
v_ctors_3908_ = lean_ctor_get(v_val_3907_, 4);
lean_inc(v_ctors_3908_);
lean_dec(v_val_3907_);
v___x_3909_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3875_, v_id_3877_, v_minIndexable_3878_, v_ctors_3908_, v___x_3901_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
lean_dec(v_ctors_3908_);
lean_dec(v_p_3875_);
return v___x_3909_;
}
else
{
lean_object* v___x_3911_; 
lean_dec(v_a_3903_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v___x_3901_);
v___x_3911_ = v___x_3905_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3901_);
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
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec_ref(v___x_3901_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
v_a_3914_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3902_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3902_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
else
{
lean_object* v_symPrios_3922_; lean_object* v___x_3923_; 
lean_dec(v_a_3899_);
v_symPrios_3922_ = lean_ctor_get(v_params_3874_, 5);
lean_inc_ref(v_symPrios_3922_);
lean_inc(v___y_3890_);
v___x_3923_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(v___y_3890_, v_symPrios_3922_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; uint8_t v___x_3925_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v___x_3925_ = lean_unbox(v_a_3924_);
lean_dec(v_a_3924_);
if (v___x_3925_ == 0)
{
lean_object* v_toCold_3926_; lean_object* v_currRecDepth_3927_; lean_object* v_ref_3928_; uint16_t v_optionFlags_3929_; uint8_t v_suppressElabErrors_3930_; uint8_t v_isRecordingDeps_3931_; lean_object* v___x_3932_; lean_object* v_ref_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v_toCold_3926_ = lean_ctor_get(v___y_3895_, 0);
v_currRecDepth_3927_ = lean_ctor_get(v___y_3895_, 1);
v_ref_3928_ = lean_ctor_get(v___y_3895_, 2);
v_optionFlags_3929_ = lean_ctor_get_uint16(v___y_3895_, sizeof(void*)*3);
v_suppressElabErrors_3930_ = lean_ctor_get_uint8(v___y_3895_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3931_ = lean_ctor_get_uint8(v___y_3895_, sizeof(void*)*3 + 3);
v___x_3932_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl___closed__1));
v_ref_3933_ = l_Lean_replaceRef(v_p_3875_, v_ref_3928_);
lean_dec(v_p_3875_);
lean_inc(v_currRecDepth_3927_);
lean_inc_ref(v_toCold_3926_);
v___x_3934_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3934_, 0, v_toCold_3926_);
lean_ctor_set(v___x_3934_, 1, v_currRecDepth_3927_);
lean_ctor_set(v___x_3934_, 2, v_ref_3933_);
lean_ctor_set_uint16(v___x_3934_, sizeof(void*)*3, v_optionFlags_3929_);
lean_ctor_set_uint8(v___x_3934_, sizeof(void*)*3 + 2, v_suppressElabErrors_3930_);
lean_ctor_set_uint8(v___x_3934_, sizeof(void*)*3 + 3, v_isRecordingDeps_3931_);
v___x_3935_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3874_, v_id_3877_, v___y_3890_, v___x_3932_, v_minIndexable_3878_, v___y_3889_, v___y_3889_, v___y_3893_, v___y_3894_, v___x_3934_, v___y_3896_);
lean_dec_ref_known(v___x_3934_, 3);
return v___x_3935_;
}
else
{
lean_object* v_toCold_3936_; lean_object* v_currRecDepth_3937_; lean_object* v_ref_3938_; uint16_t v_optionFlags_3939_; uint8_t v_suppressElabErrors_3940_; uint8_t v_isRecordingDeps_3941_; lean_object* v_ref_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
lean_dec(v_id_3877_);
v_toCold_3936_ = lean_ctor_get(v___y_3895_, 0);
v_currRecDepth_3937_ = lean_ctor_get(v___y_3895_, 1);
v_ref_3938_ = lean_ctor_get(v___y_3895_, 2);
v_optionFlags_3939_ = lean_ctor_get_uint16(v___y_3895_, sizeof(void*)*3);
v_suppressElabErrors_3940_ = lean_ctor_get_uint8(v___y_3895_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3941_ = lean_ctor_get_uint8(v___y_3895_, sizeof(void*)*3 + 3);
v_ref_3942_ = l_Lean_replaceRef(v_p_3875_, v_ref_3938_);
lean_dec(v_p_3875_);
lean_inc(v_currRecDepth_3937_);
lean_inc_ref(v_toCold_3936_);
v___x_3943_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3943_, 0, v_toCold_3936_);
lean_ctor_set(v___x_3943_, 1, v_currRecDepth_3937_);
lean_ctor_set(v___x_3943_, 2, v_ref_3942_);
lean_ctor_set_uint16(v___x_3943_, sizeof(void*)*3, v_optionFlags_3939_);
lean_ctor_set_uint8(v___x_3943_, sizeof(void*)*3 + 2, v_suppressElabErrors_3940_);
lean_ctor_set_uint8(v___x_3943_, sizeof(void*)*3 + 3, v_isRecordingDeps_3941_);
v___x_3944_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_addFact(v_params_3874_, v___y_3890_, v_minIndexable_3878_, v___y_3893_, v___y_3894_, v___x_3943_, v___y_3896_);
lean_dec_ref_known(v___x_3943_, 3);
return v___x_3944_;
}
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec(v___y_3890_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_a_3945_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3923_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3923_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
}
else
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
lean_dec(v___y_3890_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_a_3953_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3898_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3898_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
}
v___jp_3961_:
{
lean_object* v___x_3970_; 
v___x_3970_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3878_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
lean_dec_ref_known(v___x_3970_, 1);
v___x_3971_ = l_Lean_Meta_Grind_grindExt;
v___x_3972_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3971_, v___y_3969_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref_known(v___x_3972_, 1);
lean_inc(v___y_3962_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___y_3962_);
v___x_3975_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3973_, v___x_3974_);
lean_dec_ref_known(v___x_3974_, 1);
lean_dec(v_a_3973_);
v___x_3976_ = lean_box(0);
v___x_3977_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3963_, v___x_3975_, v___x_3976_);
lean_dec(v___y_3963_);
v___x_3978_ = l_List_isEmpty___redArg(v___x_3977_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; 
lean_dec(v___y_3962_);
lean_dec(v_p_3875_);
v___x_3979_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3977_, v_params_3874_);
lean_dec(v___x_3977_);
return v___x_3979_;
}
else
{
lean_object* v___x_3980_; uint8_t v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_dec(v___x_3977_);
lean_dec_ref(v_params_3874_);
v___x_3980_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3981_ = 0;
v___x_3982_ = l_Lean_MessageData_ofConstName(v___y_3962_, v___x_3981_);
v___x_3983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3980_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
v___x_3984_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3983_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3875_, v___x_3985_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
lean_dec(v_p_3875_);
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3986_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3986_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
lean_dec(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_a_3995_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3972_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3972_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_a_4003_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3970_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3970_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
v___jp_4011_:
{
lean_object* v___x_4018_; 
v___x_4018_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3878_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_toCold_4019_; lean_object* v_currRecDepth_4020_; lean_object* v_ref_4021_; uint16_t v_optionFlags_4022_; uint8_t v_suppressElabErrors_4023_; uint8_t v_isRecordingDeps_4024_; lean_object* v_ref_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
lean_dec_ref_known(v___x_4018_, 1);
v_toCold_4019_ = lean_ctor_get(v___y_4016_, 0);
v_currRecDepth_4020_ = lean_ctor_get(v___y_4016_, 1);
v_ref_4021_ = lean_ctor_get(v___y_4016_, 2);
v_optionFlags_4022_ = lean_ctor_get_uint16(v___y_4016_, sizeof(void*)*3);
v_suppressElabErrors_4023_ = lean_ctor_get_uint8(v___y_4016_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4024_ = lean_ctor_get_uint8(v___y_4016_, sizeof(void*)*3 + 3);
v_ref_4025_ = l_Lean_replaceRef(v_p_3875_, v_ref_4021_);
lean_dec(v_p_3875_);
lean_inc(v_currRecDepth_4020_);
lean_inc_ref(v_toCold_4019_);
v___x_4026_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4026_, 0, v_toCold_4019_);
lean_ctor_set(v___x_4026_, 1, v_currRecDepth_4020_);
lean_ctor_set(v___x_4026_, 2, v_ref_4025_);
lean_ctor_set_uint16(v___x_4026_, sizeof(void*)*3, v_optionFlags_4022_);
lean_ctor_set_uint8(v___x_4026_, sizeof(void*)*3 + 2, v_suppressElabErrors_4023_);
lean_ctor_set_uint8(v___x_4026_, sizeof(void*)*3 + 3, v_isRecordingDeps_4024_);
lean_inc(v___y_4012_);
v___x_4027_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_4012_, v___y_4013_, v___x_4026_, v___y_4017_);
lean_dec_ref_known(v___x_4026_, 3);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4035_; 
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4035_ == 0)
{
lean_object* v_unused_4036_; 
v_unused_4036_ = lean_ctor_get(v___x_4027_, 0);
lean_dec(v_unused_4036_);
v___x_4029_ = v___x_4027_;
v_isShared_4030_ = v_isSharedCheck_4035_;
goto v_resetjp_4028_;
}
else
{
lean_dec(v___x_4027_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4035_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4031_; lean_object* v___x_4033_; 
v___x_4031_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3874_, v___y_4012_, v___y_4013_);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 0, v___x_4031_);
v___x_4033_ = v___x_4029_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_dec(v___y_4012_);
lean_dec_ref(v_params_3874_);
v_a_4037_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4027_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4027_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec(v___y_4012_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_a_4045_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4018_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4018_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
v___jp_4053_:
{
lean_object* v_ctors_4061_; lean_object* v___x_4062_; 
v_ctors_4061_ = lean_ctor_get(v___y_4054_, 4);
lean_inc(v_ctors_4061_);
lean_dec_ref(v___y_4054_);
v___x_4062_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3875_, v_id_3877_, v_minIndexable_3878_, v_ctors_4061_, v_params_3874_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
lean_dec(v_ctors_4061_);
lean_dec(v_p_3875_);
return v___x_4062_;
}
v___jp_4063_:
{
uint8_t v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = 1;
lean_inc(v_a_4064_);
v___x_4066_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4064_, v___x_4065_, v_a_3881_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_dec_ref_known(v___x_4066_, 1);
if (lean_obj_tag(v_mod_x3f_3876_) == 1)
{
lean_object* v_val_4067_; lean_object* v___x_4068_; 
v_val_4067_ = lean_ctor_get(v_mod_x3f_3876_, 0);
lean_inc(v_val_4067_);
lean_dec_ref_known(v_mod_x3f_3876_, 1);
v___x_4068_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_4067_, v_a_3885_, v_a_3886_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4271_; 
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4071_ = v___x_4068_;
v_isShared_4072_ = v_isSharedCheck_4271_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4068_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4271_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
switch(lean_obj_tag(v_a_4069_))
{
case 0:
{
lean_object* v_k_4073_; 
lean_del_object(v___x_4071_);
v_k_4073_ = lean_ctor_get(v_a_4069_, 0);
lean_inc(v_k_4073_);
lean_dec_ref_known(v_a_4069_, 1);
if (lean_obj_tag(v_k_4073_) == 9)
{
lean_dec(v_id_3877_);
if (v_only_3879_ == 0)
{
lean_object* v_toCold_4074_; lean_object* v_currRecDepth_4075_; lean_object* v_ref_4076_; uint16_t v_optionFlags_4077_; uint8_t v_suppressElabErrors_4078_; uint8_t v_isRecordingDeps_4079_; lean_object* v_ref_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v_toCold_4074_ = lean_ctor_get(v_a_3885_, 0);
v_currRecDepth_4075_ = lean_ctor_get(v_a_3885_, 1);
v_ref_4076_ = lean_ctor_get(v_a_3885_, 2);
v_optionFlags_4077_ = lean_ctor_get_uint16(v_a_3885_, sizeof(void*)*3);
v_suppressElabErrors_4078_ = lean_ctor_get_uint8(v_a_3885_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4079_ = lean_ctor_get_uint8(v_a_3885_, sizeof(void*)*3 + 3);
v_ref_4080_ = l_Lean_replaceRef(v_p_3875_, v_ref_4076_);
lean_inc(v_currRecDepth_4075_);
lean_inc_ref(v_toCold_4074_);
v___x_4081_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4081_, 0, v_toCold_4074_);
lean_ctor_set(v___x_4081_, 1, v_currRecDepth_4075_);
lean_ctor_set(v___x_4081_, 2, v_ref_4080_);
lean_ctor_set_uint16(v___x_4081_, sizeof(void*)*3, v_optionFlags_4077_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*3 + 2, v_suppressElabErrors_4078_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*3 + 3, v_isRecordingDeps_4079_);
v___x_4082_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_4081_, v_a_3886_);
lean_dec_ref_known(v___x_4081_, 3);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_dec_ref_known(v___x_4082_, 1);
v___y_3962_ = v_a_4064_;
v___y_3963_ = v_k_4073_;
v___y_3964_ = v_a_3881_;
v___y_3965_ = v_a_3882_;
v___y_3966_ = v_a_3883_;
v___y_3967_ = v_a_3884_;
v___y_3968_ = v_a_3885_;
v___y_3969_ = v_a_3886_;
goto v___jp_3961_;
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec(v_a_4064_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4082_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4082_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
else
{
v___y_3962_ = v_a_4064_;
v___y_3963_ = v_k_4073_;
v___y_3964_ = v_a_3881_;
v___y_3965_ = v_a_3882_;
v___y_3966_ = v_a_3883_;
v___y_3967_ = v_a_3884_;
v___y_3968_ = v_a_3885_;
v___y_3969_ = v_a_3886_;
goto v___jp_3961_;
}
}
else
{
lean_object* v_toCold_4091_; lean_object* v_currRecDepth_4092_; lean_object* v_ref_4093_; uint16_t v_optionFlags_4094_; uint8_t v_suppressElabErrors_4095_; uint8_t v_isRecordingDeps_4096_; uint8_t v___x_4097_; lean_object* v_ref_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v_toCold_4091_ = lean_ctor_get(v_a_3885_, 0);
v_currRecDepth_4092_ = lean_ctor_get(v_a_3885_, 1);
v_ref_4093_ = lean_ctor_get(v_a_3885_, 2);
v_optionFlags_4094_ = lean_ctor_get_uint16(v_a_3885_, sizeof(void*)*3);
v_suppressElabErrors_4095_ = lean_ctor_get_uint8(v_a_3885_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4096_ = lean_ctor_get_uint8(v_a_3885_, sizeof(void*)*3 + 3);
v___x_4097_ = 0;
v_ref_4098_ = l_Lean_replaceRef(v_p_3875_, v_ref_4093_);
lean_dec(v_p_3875_);
lean_inc(v_currRecDepth_4092_);
lean_inc_ref(v_toCold_4091_);
v___x_4099_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4099_, 0, v_toCold_4091_);
lean_ctor_set(v___x_4099_, 1, v_currRecDepth_4092_);
lean_ctor_set(v___x_4099_, 2, v_ref_4098_);
lean_ctor_set_uint16(v___x_4099_, sizeof(void*)*3, v_optionFlags_4094_);
lean_ctor_set_uint8(v___x_4099_, sizeof(void*)*3 + 2, v_suppressElabErrors_4095_);
lean_ctor_set_uint8(v___x_4099_, sizeof(void*)*3 + 3, v_isRecordingDeps_4096_);
v___x_4100_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3874_, v_id_3877_, v_a_4064_, v_k_4073_, v_minIndexable_3878_, v___x_4097_, v___x_4065_, v_a_3883_, v_a_3884_, v___x_4099_, v_a_3886_);
lean_dec_ref_known(v___x_4099_, 3);
return v___x_4100_;
}
}
case 1:
{
lean_del_object(v___x_4071_);
lean_dec(v_id_3877_);
if (v_incremental_3880_ == 0)
{
uint8_t v_eager_4101_; 
v_eager_4101_ = lean_ctor_get_uint8(v_a_4069_, 0);
lean_dec_ref_known(v_a_4069_, 0);
v___y_4012_ = v_a_4064_;
v___y_4013_ = v_eager_4101_;
v___y_4014_ = v_a_3883_;
v___y_4015_ = v_a_3884_;
v___y_4016_ = v_a_3885_;
v___y_4017_ = v_a_3886_;
goto v___jp_4011_;
}
else
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec_ref_known(v_a_4069_, 0);
lean_dec(v_a_4064_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v___x_4102_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_4103_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4102_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4103_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4103_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
case 2:
{
uint8_t v___x_4112_; lean_object* v___x_4113_; 
lean_del_object(v___x_4071_);
v___x_4112_ = 0;
lean_inc(v_a_4064_);
v___x_4113_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_4064_, v___x_4112_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___x_4113_, 1);
if (lean_obj_tag(v_a_4114_) == 1)
{
lean_dec(v_a_4064_);
if (v_incremental_3880_ == 0)
{
lean_object* v_val_4115_; 
v_val_4115_ = lean_ctor_get(v_a_4114_, 0);
lean_inc(v_val_4115_);
lean_dec_ref_known(v_a_4114_, 1);
v___y_4054_ = v_val_4115_;
v___y_4055_ = v_a_3881_;
v___y_4056_ = v_a_3882_;
v___y_4057_ = v_a_3883_;
v___y_4058_ = v_a_3884_;
v___y_4059_ = v_a_3885_;
v___y_4060_ = v_a_3886_;
goto v___jp_4053_;
}
else
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec_ref_known(v_a_4114_, 1);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v___x_4116_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_4117_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4116_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4117_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
else
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
lean_dec(v_a_4114_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v___x_4126_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_4127_ = l_Lean_MessageData_ofConstName(v_a_4064_, v___x_4112_);
v___x_4128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4126_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
v___x_4129_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_4130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4128_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
v___x_4131_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4130_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4131_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4131_);
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
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec(v_a_4064_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_a_4140_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4113_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4113_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
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
case 3:
{
lean_del_object(v___x_4071_);
v___y_3889_ = v___x_4065_;
v___y_3890_ = v_a_4064_;
v___y_3891_ = v_a_3881_;
v___y_3892_ = v_a_3882_;
v___y_3893_ = v_a_3883_;
v___y_3894_ = v_a_3884_;
v___y_3895_ = v_a_3885_;
v___y_3896_ = v_a_3886_;
goto v___jp_3888_;
}
case 4:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_del_object(v___x_4071_);
lean_dec(v_a_4064_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v___x_4148_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_4149_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4148_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4149_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4149_);
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
case 5:
{
lean_object* v_prio_4158_; lean_object* v___x_4159_; 
lean_del_object(v___x_4071_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
v_prio_4158_ = lean_ctor_get(v_a_4069_, 0);
lean_inc(v_prio_4158_);
lean_dec_ref_known(v_a_4069_, 1);
v___x_4159_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3878_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4183_; 
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4183_ == 0)
{
lean_object* v_unused_4184_; 
v_unused_4184_ = lean_ctor_get(v___x_4159_, 0);
lean_dec(v_unused_4184_);
v___x_4161_ = v___x_4159_;
v_isShared_4162_ = v_isSharedCheck_4183_;
goto v_resetjp_4160_;
}
else
{
lean_dec(v___x_4159_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4183_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v_config_4163_; lean_object* v_extensions_4164_; lean_object* v_extra_4165_; lean_object* v_extraInj_4166_; lean_object* v_extraFacts_4167_; lean_object* v_symPrios_4168_; lean_object* v_norm_4169_; lean_object* v_normProcs_4170_; lean_object* v_anchorRefs_x3f_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4182_; 
v_config_4163_ = lean_ctor_get(v_params_3874_, 0);
v_extensions_4164_ = lean_ctor_get(v_params_3874_, 1);
v_extra_4165_ = lean_ctor_get(v_params_3874_, 2);
v_extraInj_4166_ = lean_ctor_get(v_params_3874_, 3);
v_extraFacts_4167_ = lean_ctor_get(v_params_3874_, 4);
v_symPrios_4168_ = lean_ctor_get(v_params_3874_, 5);
v_norm_4169_ = lean_ctor_get(v_params_3874_, 6);
v_normProcs_4170_ = lean_ctor_get(v_params_3874_, 7);
v_anchorRefs_x3f_4171_ = lean_ctor_get(v_params_3874_, 8);
v_isSharedCheck_4182_ = !lean_is_exclusive(v_params_3874_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4173_ = v_params_3874_;
v_isShared_4174_ = v_isSharedCheck_4182_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_anchorRefs_x3f_4171_);
lean_inc(v_normProcs_4170_);
lean_inc(v_norm_4169_);
lean_inc(v_symPrios_4168_);
lean_inc(v_extraFacts_4167_);
lean_inc(v_extraInj_4166_);
lean_inc(v_extra_4165_);
lean_inc(v_extensions_4164_);
lean_inc(v_config_4163_);
lean_dec(v_params_3874_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4182_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4175_; lean_object* v___x_4177_; 
v___x_4175_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_4168_, v_a_4064_, v_prio_4158_);
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 5, v___x_4175_);
v___x_4177_ = v___x_4173_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_config_4163_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v_extensions_4164_);
lean_ctor_set(v_reuseFailAlloc_4181_, 2, v_extra_4165_);
lean_ctor_set(v_reuseFailAlloc_4181_, 3, v_extraInj_4166_);
lean_ctor_set(v_reuseFailAlloc_4181_, 4, v_extraFacts_4167_);
lean_ctor_set(v_reuseFailAlloc_4181_, 5, v___x_4175_);
lean_ctor_set(v_reuseFailAlloc_4181_, 6, v_norm_4169_);
lean_ctor_set(v_reuseFailAlloc_4181_, 7, v_normProcs_4170_);
lean_ctor_set(v_reuseFailAlloc_4181_, 8, v_anchorRefs_x3f_4171_);
v___x_4177_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
lean_object* v___x_4179_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4177_);
v___x_4179_ = v___x_4161_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4177_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
lean_dec(v_prio_4158_);
lean_dec(v_a_4064_);
lean_dec_ref(v_params_3874_);
v_a_4185_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_4159_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4159_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
case 6:
{
lean_object* v___x_4193_; 
lean_del_object(v___x_4071_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
v___x_4193_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_4064_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4218_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4196_ = v___x_4193_;
v_isShared_4197_ = v_isSharedCheck_4218_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4193_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4218_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v_config_4198_; lean_object* v_extensions_4199_; lean_object* v_extra_4200_; lean_object* v_extraInj_4201_; lean_object* v_extraFacts_4202_; lean_object* v_symPrios_4203_; lean_object* v_norm_4204_; lean_object* v_normProcs_4205_; lean_object* v_anchorRefs_x3f_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4217_; 
v_config_4198_ = lean_ctor_get(v_params_3874_, 0);
v_extensions_4199_ = lean_ctor_get(v_params_3874_, 1);
v_extra_4200_ = lean_ctor_get(v_params_3874_, 2);
v_extraInj_4201_ = lean_ctor_get(v_params_3874_, 3);
v_extraFacts_4202_ = lean_ctor_get(v_params_3874_, 4);
v_symPrios_4203_ = lean_ctor_get(v_params_3874_, 5);
v_norm_4204_ = lean_ctor_get(v_params_3874_, 6);
v_normProcs_4205_ = lean_ctor_get(v_params_3874_, 7);
v_anchorRefs_x3f_4206_ = lean_ctor_get(v_params_3874_, 8);
v_isSharedCheck_4217_ = !lean_is_exclusive(v_params_3874_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4208_ = v_params_3874_;
v_isShared_4209_ = v_isSharedCheck_4217_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_anchorRefs_x3f_4206_);
lean_inc(v_normProcs_4205_);
lean_inc(v_norm_4204_);
lean_inc(v_symPrios_4203_);
lean_inc(v_extraFacts_4202_);
lean_inc(v_extraInj_4201_);
lean_inc(v_extra_4200_);
lean_inc(v_extensions_4199_);
lean_inc(v_config_4198_);
lean_dec(v_params_3874_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4217_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4210_; lean_object* v___x_4212_; 
v___x_4210_ = l_Lean_PersistentArray_push___redArg(v_extraInj_4201_, v_a_4194_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 3, v___x_4210_);
v___x_4212_ = v___x_4208_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_config_4198_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v_extensions_4199_);
lean_ctor_set(v_reuseFailAlloc_4216_, 2, v_extra_4200_);
lean_ctor_set(v_reuseFailAlloc_4216_, 3, v___x_4210_);
lean_ctor_set(v_reuseFailAlloc_4216_, 4, v_extraFacts_4202_);
lean_ctor_set(v_reuseFailAlloc_4216_, 5, v_symPrios_4203_);
lean_ctor_set(v_reuseFailAlloc_4216_, 6, v_norm_4204_);
lean_ctor_set(v_reuseFailAlloc_4216_, 7, v_normProcs_4205_);
lean_ctor_set(v_reuseFailAlloc_4216_, 8, v_anchorRefs_x3f_4206_);
v___x_4212_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
lean_object* v___x_4214_; 
if (v_isShared_4197_ == 0)
{
lean_ctor_set(v___x_4196_, 0, v___x_4212_);
v___x_4214_ = v___x_4196_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v___x_4212_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
lean_dec_ref(v_params_3874_);
v_a_4219_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4193_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4193_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
case 7:
{
lean_object* v___x_4227_; lean_object* v___x_4229_; 
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
v___x_4227_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3874_, v_a_4064_);
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 0, v___x_4227_);
v___x_4229_ = v___x_4071_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
case 8:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_dec_ref_known(v_a_4069_, 0);
lean_del_object(v___x_4071_);
lean_dec(v_a_4064_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v___x_4231_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_4232_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4231_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4232_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4232_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
case 9:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_del_object(v___x_4071_);
lean_dec(v_a_4064_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v___x_4241_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_4242_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4241_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4242_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4242_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
case 10:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec_ref_known(v_a_4069_, 0);
lean_del_object(v___x_4071_);
lean_dec(v_a_4064_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v___x_4251_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_4252_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4251_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
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
default: 
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_del_object(v___x_4071_);
lean_dec(v_a_4064_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v___x_4261_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
v___x_4262_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_4261_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4262_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4262_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
}
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
lean_dec(v_a_4064_);
lean_dec(v_id_3877_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_a_4272_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4068_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4068_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_3876_);
v___y_3889_ = v___x_4065_;
v___y_3890_ = v_a_4064_;
v___y_3891_ = v_a_3881_;
v___y_3892_ = v_a_3882_;
v___y_3893_ = v_a_3883_;
v___y_3894_ = v_a_3884_;
v___y_3895_ = v_a_3885_;
v___y_3896_ = v_a_3886_;
goto v___jp_3888_;
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec(v_a_4064_);
lean_dec(v_id_3877_);
lean_dec(v_mod_x3f_3876_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_a_4280_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4066_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4066_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
v___jp_4288_:
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4299_; 
v_a_4290_ = lean_ctor_get(v___y_4289_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___y_4289_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4292_ = v___y_4289_;
v_isShared_4293_ = v_isSharedCheck_4299_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___y_4289_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4299_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
if (lean_obj_tag(v_a_4290_) == 0)
{
lean_object* v_a_4294_; lean_object* v___x_4296_; 
lean_dec(v_id_3877_);
lean_dec(v_mod_x3f_3876_);
lean_dec(v_p_3875_);
lean_dec_ref(v_params_3874_);
v_a_4294_ = lean_ctor_get(v_a_4290_, 0);
lean_inc(v_a_4294_);
lean_dec_ref_known(v_a_4290_, 1);
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v_a_4294_);
v___x_4296_ = v___x_4292_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4294_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
else
{
lean_object* v_a_4298_; 
lean_del_object(v___x_4292_);
v_a_4298_ = lean_ctor_get(v_a_4290_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v_a_4290_, 1);
v_a_4064_ = v_a_4298_;
goto v___jp_4063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4379_, lean_object* v_p_4380_, lean_object* v_mod_x3f_4381_, lean_object* v_id_4382_, lean_object* v_minIndexable_4383_, lean_object* v_only_4384_, lean_object* v_incremental_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
uint8_t v_minIndexable_boxed_4393_; uint8_t v_only_boxed_4394_; uint8_t v_incremental_boxed_4395_; lean_object* v_res_4396_; 
v_minIndexable_boxed_4393_ = lean_unbox(v_minIndexable_4383_);
v_only_boxed_4394_ = lean_unbox(v_only_4384_);
v_incremental_boxed_4395_ = lean_unbox(v_incremental_4385_);
v_res_4396_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4379_, v_p_4380_, v_mod_x3f_4381_, v_id_4382_, v_minIndexable_boxed_4393_, v_only_boxed_4394_, v_incremental_boxed_4395_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_);
lean_dec(v_a_4391_);
lean_dec_ref(v_a_4390_);
lean_dec(v_a_4389_);
lean_dec_ref(v_a_4388_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4397_, lean_object* v_id_4398_, uint8_t v_minIndexable_4399_, lean_object* v_as_4400_, lean_object* v_as_x27_4401_, lean_object* v_b_4402_, lean_object* v_a_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v___x_4411_; 
v___x_4411_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4397_, v_id_4398_, v_minIndexable_4399_, v_as_x27_4401_, v_b_4402_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4412_, lean_object* v_id_4413_, lean_object* v_minIndexable_4414_, lean_object* v_as_4415_, lean_object* v_as_x27_4416_, lean_object* v_b_4417_, lean_object* v_a_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
uint8_t v_minIndexable_boxed_4426_; lean_object* v_res_4427_; 
v_minIndexable_boxed_4426_ = lean_unbox(v_minIndexable_4414_);
v_res_4427_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4412_, v_id_4413_, v_minIndexable_boxed_4426_, v_as_4415_, v_as_x27_4416_, v_b_4417_, v_a_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec(v_as_x27_4416_);
lean_dec(v_as_4415_);
lean_dec(v_p_4412_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4428_, lean_object* v_as_x27_4429_, lean_object* v_b_4430_, lean_object* v_a_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4429_, v_b_4430_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4440_, lean_object* v_as_x27_4441_, lean_object* v_b_4442_, lean_object* v_a_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4440_, v_as_x27_4441_, v_b_4442_, v_a_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v_as_x27_4441_);
lean_dec(v_as_4440_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4452_, lean_object* v_ref_4453_, lean_object* v_msg_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v___x_4462_; 
v___x_4462_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4453_, v_msg_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4463_, lean_object* v_ref_4464_, lean_object* v_msg_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_res_4473_; 
v_res_4473_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4463_, v_ref_4464_, v_msg_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec(v_ref_4464_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4474_, lean_object* v_id_4475_, uint8_t v_minIndexable_4476_, lean_object* v_as_4477_, lean_object* v_as_x27_4478_, lean_object* v_b_4479_, lean_object* v_a_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v___x_4488_; 
v___x_4488_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4474_, v_id_4475_, v_minIndexable_4476_, v_as_x27_4478_, v_b_4479_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4489_, lean_object* v_id_4490_, lean_object* v_minIndexable_4491_, lean_object* v_as_4492_, lean_object* v_as_x27_4493_, lean_object* v_b_4494_, lean_object* v_a_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
uint8_t v_minIndexable_boxed_4503_; lean_object* v_res_4504_; 
v_minIndexable_boxed_4503_ = lean_unbox(v_minIndexable_4491_);
v_res_4504_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4489_, v_id_4490_, v_minIndexable_boxed_4503_, v_as_4492_, v_as_x27_4493_, v_b_4494_, v_a_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v_as_x27_4493_);
lean_dec(v_as_4492_);
lean_dec(v_p_4489_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4505_, lean_object* v_t_4506_, lean_object* v_k_4507_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4506_, v_k_4507_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4509_, lean_object* v_t_4510_, lean_object* v_k_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4509_, v_t_4510_, v_k_4511_);
lean_dec(v_k_4511_);
lean_dec(v_t_4510_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4513_, uint8_t v_skipAuxDecl_4514_, lean_object* v_auxDeclToFullName_4515_, lean_object* v___x_4516_, lean_object* v_givenNameView_4517_, lean_object* v_as_4518_, lean_object* v_i_4519_, lean_object* v_a_4520_){
_start:
{
lean_object* v___x_4521_; 
v___x_4521_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4513_, v_skipAuxDecl_4514_, v_auxDeclToFullName_4515_, v___x_4516_, v_givenNameView_4517_, v_as_4518_, v_i_4519_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4522_, lean_object* v_skipAuxDecl_4523_, lean_object* v_auxDeclToFullName_4524_, lean_object* v___x_4525_, lean_object* v_givenNameView_4526_, lean_object* v_as_4527_, lean_object* v_i_4528_, lean_object* v_a_4529_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4530_; lean_object* v_res_4531_; 
v_skipAuxDecl_boxed_4530_ = lean_unbox(v_skipAuxDecl_4523_);
v_res_4531_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4522_, v_skipAuxDecl_boxed_4530_, v_auxDeclToFullName_4524_, v___x_4525_, v_givenNameView_4526_, v_as_4527_, v_i_4528_, v_a_4529_);
lean_dec_ref(v_as_4527_);
lean_dec(v_auxDeclToFullName_4524_);
lean_dec(v_givenName_4522_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4532_, lean_object* v_givenName_4533_, lean_object* v_as_4534_, lean_object* v_i_4535_, lean_object* v_a_4536_){
_start:
{
lean_object* v___x_4537_; 
v___x_4537_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4532_, v_givenName_4533_, v_as_4534_, v_i_4535_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4538_, lean_object* v_givenName_4539_, lean_object* v_as_4540_, lean_object* v_i_4541_, lean_object* v_a_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4538_, v_givenName_4539_, v_as_4540_, v_i_4541_, v_a_4542_);
lean_dec_ref(v_as_4540_);
lean_dec(v_givenName_4539_);
lean_dec(v_localDecl_x3f_4538_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4544_, uint8_t v_skipAuxDecl_4545_, lean_object* v_auxDeclToFullName_4546_, lean_object* v___x_4547_, lean_object* v_givenNameView_4548_, lean_object* v_as_4549_, lean_object* v_i_4550_, lean_object* v_a_4551_){
_start:
{
lean_object* v___x_4552_; 
v___x_4552_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4544_, v_skipAuxDecl_4545_, v_auxDeclToFullName_4546_, v___x_4547_, v_givenNameView_4548_, v_as_4549_, v_i_4550_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4553_, lean_object* v_skipAuxDecl_4554_, lean_object* v_auxDeclToFullName_4555_, lean_object* v___x_4556_, lean_object* v_givenNameView_4557_, lean_object* v_as_4558_, lean_object* v_i_4559_, lean_object* v_a_4560_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4561_; lean_object* v_res_4562_; 
v_skipAuxDecl_boxed_4561_ = lean_unbox(v_skipAuxDecl_4554_);
v_res_4562_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4553_, v_skipAuxDecl_boxed_4561_, v_auxDeclToFullName_4555_, v___x_4556_, v_givenNameView_4557_, v_as_4558_, v_i_4559_, v_a_4560_);
lean_dec_ref(v_as_4558_);
lean_dec(v_auxDeclToFullName_4555_);
lean_dec(v_givenName_4553_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4563_, lean_object* v_givenName_4564_, lean_object* v_as_4565_, lean_object* v_i_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v___x_4568_; 
v___x_4568_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4563_, v_givenName_4564_, v_as_4565_, v_i_4566_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4569_, lean_object* v_givenName_4570_, lean_object* v_as_4571_, lean_object* v_i_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4569_, v_givenName_4570_, v_as_4571_, v_i_4572_, v_a_4573_);
lean_dec_ref(v_as_4571_);
lean_dec(v_givenName_4570_);
lean_dec(v_localDecl_x3f_4569_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
lean_object* v___x_4583_; 
v___x_4583_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4575_, v___y_4580_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec_ref(v_opt_4584_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4593_, lean_object* v_msgData_4594_, uint8_t v_severity_4595_, uint8_t v_isSilent_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
lean_object* v___x_4604_; 
v___x_4604_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4593_, v_msgData_4594_, v_severity_4595_, v_isSilent_4596_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4605_, lean_object* v_msgData_4606_, lean_object* v_severity_4607_, lean_object* v_isSilent_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
uint8_t v_severity_boxed_4616_; uint8_t v_isSilent_boxed_4617_; lean_object* v_res_4618_; 
v_severity_boxed_4616_ = lean_unbox(v_severity_4607_);
v_isSilent_boxed_4617_ = lean_unbox(v_isSilent_4608_);
v_res_4618_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4605_, v_msgData_4606_, v_severity_boxed_4616_, v_isSilent_boxed_4617_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v_ref_4605_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4619_, uint8_t v___x_4620_, lean_object* v_b_4621_, lean_object* v_____r_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4630_ = lean_box(0);
v___x_4631_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4619_, v___x_4630_, v___y_4627_, v___y_4628_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; lean_object* v___x_4633_; 
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc_n(v_a_4632_, 2);
lean_dec_ref_known(v___x_4631_, 1);
v___x_4633_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4632_, v___x_4620_, v___y_4623_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
if (lean_obj_tag(v___x_4633_) == 0)
{
uint8_t v___x_4634_; lean_object* v___x_4635_; 
lean_dec_ref_known(v___x_4633_, 1);
v___x_4634_ = 0;
lean_inc(v_a_4632_);
v___x_4635_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4632_, v___x_4634_, v___y_4627_, v___y_4628_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4695_; 
v_a_4636_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4638_ = v___x_4635_;
v_isShared_4639_ = v_isSharedCheck_4695_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4635_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4695_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
if (lean_obj_tag(v_a_4636_) == 1)
{
lean_object* v_val_4640_; lean_object* v___x_4641_; 
lean_del_object(v___x_4638_);
lean_dec(v_a_4632_);
v_val_4640_ = lean_ctor_get(v_a_4636_, 0);
lean_inc_n(v_val_4640_, 2);
lean_dec_ref_known(v_a_4636_, 1);
v___x_4641_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4640_, v___y_4627_, v___y_4628_);
if (lean_obj_tag(v___x_4641_) == 0)
{
lean_object* v___x_4642_; 
lean_dec_ref_known(v___x_4641_, 1);
v___x_4642_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4621_, v_val_4640_, v___y_4627_, v___y_4628_);
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
else
{
lean_object* v_a_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4668_; 
lean_dec(v_val_4640_);
lean_dec_ref(v_b_4621_);
v_a_4661_ = lean_ctor_get(v___x_4641_, 0);
v_isSharedCheck_4668_ = !lean_is_exclusive(v___x_4641_);
if (v_isSharedCheck_4668_ == 0)
{
v___x_4663_ = v___x_4641_;
v_isShared_4664_ = v_isSharedCheck_4668_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_a_4661_);
lean_dec(v___x_4641_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4668_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___x_4666_; 
if (v_isShared_4664_ == 0)
{
v___x_4666_ = v___x_4663_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v_a_4661_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
return v___x_4666_;
}
}
}
}
else
{
uint8_t v___x_4669_; 
lean_dec(v_a_4636_);
lean_inc(v_a_4632_);
v___x_4669_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4621_, v_a_4632_);
if (v___x_4669_ == 0)
{
lean_object* v___x_4670_; 
lean_del_object(v___x_4638_);
v___x_4670_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4621_, v_a_4632_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4680_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4673_ = v___x_4670_;
v_isShared_4674_ = v_isSharedCheck_4680_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4670_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4680_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4678_; 
v___x_4675_ = lean_box(0);
v___x_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4675_);
lean_ctor_set(v___x_4676_, 1, v_a_4671_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 0, v___x_4676_);
v___x_4678_ = v___x_4673_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
else
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4688_; 
v_a_4681_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4683_ = v___x_4670_;
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4670_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4684_ == 0)
{
v___x_4686_ = v___x_4683_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4681_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
}
else
{
lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4693_; 
v___x_4689_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4621_, v_a_4632_);
v___x_4690_ = lean_box(0);
v___x_4691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4691_, 0, v___x_4690_);
lean_ctor_set(v___x_4691_, 1, v___x_4689_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 0, v___x_4691_);
v___x_4693_ = v___x_4638_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4691_);
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
else
{
lean_object* v_a_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4703_; 
lean_dec(v_a_4632_);
lean_dec_ref(v_b_4621_);
v_a_4696_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4698_ = v___x_4635_;
v_isShared_4699_ = v_isSharedCheck_4703_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_a_4696_);
lean_dec(v___x_4635_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4703_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4701_; 
if (v_isShared_4699_ == 0)
{
v___x_4701_ = v___x_4698_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_a_4696_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
return v___x_4701_;
}
}
}
}
else
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4711_; 
lean_dec(v_a_4632_);
lean_dec_ref(v_b_4621_);
v_a_4704_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4706_ = v___x_4633_;
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4633_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4707_ == 0)
{
v___x_4709_ = v___x_4706_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_a_4704_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
}
else
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4719_; 
lean_dec_ref(v_b_4621_);
v_a_4712_ = lean_ctor_get(v___x_4631_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4631_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4714_ = v___x_4631_;
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4631_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4720_, lean_object* v___x_4721_, lean_object* v_b_4722_, lean_object* v_____r_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_){
_start:
{
uint8_t v___x_17514__boxed_4731_; lean_object* v_res_4732_; 
v___x_17514__boxed_4731_ = lean_unbox(v___x_4721_);
v_res_4732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4720_, v___x_17514__boxed_4731_, v_b_4722_, v_____r_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4736_, lean_object* v_b_4737_, lean_object* v_a_4738_, uint8_t v___x_4739_, uint8_t v_only_4740_, uint8_t v_incremental_4741_, lean_object* v_x_4742_, lean_object* v_mod_x3f_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_){
_start:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4751_ = lean_unsigned_to_nat(1u);
v___x_4752_ = l_Lean_Syntax_getArg(v___x_4736_, v___x_4751_);
if (v___x_4739_ == 0)
{
lean_object* v___x_4813_; uint8_t v___x_4814_; 
v___x_4813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4752_);
v___x_4814_ = l_Lean_Syntax_isOfKind(v___x_4752_, v___x_4813_);
if (v___x_4814_ == 0)
{
lean_object* v___x_4815_; 
v___x_4815_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4737_, v_a_4738_, v_mod_x3f_4743_, v___x_4752_, v___x_4739_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4825_; 
v_a_4816_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4818_ = v___x_4815_;
v_isShared_4819_ = v_isSharedCheck_4825_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4815_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4825_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4823_; 
v___x_4820_ = lean_box(0);
v___x_4821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
lean_ctor_set(v___x_4821_, 1, v_a_4816_);
if (v_isShared_4819_ == 0)
{
lean_ctor_set(v___x_4818_, 0, v___x_4821_);
v___x_4823_ = v___x_4818_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v___x_4821_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
else
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4833_; 
v_a_4826_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4828_ = v___x_4815_;
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4815_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
}
else
{
goto v___jp_4773_;
}
}
else
{
goto v___jp_4773_;
}
v___jp_4753_:
{
lean_object* v___x_4754_; 
v___x_4754_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4737_, v_a_4738_, v_mod_x3f_4743_, v___x_4752_, v___x_4739_, v_only_4740_, v_incremental_4741_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4764_; 
v_a_4755_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4757_ = v___x_4754_;
v_isShared_4758_ = v_isSharedCheck_4764_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4754_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4764_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4762_; 
v___x_4759_ = lean_box(0);
v___x_4760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4759_);
lean_ctor_set(v___x_4760_, 1, v_a_4755_);
if (v_isShared_4758_ == 0)
{
lean_ctor_set(v___x_4757_, 0, v___x_4760_);
v___x_4762_ = v___x_4757_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v___x_4760_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
else
{
lean_object* v_a_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4772_; 
v_a_4765_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4767_ = v___x_4754_;
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_a_4765_);
lean_dec(v___x_4754_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v___x_4770_; 
if (v_isShared_4768_ == 0)
{
v___x_4770_ = v___x_4767_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_a_4765_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
}
v___jp_4773_:
{
lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4774_ = l_Lean_TSyntax_getId(v___x_4752_);
v___x_4775_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4774_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v_a_4776_; 
v_a_4776_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_a_4776_);
lean_dec_ref_known(v___x_4775_, 1);
if (lean_obj_tag(v_a_4776_) == 1)
{
lean_object* v_val_4777_; lean_object* v_snd_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4803_; 
v_val_4777_ = lean_ctor_get(v_a_4776_, 0);
lean_inc(v_val_4777_);
lean_dec_ref_known(v_a_4776_, 1);
v_snd_4778_ = lean_ctor_get(v_val_4777_, 1);
v_isSharedCheck_4803_ = !lean_is_exclusive(v_val_4777_);
if (v_isSharedCheck_4803_ == 0)
{
lean_object* v_unused_4804_; 
v_unused_4804_ = lean_ctor_get(v_val_4777_, 0);
lean_dec(v_unused_4804_);
v___x_4780_ = v_val_4777_;
v_isShared_4781_ = v_isSharedCheck_4803_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_snd_4778_);
lean_dec(v_val_4777_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4803_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
if (lean_obj_tag(v_snd_4778_) == 1)
{
lean_object* v___x_4782_; 
lean_dec_ref_known(v_snd_4778_, 2);
v___x_4782_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4737_, v_a_4738_, v_mod_x3f_4743_, v___x_4752_, v___x_4739_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4794_; 
v_a_4783_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4785_ = v___x_4782_;
v_isShared_4786_ = v_isSharedCheck_4794_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4782_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4794_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4787_; lean_object* v___x_4789_; 
v___x_4787_ = lean_box(0);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 1, v_a_4783_);
lean_ctor_set(v___x_4780_, 0, v___x_4787_);
v___x_4789_ = v___x_4780_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4787_);
lean_ctor_set(v_reuseFailAlloc_4793_, 1, v_a_4783_);
v___x_4789_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
lean_object* v___x_4791_; 
if (v_isShared_4786_ == 0)
{
lean_ctor_set(v___x_4785_, 0, v___x_4789_);
v___x_4791_ = v___x_4785_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4789_);
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
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
lean_del_object(v___x_4780_);
v_a_4795_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4782_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4782_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
else
{
lean_del_object(v___x_4780_);
lean_dec(v_snd_4778_);
goto v___jp_4753_;
}
}
}
else
{
lean_dec(v_a_4776_);
goto v___jp_4753_;
}
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
lean_dec(v___x_4752_);
lean_dec(v_mod_x3f_4743_);
lean_dec(v_a_4738_);
lean_dec_ref(v_b_4737_);
v_a_4805_ = lean_ctor_get(v___x_4775_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___x_4775_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4775_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4834_, lean_object* v_b_4835_, lean_object* v_a_4836_, lean_object* v___x_4837_, lean_object* v_only_4838_, lean_object* v_incremental_4839_, lean_object* v_x_4840_, lean_object* v_mod_x3f_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_){
_start:
{
uint8_t v___x_17732__boxed_4849_; uint8_t v_only_boxed_4850_; uint8_t v_incremental_boxed_4851_; lean_object* v_res_4852_; 
v___x_17732__boxed_4849_ = lean_unbox(v___x_4837_);
v_only_boxed_4850_ = lean_unbox(v_only_4838_);
v_incremental_boxed_4851_ = lean_unbox(v_incremental_4839_);
v_res_4852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4834_, v_b_4835_, v_a_4836_, v___x_17732__boxed_4849_, v_only_boxed_4850_, v_incremental_boxed_4851_, v_x_4840_, v_mod_x3f_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
lean_dec(v___y_4847_);
lean_dec_ref(v___y_4846_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___x_4834_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4853_, lean_object* v___x_4854_, lean_object* v_____r_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_){
_start:
{
lean_object* v___x_4863_; 
v___x_4863_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4853_, v___x_4854_, v___y_4860_, v___y_4861_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4873_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4866_ = v___x_4863_;
v_isShared_4867_ = v_isSharedCheck_4873_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4863_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4873_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4871_; 
v___x_4868_ = lean_box(0);
v___x_4869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4868_);
lean_ctor_set(v___x_4869_, 1, v_a_4864_);
if (v_isShared_4867_ == 0)
{
lean_ctor_set(v___x_4866_, 0, v___x_4869_);
v___x_4871_ = v___x_4866_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v___x_4869_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
}
else
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
v_a_4874_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4863_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4863_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4882_, lean_object* v___x_4883_, lean_object* v_____r_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_){
_start:
{
lean_object* v_res_4892_; 
v_res_4892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4882_, v___x_4883_, v_____r_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
lean_dec(v___y_4890_);
lean_dec_ref(v___y_4889_);
lean_dec(v___y_4888_);
lean_dec_ref(v___y_4887_);
lean_dec(v___y_4886_);
lean_dec_ref(v___y_4885_);
lean_dec(v___x_4883_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4893_, lean_object* v_b_4894_, lean_object* v_a_4895_, uint8_t v___x_4896_, uint8_t v_only_4897_, uint8_t v_incremental_4898_, uint8_t v___x_4899_, lean_object* v_x_4900_, lean_object* v_mod_x3f_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4909_ = lean_unsigned_to_nat(2u);
v___x_4910_ = l_Lean_Syntax_getArg(v___x_4893_, v___x_4909_);
if (v___x_4899_ == 0)
{
lean_object* v___x_4971_; uint8_t v___x_4972_; 
v___x_4971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4910_);
v___x_4972_ = l_Lean_Syntax_isOfKind(v___x_4910_, v___x_4971_);
if (v___x_4972_ == 0)
{
lean_object* v___x_4973_; 
v___x_4973_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4894_, v_a_4895_, v_mod_x3f_4901_, v___x_4910_, v___x_4896_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v_a_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_4983_; 
v_a_4974_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4976_ = v___x_4973_;
v_isShared_4977_ = v_isSharedCheck_4983_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_a_4974_);
lean_dec(v___x_4973_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_4983_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4981_; 
v___x_4978_ = lean_box(0);
v___x_4979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
lean_ctor_set(v___x_4979_, 1, v_a_4974_);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v___x_4979_);
v___x_4981_ = v___x_4976_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v___x_4979_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
else
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_4991_; 
v_a_4984_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4986_ = v___x_4973_;
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v___x_4973_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v___x_4989_; 
if (v_isShared_4987_ == 0)
{
v___x_4989_ = v___x_4986_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4984_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
}
else
{
goto v___jp_4931_;
}
}
else
{
goto v___jp_4931_;
}
v___jp_4911_:
{
lean_object* v___x_4912_; 
v___x_4912_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4894_, v_a_4895_, v_mod_x3f_4901_, v___x_4910_, v___x_4896_, v_only_4897_, v_incremental_4898_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4922_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4915_ = v___x_4912_;
v_isShared_4916_ = v_isSharedCheck_4922_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4912_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4922_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4920_; 
v___x_4917_ = lean_box(0);
v___x_4918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
lean_ctor_set(v___x_4918_, 1, v_a_4913_);
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 0, v___x_4918_);
v___x_4920_ = v___x_4915_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4918_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
else
{
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4930_; 
v_a_4923_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4925_ = v___x_4912_;
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4912_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4928_; 
if (v_isShared_4926_ == 0)
{
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4923_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
}
v___jp_4931_:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4932_ = l_Lean_TSyntax_getId(v___x_4910_);
v___x_4933_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4932_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
if (lean_obj_tag(v___x_4933_) == 0)
{
lean_object* v_a_4934_; 
v_a_4934_ = lean_ctor_get(v___x_4933_, 0);
lean_inc(v_a_4934_);
lean_dec_ref_known(v___x_4933_, 1);
if (lean_obj_tag(v_a_4934_) == 1)
{
lean_object* v_val_4935_; lean_object* v_snd_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4961_; 
v_val_4935_ = lean_ctor_get(v_a_4934_, 0);
lean_inc(v_val_4935_);
lean_dec_ref_known(v_a_4934_, 1);
v_snd_4936_ = lean_ctor_get(v_val_4935_, 1);
v_isSharedCheck_4961_ = !lean_is_exclusive(v_val_4935_);
if (v_isSharedCheck_4961_ == 0)
{
lean_object* v_unused_4962_; 
v_unused_4962_ = lean_ctor_get(v_val_4935_, 0);
lean_dec(v_unused_4962_);
v___x_4938_ = v_val_4935_;
v_isShared_4939_ = v_isSharedCheck_4961_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_snd_4936_);
lean_dec(v_val_4935_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4961_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
if (lean_obj_tag(v_snd_4936_) == 1)
{
lean_object* v___x_4940_; 
lean_dec_ref_known(v_snd_4936_, 2);
v___x_4940_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4894_, v_a_4895_, v_mod_x3f_4901_, v___x_4910_, v___x_4896_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
if (lean_obj_tag(v___x_4940_) == 0)
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4952_; 
v_a_4941_ = lean_ctor_get(v___x_4940_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4943_ = v___x_4940_;
v_isShared_4944_ = v_isSharedCheck_4952_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4940_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4952_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4945_; lean_object* v___x_4947_; 
v___x_4945_ = lean_box(0);
if (v_isShared_4939_ == 0)
{
lean_ctor_set(v___x_4938_, 1, v_a_4941_);
lean_ctor_set(v___x_4938_, 0, v___x_4945_);
v___x_4947_ = v___x_4938_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4945_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_a_4941_);
v___x_4947_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
lean_object* v___x_4949_; 
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 0, v___x_4947_);
v___x_4949_ = v___x_4943_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4947_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
}
}
else
{
lean_object* v_a_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4960_; 
lean_del_object(v___x_4938_);
v_a_4953_ = lean_ctor_get(v___x_4940_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4955_ = v___x_4940_;
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_a_4953_);
lean_dec(v___x_4940_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4958_; 
if (v_isShared_4956_ == 0)
{
v___x_4958_ = v___x_4955_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
else
{
lean_del_object(v___x_4938_);
lean_dec(v_snd_4936_);
goto v___jp_4911_;
}
}
}
else
{
lean_dec(v_a_4934_);
goto v___jp_4911_;
}
}
else
{
lean_object* v_a_4963_; lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_4970_; 
lean_dec(v___x_4910_);
lean_dec(v_mod_x3f_4901_);
lean_dec(v_a_4895_);
lean_dec_ref(v_b_4894_);
v_a_4963_ = lean_ctor_get(v___x_4933_, 0);
v_isSharedCheck_4970_ = !lean_is_exclusive(v___x_4933_);
if (v_isSharedCheck_4970_ == 0)
{
v___x_4965_ = v___x_4933_;
v_isShared_4966_ = v_isSharedCheck_4970_;
goto v_resetjp_4964_;
}
else
{
lean_inc(v_a_4963_);
lean_dec(v___x_4933_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_4970_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v___x_4968_; 
if (v_isShared_4966_ == 0)
{
v___x_4968_ = v___x_4965_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4969_; 
v_reuseFailAlloc_4969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4969_, 0, v_a_4963_);
v___x_4968_ = v_reuseFailAlloc_4969_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
return v___x_4968_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4992_, lean_object* v_b_4993_, lean_object* v_a_4994_, lean_object* v___x_4995_, lean_object* v_only_4996_, lean_object* v_incremental_4997_, lean_object* v___x_4998_, lean_object* v_x_4999_, lean_object* v_mod_x3f_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_){
_start:
{
uint8_t v___x_18001__boxed_5008_; uint8_t v_only_boxed_5009_; uint8_t v_incremental_boxed_5010_; uint8_t v___x_18002__boxed_5011_; lean_object* v_res_5012_; 
v___x_18001__boxed_5008_ = lean_unbox(v___x_4995_);
v_only_boxed_5009_ = lean_unbox(v_only_4996_);
v_incremental_boxed_5010_ = lean_unbox(v_incremental_4997_);
v___x_18002__boxed_5011_ = lean_unbox(v___x_4998_);
v_res_5012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4992_, v_b_4993_, v_a_4994_, v___x_18001__boxed_5008_, v_only_boxed_5009_, v_incremental_boxed_5010_, v___x_18002__boxed_5011_, v_x_4999_, v_mod_x3f_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
lean_dec(v___y_5004_);
lean_dec_ref(v___y_5003_);
lean_dec(v___y_5002_);
lean_dec_ref(v___y_5001_);
lean_dec(v___x_4992_);
return v_res_5012_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_5021_ = l_Lean_stringToMessageData(v___x_5020_);
return v___x_5021_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13(void){
_start:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12));
v___x_5048_ = l_Lean_stringToMessageData(v___x_5047_);
return v___x_5048_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5053_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_5054_ = l_Lean_stringToMessageData(v___x_5053_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_5055_, uint8_t v_only_5056_, uint8_t v_incremental_5057_, lean_object* v_as_5058_, size_t v_sz_5059_, size_t v_i_5060_, lean_object* v_b_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_){
_start:
{
lean_object* v_snd_5070_; lean_object* v___y_5075_; uint8_t v___y_5076_; lean_object* v_a_5080_; lean_object* v___y_5084_; uint8_t v___x_5088_; 
v___x_5088_ = lean_usize_dec_lt(v_i_5060_, v_sz_5059_);
if (v___x_5088_ == 0)
{
lean_object* v___x_5089_; 
v___x_5089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5089_, 0, v_b_5061_);
return v___x_5089_;
}
else
{
lean_object* v_a_5090_; lean_object* v___x_5091_; uint8_t v___x_5092_; 
v_a_5090_ = lean_array_uget_borrowed(v_as_5058_, v_i_5060_);
v___x_5091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_5090_);
v___x_5092_ = l_Lean_Syntax_isOfKind(v_a_5090_, v___x_5091_);
if (v___x_5092_ == 0)
{
lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5093_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5090_);
v___x_5094_ = l_Lean_MessageData_ofSyntax(v_a_5090_);
v___x_5095_ = l_Lean_indentD(v___x_5094_);
v___x_5096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5096_, 0, v___x_5093_);
lean_ctor_set(v___x_5096_, 1, v___x_5095_);
v___x_5097_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5096_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
if (lean_obj_tag(v___x_5097_) == 0)
{
lean_dec_ref_known(v___x_5097_, 1);
v_snd_5070_ = v_b_5061_;
goto v___jp_5069_;
}
else
{
lean_object* v_a_5098_; 
v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc(v_a_5098_);
lean_dec_ref_known(v___x_5097_, 1);
v_a_5080_ = v_a_5098_;
goto v___jp_5079_;
}
}
else
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; uint8_t v___x_5102_; 
v___x_5099_ = lean_unsigned_to_nat(0u);
v___x_5100_ = l_Lean_Syntax_getArg(v_a_5090_, v___x_5099_);
v___x_5101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_5100_);
v___x_5102_ = l_Lean_Syntax_isOfKind(v___x_5100_, v___x_5101_);
if (v___x_5102_ == 0)
{
lean_object* v___x_5103_; uint8_t v___x_5104_; 
v___x_5103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_5100_);
v___x_5104_ = l_Lean_Syntax_isOfKind(v___x_5100_, v___x_5103_);
if (v___x_5104_ == 0)
{
lean_object* v___x_5105_; uint8_t v___x_5106_; 
v___x_5105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_5100_);
v___x_5106_ = l_Lean_Syntax_isOfKind(v___x_5100_, v___x_5105_);
if (v___x_5106_ == 0)
{
lean_object* v___x_5107_; uint8_t v___x_5108_; 
v___x_5107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_5100_);
v___x_5108_ = l_Lean_Syntax_isOfKind(v___x_5100_, v___x_5107_);
if (v___x_5108_ == 0)
{
lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
lean_dec(v___x_5100_);
v___x_5109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5090_);
v___x_5110_ = l_Lean_MessageData_ofSyntax(v_a_5090_);
v___x_5111_ = l_Lean_indentD(v___x_5110_);
v___x_5112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5112_, 0, v___x_5109_);
lean_ctor_set(v___x_5112_, 1, v___x_5111_);
v___x_5113_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5112_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_dec_ref_known(v___x_5113_, 1);
v_snd_5070_ = v_b_5061_;
goto v___jp_5069_;
}
else
{
lean_object* v_a_5114_; 
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
lean_inc(v_a_5114_);
lean_dec_ref_known(v___x_5113_, 1);
v_a_5080_ = v_a_5114_;
goto v___jp_5079_;
}
}
else
{
lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5115_ = lean_unsigned_to_nat(1u);
v___x_5116_ = l_Lean_Syntax_getArg(v___x_5100_, v___x_5115_);
lean_dec(v___x_5100_);
if (v___x_5106_ == 0)
{
lean_object* v___x_5125_; uint8_t v___x_5126_; 
v___x_5125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15));
lean_inc(v___x_5116_);
v___x_5126_ = l_Lean_Syntax_isOfKind(v___x_5116_, v___x_5125_);
if (v___x_5126_ == 0)
{
lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; 
lean_dec(v___x_5116_);
v___x_5127_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5090_);
v___x_5128_ = l_Lean_MessageData_ofSyntax(v_a_5090_);
v___x_5129_ = l_Lean_indentD(v___x_5128_);
v___x_5130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5130_, 0, v___x_5127_);
lean_ctor_set(v___x_5130_, 1, v___x_5129_);
v___x_5131_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5130_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
if (lean_obj_tag(v___x_5131_) == 0)
{
lean_dec_ref_known(v___x_5131_, 1);
v_snd_5070_ = v_b_5061_;
goto v___jp_5069_;
}
else
{
lean_object* v_a_5132_; 
v_a_5132_ = lean_ctor_get(v___x_5131_, 0);
lean_inc(v_a_5132_);
lean_dec_ref_known(v___x_5131_, 1);
v_a_5080_ = v_a_5132_;
goto v___jp_5079_;
}
}
else
{
goto v___jp_5117_;
}
}
else
{
goto v___jp_5117_;
}
v___jp_5117_:
{
if (v_only_5056_ == 0)
{
lean_object* v___x_5118_; lean_object* v___x_5119_; 
v___x_5118_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13);
v___x_5119_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_5116_, v___x_5118_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v_a_5120_; lean_object* v___x_5121_; 
v_a_5120_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_a_5120_);
lean_dec_ref_known(v___x_5119_, 1);
lean_inc_ref(v_b_5061_);
v___x_5121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_5061_, v___x_5116_, v_a_5120_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
lean_dec(v___x_5116_);
v___y_5084_ = v___x_5121_;
goto v___jp_5083_;
}
else
{
lean_object* v_a_5122_; 
lean_dec(v___x_5116_);
v_a_5122_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_a_5122_);
lean_dec_ref_known(v___x_5119_, 1);
v_a_5080_ = v_a_5122_;
goto v___jp_5079_;
}
}
else
{
lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___x_5123_ = lean_box(0);
lean_inc_ref(v_b_5061_);
v___x_5124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_5061_, v___x_5116_, v___x_5123_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
lean_dec(v___x_5116_);
v___y_5084_ = v___x_5124_;
goto v___jp_5083_;
}
}
}
}
else
{
lean_object* v___x_5133_; lean_object* v___x_5134_; uint8_t v___x_5135_; 
v___x_5133_ = lean_unsigned_to_nat(1u);
v___x_5134_ = l_Lean_Syntax_getArg(v___x_5100_, v___x_5133_);
v___x_5135_ = l_Lean_Syntax_isNone(v___x_5134_);
if (v___x_5135_ == 0)
{
uint8_t v___x_5136_; 
lean_inc(v___x_5134_);
v___x_5136_ = l_Lean_Syntax_matchesNull(v___x_5134_, v___x_5133_);
if (v___x_5136_ == 0)
{
lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; 
lean_dec(v___x_5134_);
lean_dec(v___x_5100_);
v___x_5137_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5090_);
v___x_5138_ = l_Lean_MessageData_ofSyntax(v_a_5090_);
v___x_5139_ = l_Lean_indentD(v___x_5138_);
v___x_5140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5140_, 0, v___x_5137_);
lean_ctor_set(v___x_5140_, 1, v___x_5139_);
v___x_5141_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5140_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_dec_ref_known(v___x_5141_, 1);
v_snd_5070_ = v_b_5061_;
goto v___jp_5069_;
}
else
{
lean_object* v_a_5142_; 
v_a_5142_ = lean_ctor_get(v___x_5141_, 0);
lean_inc(v_a_5142_);
lean_dec_ref_known(v___x_5141_, 1);
v_a_5080_ = v_a_5142_;
goto v___jp_5079_;
}
}
else
{
lean_object* v___x_5143_; 
v___x_5143_ = l_Lean_Syntax_getArg(v___x_5134_, v___x_5099_);
lean_dec(v___x_5134_);
if (v___x_5135_ == 0)
{
lean_object* v___x_5148_; uint8_t v___x_5149_; 
v___x_5148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_5143_);
v___x_5149_ = l_Lean_Syntax_isOfKind(v___x_5143_, v___x_5148_);
if (v___x_5149_ == 0)
{
lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; 
lean_dec(v___x_5143_);
lean_dec(v___x_5100_);
v___x_5150_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5090_);
v___x_5151_ = l_Lean_MessageData_ofSyntax(v_a_5090_);
v___x_5152_ = l_Lean_indentD(v___x_5151_);
v___x_5153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5153_, 0, v___x_5150_);
lean_ctor_set(v___x_5153_, 1, v___x_5152_);
v___x_5154_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5153_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_dec_ref_known(v___x_5154_, 1);
v_snd_5070_ = v_b_5061_;
goto v___jp_5069_;
}
else
{
lean_object* v_a_5155_; 
v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_a_5155_);
lean_dec_ref_known(v___x_5154_, 1);
v_a_5080_ = v_a_5155_;
goto v___jp_5079_;
}
}
else
{
goto v___jp_5144_;
}
}
else
{
goto v___jp_5144_;
}
v___jp_5144_:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5145_ = lean_box(0);
v___x_5146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5146_, 0, v___x_5143_);
lean_inc(v_a_5090_);
lean_inc_ref(v_b_5061_);
v___x_5147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_5100_, v_b_5061_, v_a_5090_, v___x_5092_, v_only_5056_, v_incremental_5057_, v___x_5104_, v___x_5145_, v___x_5146_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
lean_dec(v___x_5100_);
v___y_5084_ = v___x_5147_;
goto v___jp_5083_;
}
}
}
else
{
lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; 
lean_dec(v___x_5134_);
v___x_5156_ = lean_box(0);
v___x_5157_ = lean_box(0);
lean_inc(v_a_5090_);
lean_inc_ref(v_b_5061_);
v___x_5158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_5100_, v_b_5061_, v_a_5090_, v___x_5092_, v_only_5056_, v_incremental_5057_, v___x_5104_, v___x_5156_, v___x_5157_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
lean_dec(v___x_5100_);
v___y_5084_ = v___x_5158_;
goto v___jp_5083_;
}
}
}
else
{
lean_object* v___x_5159_; uint8_t v___x_5160_; 
v___x_5159_ = l_Lean_Syntax_getArg(v___x_5100_, v___x_5099_);
v___x_5160_ = l_Lean_Syntax_isNone(v___x_5159_);
if (v___x_5160_ == 0)
{
lean_object* v___x_5161_; uint8_t v___x_5162_; 
v___x_5161_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_5159_);
v___x_5162_ = l_Lean_Syntax_matchesNull(v___x_5159_, v___x_5161_);
if (v___x_5162_ == 0)
{
lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; 
lean_dec(v___x_5159_);
lean_dec(v___x_5100_);
v___x_5163_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5090_);
v___x_5164_ = l_Lean_MessageData_ofSyntax(v_a_5090_);
v___x_5165_ = l_Lean_indentD(v___x_5164_);
v___x_5166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5166_, 0, v___x_5163_);
lean_ctor_set(v___x_5166_, 1, v___x_5165_);
v___x_5167_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5166_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_dec_ref_known(v___x_5167_, 1);
v_snd_5070_ = v_b_5061_;
goto v___jp_5069_;
}
else
{
lean_object* v_a_5168_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___x_5167_, 1);
v_a_5080_ = v_a_5168_;
goto v___jp_5079_;
}
}
else
{
lean_object* v___x_5169_; 
v___x_5169_ = l_Lean_Syntax_getArg(v___x_5159_, v___x_5099_);
lean_dec(v___x_5159_);
if (v___x_5160_ == 0)
{
lean_object* v___x_5174_; uint8_t v___x_5175_; 
v___x_5174_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_5169_);
v___x_5175_ = l_Lean_Syntax_isOfKind(v___x_5169_, v___x_5174_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; 
lean_dec(v___x_5169_);
lean_dec(v___x_5100_);
v___x_5176_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5090_);
v___x_5177_ = l_Lean_MessageData_ofSyntax(v_a_5090_);
v___x_5178_ = l_Lean_indentD(v___x_5177_);
v___x_5179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5179_, 0, v___x_5176_);
lean_ctor_set(v___x_5179_, 1, v___x_5178_);
v___x_5180_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5179_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
if (lean_obj_tag(v___x_5180_) == 0)
{
lean_dec_ref_known(v___x_5180_, 1);
v_snd_5070_ = v_b_5061_;
goto v___jp_5069_;
}
else
{
lean_object* v_a_5181_; 
v_a_5181_ = lean_ctor_get(v___x_5180_, 0);
lean_inc(v_a_5181_);
lean_dec_ref_known(v___x_5180_, 1);
v_a_5080_ = v_a_5181_;
goto v___jp_5079_;
}
}
else
{
goto v___jp_5170_;
}
}
else
{
goto v___jp_5170_;
}
v___jp_5170_:
{
lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; 
v___x_5171_ = lean_box(0);
v___x_5172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5172_, 0, v___x_5169_);
lean_inc(v_a_5090_);
lean_inc_ref(v_b_5061_);
v___x_5173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_5100_, v_b_5061_, v_a_5090_, v___x_5102_, v_only_5056_, v_incremental_5057_, v___x_5171_, v___x_5172_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
lean_dec(v___x_5100_);
v___y_5084_ = v___x_5173_;
goto v___jp_5083_;
}
}
}
else
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; 
lean_dec(v___x_5159_);
v___x_5182_ = lean_box(0);
v___x_5183_ = lean_box(0);
lean_inc(v_a_5090_);
lean_inc_ref(v_b_5061_);
v___x_5184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_5100_, v_b_5061_, v_a_5090_, v___x_5102_, v_only_5056_, v_incremental_5057_, v___x_5182_, v___x_5183_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
lean_dec(v___x_5100_);
v___y_5084_ = v___x_5184_;
goto v___jp_5083_;
}
}
}
else
{
lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; uint8_t v___x_5188_; 
v___x_5185_ = lean_unsigned_to_nat(1u);
v___x_5186_ = l_Lean_Syntax_getArg(v___x_5100_, v___x_5185_);
lean_dec(v___x_5100_);
v___x_5187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_5186_);
v___x_5188_ = l_Lean_Syntax_isOfKind(v___x_5186_, v___x_5187_);
if (v___x_5188_ == 0)
{
lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; 
lean_dec(v___x_5186_);
v___x_5189_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_5090_);
v___x_5190_ = l_Lean_MessageData_ofSyntax(v_a_5090_);
v___x_5191_ = l_Lean_indentD(v___x_5190_);
v___x_5192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5189_);
lean_ctor_set(v___x_5192_, 1, v___x_5191_);
v___x_5193_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__2___redArg(v___x_5192_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_dec_ref_known(v___x_5193_, 1);
v_snd_5070_ = v_b_5061_;
goto v___jp_5069_;
}
else
{
lean_object* v_a_5194_; 
v_a_5194_ = lean_ctor_get(v___x_5193_, 0);
lean_inc(v_a_5194_);
lean_dec_ref_known(v___x_5193_, 1);
v_a_5080_ = v_a_5194_;
goto v___jp_5079_;
}
}
else
{
if (v_incremental_5057_ == 0)
{
lean_object* v___x_5195_; lean_object* v___x_5196_; 
v___x_5195_ = lean_box(0);
lean_inc_ref(v_b_5061_);
v___x_5196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_5186_, v___x_5092_, v_b_5061_, v___x_5195_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
v___y_5084_ = v___x_5196_;
goto v___jp_5083_;
}
else
{
lean_object* v___x_5197_; lean_object* v___x_5198_; 
v___x_5197_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_5198_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_5090_, v___x_5197_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
if (lean_obj_tag(v___x_5198_) == 0)
{
lean_object* v_a_5199_; lean_object* v___x_5200_; 
v_a_5199_ = lean_ctor_get(v___x_5198_, 0);
lean_inc(v_a_5199_);
lean_dec_ref_known(v___x_5198_, 1);
lean_inc_ref(v_b_5061_);
v___x_5200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_5186_, v___x_5092_, v_b_5061_, v_a_5199_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
v___y_5084_ = v___x_5200_;
goto v___jp_5083_;
}
else
{
lean_object* v_a_5201_; 
lean_dec(v___x_5186_);
v_a_5201_ = lean_ctor_get(v___x_5198_, 0);
lean_inc(v_a_5201_);
lean_dec_ref_known(v___x_5198_, 1);
v_a_5080_ = v_a_5201_;
goto v___jp_5079_;
}
}
}
}
}
}
v___jp_5069_:
{
size_t v___x_5071_; size_t v___x_5072_; 
v___x_5071_ = ((size_t)1ULL);
v___x_5072_ = lean_usize_add(v_i_5060_, v___x_5071_);
v_i_5060_ = v___x_5072_;
v_b_5061_ = v_snd_5070_;
goto _start;
}
v___jp_5074_:
{
if (v___y_5076_ == 0)
{
if (v_lax_5055_ == 0)
{
lean_object* v___x_5077_; 
lean_dec_ref(v_b_5061_);
v___x_5077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5077_, 0, v___y_5075_);
return v___x_5077_;
}
else
{
lean_dec_ref(v___y_5075_);
v_snd_5070_ = v_b_5061_;
goto v___jp_5069_;
}
}
else
{
lean_object* v___x_5078_; 
lean_dec_ref(v_b_5061_);
v___x_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5078_, 0, v___y_5075_);
return v___x_5078_;
}
}
v___jp_5079_:
{
uint8_t v___x_5081_; 
v___x_5081_ = l_Lean_Exception_isInterrupt(v_a_5080_);
if (v___x_5081_ == 0)
{
uint8_t v___x_5082_; 
lean_inc_ref(v_a_5080_);
v___x_5082_ = l_Lean_Exception_isRuntime(v_a_5080_);
v___y_5075_ = v_a_5080_;
v___y_5076_ = v___x_5082_;
goto v___jp_5074_;
}
else
{
v___y_5075_ = v_a_5080_;
v___y_5076_ = v___x_5081_;
goto v___jp_5074_;
}
}
v___jp_5083_:
{
if (lean_obj_tag(v___y_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v_snd_5086_; 
lean_dec_ref(v_b_5061_);
v_a_5085_ = lean_ctor_get(v___y_5084_, 0);
lean_inc(v_a_5085_);
lean_dec_ref_known(v___y_5084_, 1);
v_snd_5086_ = lean_ctor_get(v_a_5085_, 1);
lean_inc(v_snd_5086_);
lean_dec(v_a_5085_);
v_snd_5070_ = v_snd_5086_;
goto v___jp_5069_;
}
else
{
lean_object* v_a_5087_; 
v_a_5087_ = lean_ctor_get(v___y_5084_, 0);
lean_inc(v_a_5087_);
lean_dec_ref_known(v___y_5084_, 1);
v_a_5080_ = v_a_5087_;
goto v___jp_5079_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_5202_, lean_object* v_only_5203_, lean_object* v_incremental_5204_, lean_object* v_as_5205_, lean_object* v_sz_5206_, lean_object* v_i_5207_, lean_object* v_b_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_){
_start:
{
uint8_t v_lax_boxed_5216_; uint8_t v_only_boxed_5217_; uint8_t v_incremental_boxed_5218_; size_t v_sz_boxed_5219_; size_t v_i_boxed_5220_; lean_object* v_res_5221_; 
v_lax_boxed_5216_ = lean_unbox(v_lax_5202_);
v_only_boxed_5217_ = lean_unbox(v_only_5203_);
v_incremental_boxed_5218_ = lean_unbox(v_incremental_5204_);
v_sz_boxed_5219_ = lean_unbox_usize(v_sz_5206_);
lean_dec(v_sz_5206_);
v_i_boxed_5220_ = lean_unbox_usize(v_i_5207_);
lean_dec(v_i_5207_);
v_res_5221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_5216_, v_only_boxed_5217_, v_incremental_boxed_5218_, v_as_5205_, v_sz_boxed_5219_, v_i_boxed_5220_, v_b_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
lean_dec(v___y_5212_);
lean_dec_ref(v___y_5211_);
lean_dec(v___y_5210_);
lean_dec_ref(v___y_5209_);
lean_dec_ref(v_as_5205_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_5222_, lean_object* v_ps_5223_, uint8_t v_only_5224_, uint8_t v_lax_5225_, uint8_t v_incremental_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_){
_start:
{
size_t v_sz_5234_; size_t v___x_5235_; lean_object* v___x_5236_; 
v_sz_5234_ = lean_array_size(v_ps_5223_);
v___x_5235_ = ((size_t)0ULL);
v___x_5236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_5225_, v_only_5224_, v_incremental_5226_, v_ps_5223_, v_sz_5234_, v___x_5235_, v_params_5222_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_);
return v___x_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_5237_, lean_object* v_ps_5238_, lean_object* v_only_5239_, lean_object* v_lax_5240_, lean_object* v_incremental_5241_, lean_object* v_a_5242_, lean_object* v_a_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_){
_start:
{
uint8_t v_only_boxed_5249_; uint8_t v_lax_boxed_5250_; uint8_t v_incremental_boxed_5251_; lean_object* v_res_5252_; 
v_only_boxed_5249_ = lean_unbox(v_only_5239_);
v_lax_boxed_5250_ = lean_unbox(v_lax_5240_);
v_incremental_boxed_5251_ = lean_unbox(v_incremental_5241_);
v_res_5252_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5237_, v_ps_5238_, v_only_boxed_5249_, v_lax_boxed_5250_, v_incremental_boxed_5251_, v_a_5242_, v_a_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec_ref(v_a_5244_);
lean_dec(v_a_5243_);
lean_dec_ref(v_a_5242_);
lean_dec_ref(v_ps_5238_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_){
_start:
{
lean_object* v_origin_5264_; 
v_origin_5264_ = lean_ctor_get(v_thm_5253_, 5);
if (lean_obj_tag(v_origin_5264_) == 0)
{
lean_object* v_declName_5265_; lean_object* v___x_5266_; 
lean_inc_ref(v_origin_5264_);
lean_dec_ref(v_thm_5253_);
v_declName_5265_ = lean_ctor_get(v_origin_5264_, 0);
lean_inc(v_declName_5265_);
lean_dec_ref_known(v_origin_5264_, 1);
v___x_5266_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_5265_, v_a_5261_, v_a_5262_);
return v___x_5266_;
}
else
{
lean_object* v_proof_5267_; lean_object* v___x_5268_; 
v_proof_5267_ = lean_ctor_get(v_thm_5253_, 1);
lean_inc_ref(v_proof_5267_);
lean_dec_ref(v_thm_5253_);
v___x_5268_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_5267_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_);
return v___x_5268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_){
_start:
{
lean_object* v_res_5280_; 
v_res_5280_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_);
lean_dec(v_a_5278_);
lean_dec_ref(v_a_5277_);
lean_dec(v_a_5276_);
lean_dec_ref(v_a_5275_);
lean_dec(v_a_5274_);
lean_dec_ref(v_a_5273_);
lean_dec(v_a_5272_);
lean_dec_ref(v_a_5271_);
lean_dec(v_a_5270_);
return v_res_5280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_5281_, size_t v_sz_5282_, size_t v_i_5283_, lean_object* v_b_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_){
_start:
{
uint8_t v___x_5295_; 
v___x_5295_ = lean_usize_dec_lt(v_i_5283_, v_sz_5282_);
if (v___x_5295_ == 0)
{
lean_object* v___x_5296_; 
v___x_5296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5296_, 0, v_b_5284_);
return v___x_5296_;
}
else
{
lean_object* v_snd_5297_; lean_object* v___x_5299_; uint8_t v_isShared_5300_; uint8_t v_isSharedCheck_5323_; 
v_snd_5297_ = lean_ctor_get(v_b_5284_, 1);
v_isSharedCheck_5323_ = !lean_is_exclusive(v_b_5284_);
if (v_isSharedCheck_5323_ == 0)
{
lean_object* v_unused_5324_; 
v_unused_5324_ = lean_ctor_get(v_b_5284_, 0);
lean_dec(v_unused_5324_);
v___x_5299_ = v_b_5284_;
v_isShared_5300_ = v_isSharedCheck_5323_;
goto v_resetjp_5298_;
}
else
{
lean_inc(v_snd_5297_);
lean_dec(v_b_5284_);
v___x_5299_ = lean_box(0);
v_isShared_5300_ = v_isSharedCheck_5323_;
goto v_resetjp_5298_;
}
v_resetjp_5298_:
{
lean_object* v___x_5301_; lean_object* v_a_5303_; lean_object* v_a_5310_; lean_object* v___x_5311_; 
v___x_5301_ = lean_box(0);
v_a_5310_ = lean_array_uget_borrowed(v_as_5281_, v_i_5283_);
lean_inc(v_a_5310_);
v___x_5311_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5310_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v_a_5312_; uint8_t v___x_5313_; 
v_a_5312_ = lean_ctor_get(v___x_5311_, 0);
lean_inc(v_a_5312_);
lean_dec_ref_known(v___x_5311_, 1);
v___x_5313_ = lean_unbox(v_a_5312_);
lean_dec(v_a_5312_);
if (v___x_5313_ == 0)
{
v_a_5303_ = v_snd_5297_;
goto v___jp_5302_;
}
else
{
lean_object* v___x_5314_; 
lean_inc(v_a_5310_);
v___x_5314_ = l_Lean_PersistentArray_push___redArg(v_snd_5297_, v_a_5310_);
v_a_5303_ = v___x_5314_;
goto v___jp_5302_;
}
}
else
{
lean_object* v_a_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5322_; 
lean_del_object(v___x_5299_);
lean_dec(v_snd_5297_);
v_a_5315_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5322_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5322_ == 0)
{
v___x_5317_ = v___x_5311_;
v_isShared_5318_ = v_isSharedCheck_5322_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_a_5315_);
lean_dec(v___x_5311_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5322_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v___x_5320_; 
if (v_isShared_5318_ == 0)
{
v___x_5320_ = v___x_5317_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_a_5315_);
v___x_5320_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
return v___x_5320_;
}
}
}
v___jp_5302_:
{
lean_object* v___x_5305_; 
if (v_isShared_5300_ == 0)
{
lean_ctor_set(v___x_5299_, 1, v_a_5303_);
lean_ctor_set(v___x_5299_, 0, v___x_5301_);
v___x_5305_ = v___x_5299_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v___x_5301_);
lean_ctor_set(v_reuseFailAlloc_5309_, 1, v_a_5303_);
v___x_5305_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
size_t v___x_5306_; size_t v___x_5307_; 
v___x_5306_ = ((size_t)1ULL);
v___x_5307_ = lean_usize_add(v_i_5283_, v___x_5306_);
v_i_5283_ = v___x_5307_;
v_b_5284_ = v___x_5305_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5325_, lean_object* v_sz_5326_, lean_object* v_i_5327_, lean_object* v_b_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_){
_start:
{
size_t v_sz_boxed_5339_; size_t v_i_boxed_5340_; lean_object* v_res_5341_; 
v_sz_boxed_5339_ = lean_unbox_usize(v_sz_5326_);
lean_dec(v_sz_5326_);
v_i_boxed_5340_ = lean_unbox_usize(v_i_5327_);
lean_dec(v_i_5327_);
v_res_5341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5325_, v_sz_boxed_5339_, v_i_boxed_5340_, v_b_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5334_);
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
lean_dec(v___y_5331_);
lean_dec_ref(v___y_5330_);
lean_dec(v___y_5329_);
lean_dec_ref(v_as_5325_);
return v_res_5341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5342_, size_t v_sz_5343_, size_t v_i_5344_, lean_object* v_b_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_){
_start:
{
uint8_t v___x_5356_; 
v___x_5356_ = lean_usize_dec_lt(v_i_5344_, v_sz_5343_);
if (v___x_5356_ == 0)
{
lean_object* v___x_5357_; 
v___x_5357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5357_, 0, v_b_5345_);
return v___x_5357_;
}
else
{
lean_object* v_snd_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5384_; 
v_snd_5358_ = lean_ctor_get(v_b_5345_, 1);
v_isSharedCheck_5384_ = !lean_is_exclusive(v_b_5345_);
if (v_isSharedCheck_5384_ == 0)
{
lean_object* v_unused_5385_; 
v_unused_5385_ = lean_ctor_get(v_b_5345_, 0);
lean_dec(v_unused_5385_);
v___x_5360_ = v_b_5345_;
v_isShared_5361_ = v_isSharedCheck_5384_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_snd_5358_);
lean_dec(v_b_5345_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5384_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5362_; lean_object* v_a_5364_; lean_object* v_a_5371_; lean_object* v___x_5372_; 
v___x_5362_ = lean_box(0);
v_a_5371_ = lean_array_uget_borrowed(v_as_5342_, v_i_5344_);
lean_inc(v_a_5371_);
v___x_5372_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5371_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_);
if (lean_obj_tag(v___x_5372_) == 0)
{
lean_object* v_a_5373_; uint8_t v___x_5374_; 
v_a_5373_ = lean_ctor_get(v___x_5372_, 0);
lean_inc(v_a_5373_);
lean_dec_ref_known(v___x_5372_, 1);
v___x_5374_ = lean_unbox(v_a_5373_);
lean_dec(v_a_5373_);
if (v___x_5374_ == 0)
{
v_a_5364_ = v_snd_5358_;
goto v___jp_5363_;
}
else
{
lean_object* v___x_5375_; 
lean_inc(v_a_5371_);
v___x_5375_ = l_Lean_PersistentArray_push___redArg(v_snd_5358_, v_a_5371_);
v_a_5364_ = v___x_5375_;
goto v___jp_5363_;
}
}
else
{
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5383_; 
lean_del_object(v___x_5360_);
lean_dec(v_snd_5358_);
v_a_5376_ = lean_ctor_get(v___x_5372_, 0);
v_isSharedCheck_5383_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5383_ == 0)
{
v___x_5378_ = v___x_5372_;
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v___x_5372_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5381_; 
if (v_isShared_5379_ == 0)
{
v___x_5381_ = v___x_5378_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_a_5376_);
v___x_5381_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
return v___x_5381_;
}
}
}
v___jp_5363_:
{
lean_object* v___x_5366_; 
if (v_isShared_5361_ == 0)
{
lean_ctor_set(v___x_5360_, 1, v_a_5364_);
lean_ctor_set(v___x_5360_, 0, v___x_5362_);
v___x_5366_ = v___x_5360_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v___x_5362_);
lean_ctor_set(v_reuseFailAlloc_5370_, 1, v_a_5364_);
v___x_5366_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
size_t v___x_5367_; size_t v___x_5368_; lean_object* v___x_5369_; 
v___x_5367_ = ((size_t)1ULL);
v___x_5368_ = lean_usize_add(v_i_5344_, v___x_5367_);
v___x_5369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5342_, v_sz_5343_, v___x_5368_, v___x_5366_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_);
return v___x_5369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5386_, lean_object* v_sz_5387_, lean_object* v_i_5388_, lean_object* v_b_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_){
_start:
{
size_t v_sz_boxed_5400_; size_t v_i_boxed_5401_; lean_object* v_res_5402_; 
v_sz_boxed_5400_ = lean_unbox_usize(v_sz_5387_);
lean_dec(v_sz_5387_);
v_i_boxed_5401_ = lean_unbox_usize(v_i_5388_);
lean_dec(v_i_5388_);
v_res_5402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5386_, v_sz_boxed_5400_, v_i_boxed_5401_, v_b_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_);
lean_dec(v___y_5398_);
lean_dec_ref(v___y_5397_);
lean_dec(v___y_5396_);
lean_dec_ref(v___y_5395_);
lean_dec(v___y_5394_);
lean_dec_ref(v___y_5393_);
lean_dec(v___y_5392_);
lean_dec_ref(v___y_5391_);
lean_dec(v___y_5390_);
lean_dec_ref(v_as_5386_);
return v_res_5402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5403_, size_t v_sz_5404_, size_t v_i_5405_, lean_object* v_b_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_){
_start:
{
uint8_t v___x_5417_; 
v___x_5417_ = lean_usize_dec_lt(v_i_5405_, v_sz_5404_);
if (v___x_5417_ == 0)
{
lean_object* v___x_5418_; 
v___x_5418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5418_, 0, v_b_5406_);
return v___x_5418_;
}
else
{
lean_object* v_snd_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5445_; 
v_snd_5419_ = lean_ctor_get(v_b_5406_, 1);
v_isSharedCheck_5445_ = !lean_is_exclusive(v_b_5406_);
if (v_isSharedCheck_5445_ == 0)
{
lean_object* v_unused_5446_; 
v_unused_5446_ = lean_ctor_get(v_b_5406_, 0);
lean_dec(v_unused_5446_);
v___x_5421_ = v_b_5406_;
v_isShared_5422_ = v_isSharedCheck_5445_;
goto v_resetjp_5420_;
}
else
{
lean_inc(v_snd_5419_);
lean_dec(v_b_5406_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5445_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v___x_5423_; lean_object* v_a_5425_; lean_object* v_a_5432_; lean_object* v___x_5433_; 
v___x_5423_ = lean_box(0);
v_a_5432_ = lean_array_uget_borrowed(v_as_5403_, v_i_5405_);
lean_inc(v_a_5432_);
v___x_5433_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5432_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
if (lean_obj_tag(v___x_5433_) == 0)
{
lean_object* v_a_5434_; uint8_t v___x_5435_; 
v_a_5434_ = lean_ctor_get(v___x_5433_, 0);
lean_inc(v_a_5434_);
lean_dec_ref_known(v___x_5433_, 1);
v___x_5435_ = lean_unbox(v_a_5434_);
lean_dec(v_a_5434_);
if (v___x_5435_ == 0)
{
v_a_5425_ = v_snd_5419_;
goto v___jp_5424_;
}
else
{
lean_object* v___x_5436_; 
lean_inc(v_a_5432_);
v___x_5436_ = l_Lean_PersistentArray_push___redArg(v_snd_5419_, v_a_5432_);
v_a_5425_ = v___x_5436_;
goto v___jp_5424_;
}
}
else
{
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5444_; 
lean_del_object(v___x_5421_);
lean_dec(v_snd_5419_);
v_a_5437_ = lean_ctor_get(v___x_5433_, 0);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5433_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5439_ = v___x_5433_;
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v___x_5433_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5442_; 
if (v_isShared_5440_ == 0)
{
v___x_5442_ = v___x_5439_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_a_5437_);
v___x_5442_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
return v___x_5442_;
}
}
}
v___jp_5424_:
{
lean_object* v___x_5427_; 
if (v_isShared_5422_ == 0)
{
lean_ctor_set(v___x_5421_, 1, v_a_5425_);
lean_ctor_set(v___x_5421_, 0, v___x_5423_);
v___x_5427_ = v___x_5421_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v___x_5423_);
lean_ctor_set(v_reuseFailAlloc_5431_, 1, v_a_5425_);
v___x_5427_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
size_t v___x_5428_; size_t v___x_5429_; 
v___x_5428_ = ((size_t)1ULL);
v___x_5429_ = lean_usize_add(v_i_5405_, v___x_5428_);
v_i_5405_ = v___x_5429_;
v_b_5406_ = v___x_5427_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5447_, lean_object* v_sz_5448_, lean_object* v_i_5449_, lean_object* v_b_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_){
_start:
{
size_t v_sz_boxed_5461_; size_t v_i_boxed_5462_; lean_object* v_res_5463_; 
v_sz_boxed_5461_ = lean_unbox_usize(v_sz_5448_);
lean_dec(v_sz_5448_);
v_i_boxed_5462_ = lean_unbox_usize(v_i_5449_);
lean_dec(v_i_5449_);
v_res_5463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5447_, v_sz_boxed_5461_, v_i_boxed_5462_, v_b_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
lean_dec(v___y_5453_);
lean_dec_ref(v___y_5452_);
lean_dec(v___y_5451_);
lean_dec_ref(v_as_5447_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5464_, size_t v_sz_5465_, size_t v_i_5466_, lean_object* v_b_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_){
_start:
{
uint8_t v___x_5478_; 
v___x_5478_ = lean_usize_dec_lt(v_i_5466_, v_sz_5465_);
if (v___x_5478_ == 0)
{
lean_object* v___x_5479_; 
v___x_5479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5479_, 0, v_b_5467_);
return v___x_5479_;
}
else
{
lean_object* v_snd_5480_; lean_object* v___x_5482_; uint8_t v_isShared_5483_; uint8_t v_isSharedCheck_5506_; 
v_snd_5480_ = lean_ctor_get(v_b_5467_, 1);
v_isSharedCheck_5506_ = !lean_is_exclusive(v_b_5467_);
if (v_isSharedCheck_5506_ == 0)
{
lean_object* v_unused_5507_; 
v_unused_5507_ = lean_ctor_get(v_b_5467_, 0);
lean_dec(v_unused_5507_);
v___x_5482_ = v_b_5467_;
v_isShared_5483_ = v_isSharedCheck_5506_;
goto v_resetjp_5481_;
}
else
{
lean_inc(v_snd_5480_);
lean_dec(v_b_5467_);
v___x_5482_ = lean_box(0);
v_isShared_5483_ = v_isSharedCheck_5506_;
goto v_resetjp_5481_;
}
v_resetjp_5481_:
{
lean_object* v___x_5484_; lean_object* v_a_5486_; lean_object* v_a_5493_; lean_object* v___x_5494_; 
v___x_5484_ = lean_box(0);
v_a_5493_ = lean_array_uget_borrowed(v_as_5464_, v_i_5466_);
lean_inc(v_a_5493_);
v___x_5494_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5493_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v_a_5495_; uint8_t v___x_5496_; 
v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
lean_inc(v_a_5495_);
lean_dec_ref_known(v___x_5494_, 1);
v___x_5496_ = lean_unbox(v_a_5495_);
lean_dec(v_a_5495_);
if (v___x_5496_ == 0)
{
v_a_5486_ = v_snd_5480_;
goto v___jp_5485_;
}
else
{
lean_object* v___x_5497_; 
lean_inc(v_a_5493_);
v___x_5497_ = l_Lean_PersistentArray_push___redArg(v_snd_5480_, v_a_5493_);
v_a_5486_ = v___x_5497_;
goto v___jp_5485_;
}
}
else
{
lean_object* v_a_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5505_; 
lean_del_object(v___x_5482_);
lean_dec(v_snd_5480_);
v_a_5498_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5500_ = v___x_5494_;
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_a_5498_);
lean_dec(v___x_5494_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v___x_5503_; 
if (v_isShared_5501_ == 0)
{
v___x_5503_ = v___x_5500_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_a_5498_);
v___x_5503_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
return v___x_5503_;
}
}
}
v___jp_5485_:
{
lean_object* v___x_5488_; 
if (v_isShared_5483_ == 0)
{
lean_ctor_set(v___x_5482_, 1, v_a_5486_);
lean_ctor_set(v___x_5482_, 0, v___x_5484_);
v___x_5488_ = v___x_5482_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v___x_5484_);
lean_ctor_set(v_reuseFailAlloc_5492_, 1, v_a_5486_);
v___x_5488_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
size_t v___x_5489_; size_t v___x_5490_; lean_object* v___x_5491_; 
v___x_5489_ = ((size_t)1ULL);
v___x_5490_ = lean_usize_add(v_i_5466_, v___x_5489_);
v___x_5491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5464_, v_sz_5465_, v___x_5490_, v___x_5488_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
return v___x_5491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5508_, lean_object* v_sz_5509_, lean_object* v_i_5510_, lean_object* v_b_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_){
_start:
{
size_t v_sz_boxed_5522_; size_t v_i_boxed_5523_; lean_object* v_res_5524_; 
v_sz_boxed_5522_ = lean_unbox_usize(v_sz_5509_);
lean_dec(v_sz_5509_);
v_i_boxed_5523_ = lean_unbox_usize(v_i_5510_);
lean_dec(v_i_5510_);
v_res_5524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5508_, v_sz_boxed_5522_, v_i_boxed_5523_, v_b_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_);
lean_dec(v___y_5520_);
lean_dec_ref(v___y_5519_);
lean_dec(v___y_5518_);
lean_dec_ref(v___y_5517_);
lean_dec(v___y_5516_);
lean_dec_ref(v___y_5515_);
lean_dec(v___y_5514_);
lean_dec_ref(v___y_5513_);
lean_dec(v___y_5512_);
lean_dec_ref(v_as_5508_);
return v_res_5524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5525_, lean_object* v_n_5526_, lean_object* v_b_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_){
_start:
{
if (lean_obj_tag(v_n_5526_) == 0)
{
lean_object* v_cs_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; size_t v_sz_5541_; size_t v___x_5542_; lean_object* v___x_5543_; 
v_cs_5538_ = lean_ctor_get(v_n_5526_, 0);
v___x_5539_ = lean_box(0);
v___x_5540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5540_, 0, v___x_5539_);
lean_ctor_set(v___x_5540_, 1, v_b_5527_);
v_sz_5541_ = lean_array_size(v_cs_5538_);
v___x_5542_ = ((size_t)0ULL);
v___x_5543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5525_, v_cs_5538_, v_sz_5541_, v___x_5542_, v___x_5540_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_);
if (lean_obj_tag(v___x_5543_) == 0)
{
lean_object* v_a_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5558_; 
v_a_5544_ = lean_ctor_get(v___x_5543_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5543_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5546_ = v___x_5543_;
v_isShared_5547_ = v_isSharedCheck_5558_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_a_5544_);
lean_dec(v___x_5543_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5558_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v_fst_5548_; 
v_fst_5548_ = lean_ctor_get(v_a_5544_, 0);
if (lean_obj_tag(v_fst_5548_) == 0)
{
lean_object* v_snd_5549_; lean_object* v___x_5550_; lean_object* v___x_5552_; 
v_snd_5549_ = lean_ctor_get(v_a_5544_, 1);
lean_inc(v_snd_5549_);
lean_dec(v_a_5544_);
v___x_5550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5550_, 0, v_snd_5549_);
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 0, v___x_5550_);
v___x_5552_ = v___x_5546_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v___x_5550_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
else
{
lean_object* v_val_5554_; lean_object* v___x_5556_; 
lean_inc_ref(v_fst_5548_);
lean_dec(v_a_5544_);
v_val_5554_ = lean_ctor_get(v_fst_5548_, 0);
lean_inc(v_val_5554_);
lean_dec_ref_known(v_fst_5548_, 1);
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 0, v_val_5554_);
v___x_5556_ = v___x_5546_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_val_5554_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
else
{
lean_object* v_a_5559_; lean_object* v___x_5561_; uint8_t v_isShared_5562_; uint8_t v_isSharedCheck_5566_; 
v_a_5559_ = lean_ctor_get(v___x_5543_, 0);
v_isSharedCheck_5566_ = !lean_is_exclusive(v___x_5543_);
if (v_isSharedCheck_5566_ == 0)
{
v___x_5561_ = v___x_5543_;
v_isShared_5562_ = v_isSharedCheck_5566_;
goto v_resetjp_5560_;
}
else
{
lean_inc(v_a_5559_);
lean_dec(v___x_5543_);
v___x_5561_ = lean_box(0);
v_isShared_5562_ = v_isSharedCheck_5566_;
goto v_resetjp_5560_;
}
v_resetjp_5560_:
{
lean_object* v___x_5564_; 
if (v_isShared_5562_ == 0)
{
v___x_5564_ = v___x_5561_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_a_5559_);
v___x_5564_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
return v___x_5564_;
}
}
}
}
else
{
lean_object* v_vs_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; size_t v_sz_5570_; size_t v___x_5571_; lean_object* v___x_5572_; 
v_vs_5567_ = lean_ctor_get(v_n_5526_, 0);
v___x_5568_ = lean_box(0);
v___x_5569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5569_, 0, v___x_5568_);
lean_ctor_set(v___x_5569_, 1, v_b_5527_);
v_sz_5570_ = lean_array_size(v_vs_5567_);
v___x_5571_ = ((size_t)0ULL);
v___x_5572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5567_, v_sz_5570_, v___x_5571_, v___x_5569_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_);
if (lean_obj_tag(v___x_5572_) == 0)
{
lean_object* v_a_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5587_; 
v_a_5573_ = lean_ctor_get(v___x_5572_, 0);
v_isSharedCheck_5587_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5587_ == 0)
{
v___x_5575_ = v___x_5572_;
v_isShared_5576_ = v_isSharedCheck_5587_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_a_5573_);
lean_dec(v___x_5572_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5587_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v_fst_5577_; 
v_fst_5577_ = lean_ctor_get(v_a_5573_, 0);
if (lean_obj_tag(v_fst_5577_) == 0)
{
lean_object* v_snd_5578_; lean_object* v___x_5579_; lean_object* v___x_5581_; 
v_snd_5578_ = lean_ctor_get(v_a_5573_, 1);
lean_inc(v_snd_5578_);
lean_dec(v_a_5573_);
v___x_5579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5579_, 0, v_snd_5578_);
if (v_isShared_5576_ == 0)
{
lean_ctor_set(v___x_5575_, 0, v___x_5579_);
v___x_5581_ = v___x_5575_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v___x_5579_);
v___x_5581_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
return v___x_5581_;
}
}
else
{
lean_object* v_val_5583_; lean_object* v___x_5585_; 
lean_inc_ref(v_fst_5577_);
lean_dec(v_a_5573_);
v_val_5583_ = lean_ctor_get(v_fst_5577_, 0);
lean_inc(v_val_5583_);
lean_dec_ref_known(v_fst_5577_, 1);
if (v_isShared_5576_ == 0)
{
lean_ctor_set(v___x_5575_, 0, v_val_5583_);
v___x_5585_ = v___x_5575_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_val_5583_);
v___x_5585_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
return v___x_5585_;
}
}
}
}
else
{
lean_object* v_a_5588_; lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5595_; 
v_a_5588_ = lean_ctor_get(v___x_5572_, 0);
v_isSharedCheck_5595_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5595_ == 0)
{
v___x_5590_ = v___x_5572_;
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
else
{
lean_inc(v_a_5588_);
lean_dec(v___x_5572_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v___x_5593_; 
if (v_isShared_5591_ == 0)
{
v___x_5593_ = v___x_5590_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5588_);
v___x_5593_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
return v___x_5593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5596_, lean_object* v_as_5597_, size_t v_sz_5598_, size_t v_i_5599_, lean_object* v_b_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_){
_start:
{
uint8_t v___x_5611_; 
v___x_5611_ = lean_usize_dec_lt(v_i_5599_, v_sz_5598_);
if (v___x_5611_ == 0)
{
lean_object* v___x_5612_; 
v___x_5612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5612_, 0, v_b_5600_);
return v___x_5612_;
}
else
{
lean_object* v_snd_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5647_; 
v_snd_5613_ = lean_ctor_get(v_b_5600_, 1);
v_isSharedCheck_5647_ = !lean_is_exclusive(v_b_5600_);
if (v_isSharedCheck_5647_ == 0)
{
lean_object* v_unused_5648_; 
v_unused_5648_ = lean_ctor_get(v_b_5600_, 0);
lean_dec(v_unused_5648_);
v___x_5615_ = v_b_5600_;
v_isShared_5616_ = v_isSharedCheck_5647_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_snd_5613_);
lean_dec(v_b_5600_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5647_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v___x_5617_; lean_object* v_a_5618_; lean_object* v___x_5619_; 
v___x_5617_ = lean_box(0);
v_a_5618_ = lean_array_uget_borrowed(v_as_5597_, v_i_5599_);
lean_inc(v_snd_5613_);
v___x_5619_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5596_, v_a_5618_, v_snd_5613_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_);
if (lean_obj_tag(v___x_5619_) == 0)
{
lean_object* v_a_5620_; lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5638_; 
v_a_5620_ = lean_ctor_get(v___x_5619_, 0);
v_isSharedCheck_5638_ = !lean_is_exclusive(v___x_5619_);
if (v_isSharedCheck_5638_ == 0)
{
v___x_5622_ = v___x_5619_;
v_isShared_5623_ = v_isSharedCheck_5638_;
goto v_resetjp_5621_;
}
else
{
lean_inc(v_a_5620_);
lean_dec(v___x_5619_);
v___x_5622_ = lean_box(0);
v_isShared_5623_ = v_isSharedCheck_5638_;
goto v_resetjp_5621_;
}
v_resetjp_5621_:
{
if (lean_obj_tag(v_a_5620_) == 0)
{
lean_object* v___x_5624_; lean_object* v___x_5626_; 
v___x_5624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5624_, 0, v_a_5620_);
if (v_isShared_5616_ == 0)
{
lean_ctor_set(v___x_5615_, 0, v___x_5624_);
v___x_5626_ = v___x_5615_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v___x_5624_);
lean_ctor_set(v_reuseFailAlloc_5630_, 1, v_snd_5613_);
v___x_5626_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
lean_object* v___x_5628_; 
if (v_isShared_5623_ == 0)
{
lean_ctor_set(v___x_5622_, 0, v___x_5626_);
v___x_5628_ = v___x_5622_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v___x_5626_);
v___x_5628_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
return v___x_5628_;
}
}
}
else
{
lean_object* v_a_5631_; lean_object* v___x_5633_; 
lean_del_object(v___x_5622_);
lean_dec(v_snd_5613_);
v_a_5631_ = lean_ctor_get(v_a_5620_, 0);
lean_inc(v_a_5631_);
lean_dec_ref_known(v_a_5620_, 1);
if (v_isShared_5616_ == 0)
{
lean_ctor_set(v___x_5615_, 1, v_a_5631_);
lean_ctor_set(v___x_5615_, 0, v___x_5617_);
v___x_5633_ = v___x_5615_;
goto v_reusejp_5632_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v___x_5617_);
lean_ctor_set(v_reuseFailAlloc_5637_, 1, v_a_5631_);
v___x_5633_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5632_;
}
v_reusejp_5632_:
{
size_t v___x_5634_; size_t v___x_5635_; 
v___x_5634_ = ((size_t)1ULL);
v___x_5635_ = lean_usize_add(v_i_5599_, v___x_5634_);
v_i_5599_ = v___x_5635_;
v_b_5600_ = v___x_5633_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5639_; lean_object* v___x_5641_; uint8_t v_isShared_5642_; uint8_t v_isSharedCheck_5646_; 
lean_del_object(v___x_5615_);
lean_dec(v_snd_5613_);
v_a_5639_ = lean_ctor_get(v___x_5619_, 0);
v_isSharedCheck_5646_ = !lean_is_exclusive(v___x_5619_);
if (v_isSharedCheck_5646_ == 0)
{
v___x_5641_ = v___x_5619_;
v_isShared_5642_ = v_isSharedCheck_5646_;
goto v_resetjp_5640_;
}
else
{
lean_inc(v_a_5639_);
lean_dec(v___x_5619_);
v___x_5641_ = lean_box(0);
v_isShared_5642_ = v_isSharedCheck_5646_;
goto v_resetjp_5640_;
}
v_resetjp_5640_:
{
lean_object* v___x_5644_; 
if (v_isShared_5642_ == 0)
{
v___x_5644_ = v___x_5641_;
goto v_reusejp_5643_;
}
else
{
lean_object* v_reuseFailAlloc_5645_; 
v_reuseFailAlloc_5645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
v___x_5644_ = v_reuseFailAlloc_5645_;
goto v_reusejp_5643_;
}
v_reusejp_5643_:
{
return v___x_5644_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5649_, lean_object* v_as_5650_, lean_object* v_sz_5651_, lean_object* v_i_5652_, lean_object* v_b_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_){
_start:
{
size_t v_sz_boxed_5664_; size_t v_i_boxed_5665_; lean_object* v_res_5666_; 
v_sz_boxed_5664_ = lean_unbox_usize(v_sz_5651_);
lean_dec(v_sz_5651_);
v_i_boxed_5665_ = lean_unbox_usize(v_i_5652_);
lean_dec(v_i_5652_);
v_res_5666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5649_, v_as_5650_, v_sz_boxed_5664_, v_i_boxed_5665_, v_b_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
lean_dec(v___y_5658_);
lean_dec_ref(v___y_5657_);
lean_dec(v___y_5656_);
lean_dec_ref(v___y_5655_);
lean_dec(v___y_5654_);
lean_dec_ref(v_as_5650_);
lean_dec_ref(v_init_5649_);
return v_res_5666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5667_, lean_object* v_n_5668_, lean_object* v_b_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_){
_start:
{
lean_object* v_res_5680_; 
v_res_5680_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5667_, v_n_5668_, v_b_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_);
lean_dec(v___y_5678_);
lean_dec_ref(v___y_5677_);
lean_dec(v___y_5676_);
lean_dec_ref(v___y_5675_);
lean_dec(v___y_5674_);
lean_dec_ref(v___y_5673_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
lean_dec(v___y_5670_);
lean_dec_ref(v_n_5668_);
lean_dec_ref(v_init_5667_);
return v_res_5680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5681_, lean_object* v_init_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_){
_start:
{
lean_object* v_root_5693_; lean_object* v_tail_5694_; lean_object* v___x_5695_; 
v_root_5693_ = lean_ctor_get(v_t_5681_, 0);
v_tail_5694_ = lean_ctor_get(v_t_5681_, 1);
lean_inc_ref(v_init_5682_);
v___x_5695_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5682_, v_root_5693_, v_init_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
lean_dec_ref(v_init_5682_);
if (lean_obj_tag(v___x_5695_) == 0)
{
lean_object* v_a_5696_; lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5732_; 
v_a_5696_ = lean_ctor_get(v___x_5695_, 0);
v_isSharedCheck_5732_ = !lean_is_exclusive(v___x_5695_);
if (v_isSharedCheck_5732_ == 0)
{
v___x_5698_ = v___x_5695_;
v_isShared_5699_ = v_isSharedCheck_5732_;
goto v_resetjp_5697_;
}
else
{
lean_inc(v_a_5696_);
lean_dec(v___x_5695_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5732_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
if (lean_obj_tag(v_a_5696_) == 0)
{
lean_object* v_a_5700_; lean_object* v___x_5702_; 
v_a_5700_ = lean_ctor_get(v_a_5696_, 0);
lean_inc(v_a_5700_);
lean_dec_ref_known(v_a_5696_, 1);
if (v_isShared_5699_ == 0)
{
lean_ctor_set(v___x_5698_, 0, v_a_5700_);
v___x_5702_ = v___x_5698_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_a_5700_);
v___x_5702_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
return v___x_5702_;
}
}
else
{
lean_object* v_a_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; size_t v_sz_5707_; size_t v___x_5708_; lean_object* v___x_5709_; 
lean_del_object(v___x_5698_);
v_a_5704_ = lean_ctor_get(v_a_5696_, 0);
lean_inc(v_a_5704_);
lean_dec_ref_known(v_a_5696_, 1);
v___x_5705_ = lean_box(0);
v___x_5706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5706_, 0, v___x_5705_);
lean_ctor_set(v___x_5706_, 1, v_a_5704_);
v_sz_5707_ = lean_array_size(v_tail_5694_);
v___x_5708_ = ((size_t)0ULL);
v___x_5709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5694_, v_sz_5707_, v___x_5708_, v___x_5706_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
if (lean_obj_tag(v___x_5709_) == 0)
{
lean_object* v_a_5710_; lean_object* v___x_5712_; uint8_t v_isShared_5713_; uint8_t v_isSharedCheck_5723_; 
v_a_5710_ = lean_ctor_get(v___x_5709_, 0);
v_isSharedCheck_5723_ = !lean_is_exclusive(v___x_5709_);
if (v_isSharedCheck_5723_ == 0)
{
v___x_5712_ = v___x_5709_;
v_isShared_5713_ = v_isSharedCheck_5723_;
goto v_resetjp_5711_;
}
else
{
lean_inc(v_a_5710_);
lean_dec(v___x_5709_);
v___x_5712_ = lean_box(0);
v_isShared_5713_ = v_isSharedCheck_5723_;
goto v_resetjp_5711_;
}
v_resetjp_5711_:
{
lean_object* v_fst_5714_; 
v_fst_5714_ = lean_ctor_get(v_a_5710_, 0);
if (lean_obj_tag(v_fst_5714_) == 0)
{
lean_object* v_snd_5715_; lean_object* v___x_5717_; 
v_snd_5715_ = lean_ctor_get(v_a_5710_, 1);
lean_inc(v_snd_5715_);
lean_dec(v_a_5710_);
if (v_isShared_5713_ == 0)
{
lean_ctor_set(v___x_5712_, 0, v_snd_5715_);
v___x_5717_ = v___x_5712_;
goto v_reusejp_5716_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v_snd_5715_);
v___x_5717_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5716_;
}
v_reusejp_5716_:
{
return v___x_5717_;
}
}
else
{
lean_object* v_val_5719_; lean_object* v___x_5721_; 
lean_inc_ref(v_fst_5714_);
lean_dec(v_a_5710_);
v_val_5719_ = lean_ctor_get(v_fst_5714_, 0);
lean_inc(v_val_5719_);
lean_dec_ref_known(v_fst_5714_, 1);
if (v_isShared_5713_ == 0)
{
lean_ctor_set(v___x_5712_, 0, v_val_5719_);
v___x_5721_ = v___x_5712_;
goto v_reusejp_5720_;
}
else
{
lean_object* v_reuseFailAlloc_5722_; 
v_reuseFailAlloc_5722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5722_, 0, v_val_5719_);
v___x_5721_ = v_reuseFailAlloc_5722_;
goto v_reusejp_5720_;
}
v_reusejp_5720_:
{
return v___x_5721_;
}
}
}
}
else
{
lean_object* v_a_5724_; lean_object* v___x_5726_; uint8_t v_isShared_5727_; uint8_t v_isSharedCheck_5731_; 
v_a_5724_ = lean_ctor_get(v___x_5709_, 0);
v_isSharedCheck_5731_ = !lean_is_exclusive(v___x_5709_);
if (v_isSharedCheck_5731_ == 0)
{
v___x_5726_ = v___x_5709_;
v_isShared_5727_ = v_isSharedCheck_5731_;
goto v_resetjp_5725_;
}
else
{
lean_inc(v_a_5724_);
lean_dec(v___x_5709_);
v___x_5726_ = lean_box(0);
v_isShared_5727_ = v_isSharedCheck_5731_;
goto v_resetjp_5725_;
}
v_resetjp_5725_:
{
lean_object* v___x_5729_; 
if (v_isShared_5727_ == 0)
{
v___x_5729_ = v___x_5726_;
goto v_reusejp_5728_;
}
else
{
lean_object* v_reuseFailAlloc_5730_; 
v_reuseFailAlloc_5730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5730_, 0, v_a_5724_);
v___x_5729_ = v_reuseFailAlloc_5730_;
goto v_reusejp_5728_;
}
v_reusejp_5728_:
{
return v___x_5729_;
}
}
}
}
}
}
else
{
lean_object* v_a_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5740_; 
v_a_5733_ = lean_ctor_get(v___x_5695_, 0);
v_isSharedCheck_5740_ = !lean_is_exclusive(v___x_5695_);
if (v_isSharedCheck_5740_ == 0)
{
v___x_5735_ = v___x_5695_;
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_a_5733_);
lean_dec(v___x_5695_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v___x_5738_; 
if (v_isShared_5736_ == 0)
{
v___x_5738_ = v___x_5735_;
goto v_reusejp_5737_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v_a_5733_);
v___x_5738_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5737_;
}
v_reusejp_5737_:
{
return v___x_5738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5741_, lean_object* v_init_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_){
_start:
{
lean_object* v_res_5753_; 
v_res_5753_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5741_, v_init_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_, v___y_5750_, v___y_5751_);
lean_dec(v___y_5751_);
lean_dec_ref(v___y_5750_);
lean_dec(v___y_5749_);
lean_dec_ref(v___y_5748_);
lean_dec(v___y_5747_);
lean_dec_ref(v___y_5746_);
lean_dec(v___y_5745_);
lean_dec_ref(v___y_5744_);
lean_dec(v___y_5743_);
lean_dec_ref(v_t_5741_);
return v_res_5753_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; 
v___x_5754_ = lean_unsigned_to_nat(32u);
v___x_5755_ = lean_mk_empty_array_with_capacity(v___x_5754_);
v___x_5756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5755_);
return v___x_5756_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v_result_5762_; 
v___x_5757_ = ((size_t)5ULL);
v___x_5758_ = lean_unsigned_to_nat(0u);
v___x_5759_ = lean_unsigned_to_nat(32u);
v___x_5760_ = lean_mk_empty_array_with_capacity(v___x_5759_);
v___x_5761_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5762_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5762_, 0, v___x_5761_);
lean_ctor_set(v_result_5762_, 1, v___x_5760_);
lean_ctor_set(v_result_5762_, 2, v___x_5758_);
lean_ctor_set(v_result_5762_, 3, v___x_5758_);
lean_ctor_set_usize(v_result_5762_, 4, v___x_5757_);
return v_result_5762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_){
_start:
{
lean_object* v_result_5774_; lean_object* v___x_5775_; 
v_result_5774_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5775_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5763_, v_result_5774_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_);
return v___x_5775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_){
_start:
{
lean_object* v_res_5787_; 
v_res_5787_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5776_, v_a_5777_, v_a_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_);
lean_dec(v_a_5785_);
lean_dec_ref(v_a_5784_);
lean_dec(v_a_5783_);
lean_dec_ref(v_a_5782_);
lean_dec(v_a_5781_);
lean_dec_ref(v_a_5780_);
lean_dec(v_a_5779_);
lean_dec_ref(v_a_5778_);
lean_dec(v_a_5777_);
lean_dec_ref(v_thms_5776_);
return v_res_5787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(lean_object* v___x_5788_, uint8_t v___x_5789_, uint8_t v___x_5790_, lean_object* v_keepIdentParam_5791_, lean_object* v_x_5792_, lean_object* v_mod_x3f_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_){
_start:
{
lean_object* v___x_5801_; lean_object* v_id_5802_; 
v___x_5801_ = lean_unsigned_to_nat(2u);
v_id_5802_ = l_Lean_Syntax_getArg(v___x_5788_, v___x_5801_);
if (v___x_5789_ == 0)
{
lean_object* v___x_5803_; uint8_t v___x_5804_; 
v___x_5803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v_id_5802_);
v___x_5804_ = l_Lean_Syntax_isOfKind(v_id_5802_, v___x_5803_);
if (v___x_5804_ == 0)
{
lean_object* v___x_5805_; lean_object* v___x_5806_; 
lean_dec(v_id_5802_);
lean_dec(v_mod_x3f_5793_);
lean_dec_ref(v_keepIdentParam_5791_);
v___x_5805_ = lean_box(v___x_5790_);
v___x_5806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5806_, 0, v___x_5805_);
return v___x_5806_;
}
else
{
lean_object* v___x_5807_; 
lean_inc(v___y_5799_);
lean_inc_ref(v___y_5798_);
lean_inc(v___y_5797_);
lean_inc_ref(v___y_5796_);
lean_inc(v___y_5795_);
lean_inc_ref(v___y_5794_);
v___x_5807_ = lean_apply_9(v_keepIdentParam_5791_, v_mod_x3f_5793_, v_id_5802_, v___y_5794_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_, lean_box(0));
return v___x_5807_;
}
}
else
{
lean_object* v___x_5808_; 
lean_inc(v___y_5799_);
lean_inc_ref(v___y_5798_);
lean_inc(v___y_5797_);
lean_inc_ref(v___y_5796_);
lean_inc(v___y_5795_);
lean_inc_ref(v___y_5794_);
v___x_5808_ = lean_apply_9(v_keepIdentParam_5791_, v_mod_x3f_5793_, v_id_5802_, v___y_5794_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_, lean_box(0));
return v___x_5808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1___boxed(lean_object* v___x_5809_, lean_object* v___x_5810_, lean_object* v___x_5811_, lean_object* v_keepIdentParam_5812_, lean_object* v_x_5813_, lean_object* v_mod_x3f_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_){
_start:
{
uint8_t v___x_6830__boxed_5822_; uint8_t v___x_6831__boxed_5823_; lean_object* v_res_5824_; 
v___x_6830__boxed_5822_ = lean_unbox(v___x_5810_);
v___x_6831__boxed_5823_ = lean_unbox(v___x_5811_);
v_res_5824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(v___x_5809_, v___x_6830__boxed_5822_, v___x_6831__boxed_5823_, v_keepIdentParam_5812_, v_x_5813_, v_mod_x3f_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
lean_dec(v___y_5820_);
lean_dec_ref(v___y_5819_);
lean_dec(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___y_5816_);
lean_dec_ref(v___y_5815_);
lean_dec(v___x_5809_);
return v_res_5824_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0(void){
_start:
{
lean_object* v___x_5825_; lean_object* v___x_5826_; 
v___x_5825_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_5826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5826_, 0, v___x_5825_);
return v___x_5826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0(uint8_t v___x_5827_, uint8_t v___x_5828_, lean_object* v_mod_x3f_5829_, lean_object* v_id_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_){
_start:
{
lean_object* v___y_5839_; uint8_t v___y_5840_; lean_object* v___y_5845_; lean_object* v___y_5846_; lean_object* v___y_5847_; lean_object* v___y_5848_; lean_object* v___x_5887_; lean_object* v___x_5888_; 
v___x_5887_ = l_Lean_TSyntax_getId(v_id_5830_);
v___x_5888_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_5887_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_);
if (lean_obj_tag(v___x_5888_) == 0)
{
lean_object* v_a_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5899_; 
v_a_5889_ = lean_ctor_get(v___x_5888_, 0);
v_isSharedCheck_5899_ = !lean_is_exclusive(v___x_5888_);
if (v_isSharedCheck_5899_ == 0)
{
v___x_5891_ = v___x_5888_;
v_isShared_5892_ = v_isSharedCheck_5899_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_a_5889_);
lean_dec(v___x_5888_);
v___x_5891_ = lean_box(0);
v_isShared_5892_ = v_isSharedCheck_5899_;
goto v_resetjp_5890_;
}
v_resetjp_5890_:
{
if (lean_obj_tag(v_a_5889_) == 1)
{
lean_object* v_val_5893_; lean_object* v_snd_5894_; 
v_val_5893_ = lean_ctor_get(v_a_5889_, 0);
lean_inc(v_val_5893_);
lean_dec_ref_known(v_a_5889_, 1);
v_snd_5894_ = lean_ctor_get(v_val_5893_, 1);
lean_inc(v_snd_5894_);
lean_dec(v_val_5893_);
if (lean_obj_tag(v_snd_5894_) == 1)
{
lean_object* v___x_5895_; lean_object* v___x_5897_; 
lean_dec_ref_known(v_snd_5894_, 2);
lean_dec(v_id_5830_);
lean_dec(v_mod_x3f_5829_);
v___x_5895_ = lean_box(v___x_5828_);
if (v_isShared_5892_ == 0)
{
lean_ctor_set(v___x_5891_, 0, v___x_5895_);
v___x_5897_ = v___x_5891_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_5898_; 
v_reuseFailAlloc_5898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5898_, 0, v___x_5895_);
v___x_5897_ = v_reuseFailAlloc_5898_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
return v___x_5897_;
}
}
else
{
lean_dec(v_snd_5894_);
lean_del_object(v___x_5891_);
goto v___jp_5859_;
}
}
else
{
lean_del_object(v___x_5891_);
lean_dec(v_a_5889_);
goto v___jp_5859_;
}
}
}
else
{
lean_object* v_a_5900_; lean_object* v___x_5902_; uint8_t v_isShared_5903_; uint8_t v_isSharedCheck_5907_; 
lean_dec(v_id_5830_);
lean_dec(v_mod_x3f_5829_);
v_a_5900_ = lean_ctor_get(v___x_5888_, 0);
v_isSharedCheck_5907_ = !lean_is_exclusive(v___x_5888_);
if (v_isSharedCheck_5907_ == 0)
{
v___x_5902_ = v___x_5888_;
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
else
{
lean_inc(v_a_5900_);
lean_dec(v___x_5888_);
v___x_5902_ = lean_box(0);
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
v_resetjp_5901_:
{
lean_object* v___x_5905_; 
if (v_isShared_5903_ == 0)
{
v___x_5905_ = v___x_5902_;
goto v_reusejp_5904_;
}
else
{
lean_object* v_reuseFailAlloc_5906_; 
v_reuseFailAlloc_5906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5906_, 0, v_a_5900_);
v___x_5905_ = v_reuseFailAlloc_5906_;
goto v_reusejp_5904_;
}
v_reusejp_5904_:
{
return v___x_5905_;
}
}
}
v___jp_5838_:
{
if (v___y_5840_ == 0)
{
lean_object* v___x_5841_; lean_object* v___x_5842_; 
lean_dec_ref(v___y_5839_);
v___x_5841_ = lean_box(v___y_5840_);
v___x_5842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5842_, 0, v___x_5841_);
return v___x_5842_;
}
else
{
lean_object* v___x_5843_; 
v___x_5843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5843_, 0, v___y_5839_);
return v___x_5843_;
}
}
v___jp_5844_:
{
lean_object* v___x_5849_; 
v___x_5849_ = l_Lean_realizeGlobalConstNoOverload(v_id_5830_, v___y_5847_, v___y_5848_);
if (lean_obj_tag(v___x_5849_) == 0)
{
lean_object* v_a_5850_; lean_object* v___x_5851_; 
v_a_5850_ = lean_ctor_get(v___x_5849_, 0);
lean_inc_n(v_a_5850_, 2);
lean_dec_ref_known(v___x_5849_, 1);
v___x_5851_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_a_5850_, v___x_5827_, v___y_5847_, v___y_5848_);
if (lean_obj_tag(v___x_5851_) == 0)
{
lean_object* v_a_5852_; uint8_t v___x_5853_; 
v_a_5852_ = lean_ctor_get(v___x_5851_, 0);
v___x_5853_ = lean_unbox(v_a_5852_);
if (v___x_5853_ == 0)
{
lean_object* v___x_5854_; lean_object* v___x_5855_; 
lean_dec_ref_known(v___x_5851_, 1);
v___x_5854_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___closed__0);
v___x_5855_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_isFactDecl(v_a_5850_, v___x_5854_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_);
return v___x_5855_;
}
else
{
lean_dec(v_a_5850_);
return v___x_5851_;
}
}
else
{
lean_dec(v_a_5850_);
return v___x_5851_;
}
}
else
{
lean_object* v_a_5856_; uint8_t v___x_5857_; 
v_a_5856_ = lean_ctor_get(v___x_5849_, 0);
lean_inc(v_a_5856_);
lean_dec_ref_known(v___x_5849_, 1);
v___x_5857_ = l_Lean_Exception_isInterrupt(v_a_5856_);
if (v___x_5857_ == 0)
{
uint8_t v___x_5858_; 
lean_inc(v_a_5856_);
v___x_5858_ = l_Lean_Exception_isRuntime(v_a_5856_);
v___y_5839_ = v_a_5856_;
v___y_5840_ = v___x_5858_;
goto v___jp_5838_;
}
else
{
v___y_5839_ = v_a_5856_;
v___y_5840_ = v___x_5857_;
goto v___jp_5838_;
}
}
}
v___jp_5859_:
{
if (lean_obj_tag(v_mod_x3f_5829_) == 1)
{
lean_object* v_val_5860_; lean_object* v___x_5861_; 
v_val_5860_ = lean_ctor_get(v_mod_x3f_5829_, 0);
lean_inc(v_val_5860_);
lean_dec_ref_known(v_mod_x3f_5829_, 1);
v___x_5861_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_5860_, v___y_5835_, v___y_5836_);
if (lean_obj_tag(v___x_5861_) == 0)
{
lean_object* v_a_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5878_; 
v_a_5862_ = lean_ctor_get(v___x_5861_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5861_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5864_ = v___x_5861_;
v_isShared_5865_ = v_isSharedCheck_5878_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_a_5862_);
lean_dec(v___x_5861_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5878_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
switch(lean_obj_tag(v_a_5862_))
{
case 0:
{
lean_object* v___x_5866_; lean_object* v___x_5868_; 
lean_dec_ref_known(v_a_5862_, 1);
lean_dec(v_id_5830_);
v___x_5866_ = lean_box(v___x_5827_);
if (v_isShared_5865_ == 0)
{
lean_ctor_set(v___x_5864_, 0, v___x_5866_);
v___x_5868_ = v___x_5864_;
goto v_reusejp_5867_;
}
else
{
lean_object* v_reuseFailAlloc_5869_; 
v_reuseFailAlloc_5869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5869_, 0, v___x_5866_);
v___x_5868_ = v_reuseFailAlloc_5869_;
goto v_reusejp_5867_;
}
v_reusejp_5867_:
{
return v___x_5868_;
}
}
case 2:
{
lean_object* v___x_5870_; lean_object* v___x_5872_; 
lean_dec(v_id_5830_);
v___x_5870_ = lean_box(v___x_5827_);
if (v_isShared_5865_ == 0)
{
lean_ctor_set(v___x_5864_, 0, v___x_5870_);
v___x_5872_ = v___x_5864_;
goto v_reusejp_5871_;
}
else
{
lean_object* v_reuseFailAlloc_5873_; 
v_reuseFailAlloc_5873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5873_, 0, v___x_5870_);
v___x_5872_ = v_reuseFailAlloc_5873_;
goto v_reusejp_5871_;
}
v_reusejp_5871_:
{
return v___x_5872_;
}
}
case 3:
{
lean_del_object(v___x_5864_);
v___y_5845_ = v___y_5833_;
v___y_5846_ = v___y_5834_;
v___y_5847_ = v___y_5835_;
v___y_5848_ = v___y_5836_;
goto v___jp_5844_;
}
default: 
{
lean_object* v___x_5874_; lean_object* v___x_5876_; 
lean_dec(v_a_5862_);
lean_dec(v_id_5830_);
v___x_5874_ = lean_box(v___x_5828_);
if (v_isShared_5865_ == 0)
{
lean_ctor_set(v___x_5864_, 0, v___x_5874_);
v___x_5876_ = v___x_5864_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v___x_5874_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
}
}
}
else
{
lean_object* v_a_5879_; lean_object* v___x_5881_; uint8_t v_isShared_5882_; uint8_t v_isSharedCheck_5886_; 
lean_dec(v_id_5830_);
v_a_5879_ = lean_ctor_get(v___x_5861_, 0);
v_isSharedCheck_5886_ = !lean_is_exclusive(v___x_5861_);
if (v_isSharedCheck_5886_ == 0)
{
v___x_5881_ = v___x_5861_;
v_isShared_5882_ = v_isSharedCheck_5886_;
goto v_resetjp_5880_;
}
else
{
lean_inc(v_a_5879_);
lean_dec(v___x_5861_);
v___x_5881_ = lean_box(0);
v_isShared_5882_ = v_isSharedCheck_5886_;
goto v_resetjp_5880_;
}
v_resetjp_5880_:
{
lean_object* v___x_5884_; 
if (v_isShared_5882_ == 0)
{
v___x_5884_ = v___x_5881_;
goto v_reusejp_5883_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_a_5879_);
v___x_5884_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5883_;
}
v_reusejp_5883_:
{
return v___x_5884_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_5829_);
v___y_5845_ = v___y_5833_;
v___y_5846_ = v___y_5834_;
v___y_5847_ = v___y_5835_;
v___y_5848_ = v___y_5836_;
goto v___jp_5844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___boxed(lean_object* v___x_5908_, lean_object* v___x_5909_, lean_object* v_mod_x3f_5910_, lean_object* v_id_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_){
_start:
{
uint8_t v___x_6882__boxed_5919_; uint8_t v___x_6883__boxed_5920_; lean_object* v_res_5921_; 
v___x_6882__boxed_5919_ = lean_unbox(v___x_5908_);
v___x_6883__boxed_5920_ = lean_unbox(v___x_5909_);
v_res_5921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0(v___x_6882__boxed_5919_, v___x_6883__boxed_5920_, v_mod_x3f_5910_, v_id_5911_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_);
lean_dec(v___y_5917_);
lean_dec_ref(v___y_5916_);
lean_dec(v___y_5915_);
lean_dec_ref(v___y_5914_);
lean_dec(v___y_5913_);
lean_dec_ref(v___y_5912_);
return v_res_5921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(lean_object* v___x_5922_, uint8_t v___x_5923_, lean_object* v_keepIdentParam_5924_, lean_object* v_x_5925_, lean_object* v_mod_x3f_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_){
_start:
{
lean_object* v___x_5934_; lean_object* v_id_5935_; lean_object* v___x_5936_; uint8_t v___x_5937_; 
v___x_5934_ = lean_unsigned_to_nat(1u);
v_id_5935_ = l_Lean_Syntax_getArg(v___x_5922_, v___x_5934_);
v___x_5936_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v_id_5935_);
v___x_5937_ = l_Lean_Syntax_isOfKind(v_id_5935_, v___x_5936_);
if (v___x_5937_ == 0)
{
lean_object* v___x_5938_; lean_object* v___x_5939_; 
lean_dec(v_id_5935_);
lean_dec(v_mod_x3f_5926_);
lean_dec_ref(v_keepIdentParam_5924_);
v___x_5938_ = lean_box(v___x_5923_);
v___x_5939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5939_, 0, v___x_5938_);
return v___x_5939_;
}
else
{
lean_object* v___x_5940_; 
lean_inc(v___y_5932_);
lean_inc_ref(v___y_5931_);
lean_inc(v___y_5930_);
lean_inc_ref(v___y_5929_);
lean_inc(v___y_5928_);
lean_inc_ref(v___y_5927_);
v___x_5940_ = lean_apply_9(v_keepIdentParam_5924_, v_mod_x3f_5926_, v_id_5935_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, lean_box(0));
return v___x_5940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2___boxed(lean_object* v___x_5941_, lean_object* v___x_5942_, lean_object* v_keepIdentParam_5943_, lean_object* v_x_5944_, lean_object* v_mod_x3f_5945_, lean_object* v___y_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_){
_start:
{
uint8_t v___x_7059__boxed_5953_; lean_object* v_res_5954_; 
v___x_7059__boxed_5953_ = lean_unbox(v___x_5942_);
v_res_5954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(v___x_5941_, v___x_7059__boxed_5953_, v_keepIdentParam_5943_, v_x_5944_, v_mod_x3f_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_);
lean_dec(v___y_5951_);
lean_dec_ref(v___y_5950_);
lean_dec(v___y_5949_);
lean_dec_ref(v___y_5948_);
lean_dec(v___y_5947_);
lean_dec_ref(v___y_5946_);
lean_dec(v___x_5941_);
return v_res_5954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(lean_object* v_as_5955_, size_t v_i_5956_, size_t v_stop_5957_, lean_object* v_b_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_){
_start:
{
lean_object* v_a_5967_; uint8_t v___x_5971_; 
v___x_5971_ = lean_usize_dec_eq(v_i_5956_, v_stop_5957_);
if (v___x_5971_ == 0)
{
lean_object* v___x_5972_; uint8_t v_a_5976_; lean_object* v___y_5978_; lean_object* v___x_5989_; uint8_t v___x_5990_; 
v___x_5972_ = lean_array_uget_borrowed(v_as_5955_, v_i_5956_);
v___x_5989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v___x_5972_);
v___x_5990_ = l_Lean_Syntax_isOfKind(v___x_5972_, v___x_5989_);
if (v___x_5990_ == 0)
{
goto v___jp_5973_;
}
else
{
lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v_keepIdentParam_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; uint8_t v___x_5997_; 
v___x_5991_ = lean_box(v___x_5971_);
v___x_5992_ = lean_box(v___x_5990_);
v_keepIdentParam_5993_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__0___boxed), 11, 2);
lean_closure_set(v_keepIdentParam_5993_, 0, v___x_5991_);
lean_closure_set(v_keepIdentParam_5993_, 1, v___x_5992_);
v___x_5994_ = lean_unsigned_to_nat(0u);
v___x_5995_ = l_Lean_Syntax_getArg(v___x_5972_, v___x_5994_);
v___x_5996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_5995_);
v___x_5997_ = l_Lean_Syntax_isOfKind(v___x_5995_, v___x_5996_);
if (v___x_5997_ == 0)
{
lean_object* v___x_5998_; uint8_t v___x_5999_; 
v___x_5998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_5995_);
v___x_5999_ = l_Lean_Syntax_isOfKind(v___x_5995_, v___x_5998_);
if (v___x_5999_ == 0)
{
lean_object* v___x_6000_; uint8_t v___x_6001_; 
lean_dec_ref(v_keepIdentParam_5993_);
v___x_6000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_5995_);
v___x_6001_ = l_Lean_Syntax_isOfKind(v___x_5995_, v___x_6000_);
if (v___x_6001_ == 0)
{
lean_object* v___x_6002_; uint8_t v___x_6003_; 
v___x_6002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_5995_);
v___x_6003_ = l_Lean_Syntax_isOfKind(v___x_5995_, v___x_6002_);
if (v___x_6003_ == 0)
{
lean_dec(v___x_5995_);
goto v___jp_5973_;
}
else
{
if (v___x_6001_ == 0)
{
lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; uint8_t v___x_6007_; 
v___x_6004_ = lean_unsigned_to_nat(1u);
v___x_6005_ = l_Lean_Syntax_getArg(v___x_5995_, v___x_6004_);
lean_dec(v___x_5995_);
v___x_6006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15));
v___x_6007_ = l_Lean_Syntax_isOfKind(v___x_6005_, v___x_6006_);
if (v___x_6007_ == 0)
{
goto v___jp_5973_;
}
else
{
v_a_5976_ = v___x_6001_;
goto v___jp_5975_;
}
}
else
{
lean_dec(v___x_5995_);
v_a_5976_ = v___x_6001_;
goto v___jp_5975_;
}
}
}
else
{
if (v___x_5999_ == 0)
{
lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; uint8_t v___x_6011_; 
v___x_6008_ = lean_unsigned_to_nat(1u);
v___x_6009_ = l_Lean_Syntax_getArg(v___x_5995_, v___x_6008_);
lean_dec(v___x_5995_);
v___x_6010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
v___x_6011_ = l_Lean_Syntax_isOfKind(v___x_6009_, v___x_6010_);
if (v___x_6011_ == 0)
{
goto v___jp_5973_;
}
else
{
v_a_5976_ = v___x_5999_;
goto v___jp_5975_;
}
}
else
{
lean_dec(v___x_5995_);
v_a_5976_ = v___x_5999_;
goto v___jp_5975_;
}
}
}
else
{
lean_object* v___x_6012_; lean_object* v___x_6013_; uint8_t v___x_6014_; 
v___x_6012_ = lean_unsigned_to_nat(1u);
v___x_6013_ = l_Lean_Syntax_getArg(v___x_5995_, v___x_6012_);
v___x_6014_ = l_Lean_Syntax_isNone(v___x_6013_);
if (v___x_6014_ == 0)
{
uint8_t v___x_6015_; 
lean_inc(v___x_6013_);
v___x_6015_ = l_Lean_Syntax_matchesNull(v___x_6013_, v___x_6012_);
if (v___x_6015_ == 0)
{
lean_dec(v___x_6013_);
lean_dec(v___x_5995_);
lean_dec_ref(v_keepIdentParam_5993_);
goto v___jp_5973_;
}
else
{
lean_object* v_mod_x3f_6016_; 
v_mod_x3f_6016_ = l_Lean_Syntax_getArg(v___x_6013_, v___x_5994_);
lean_dec(v___x_6013_);
if (v___x_6014_ == 0)
{
lean_object* v___x_6021_; uint8_t v___x_6022_; 
v___x_6021_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v_mod_x3f_6016_);
v___x_6022_ = l_Lean_Syntax_isOfKind(v_mod_x3f_6016_, v___x_6021_);
if (v___x_6022_ == 0)
{
lean_dec(v_mod_x3f_6016_);
lean_dec(v___x_5995_);
lean_dec_ref(v_keepIdentParam_5993_);
goto v___jp_5973_;
}
else
{
goto v___jp_6017_;
}
}
else
{
goto v___jp_6017_;
}
v___jp_6017_:
{
lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; 
v___x_6018_ = lean_box(0);
v___x_6019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6019_, 0, v_mod_x3f_6016_);
v___x_6020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(v___x_5995_, v___x_5997_, v___x_5990_, v_keepIdentParam_5993_, v___x_6018_, v___x_6019_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_);
lean_dec(v___x_5995_);
v___y_5978_ = v___x_6020_;
goto v___jp_5977_;
}
}
}
else
{
lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; 
lean_dec(v___x_6013_);
v___x_6023_ = lean_box(0);
v___x_6024_ = lean_box(0);
v___x_6025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__1(v___x_5995_, v___x_5997_, v___x_5990_, v_keepIdentParam_5993_, v___x_6023_, v___x_6024_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_);
lean_dec(v___x_5995_);
v___y_5978_ = v___x_6025_;
goto v___jp_5977_;
}
}
}
else
{
lean_object* v___x_6026_; uint8_t v___x_6027_; 
v___x_6026_ = l_Lean_Syntax_getArg(v___x_5995_, v___x_5994_);
v___x_6027_ = l_Lean_Syntax_isNone(v___x_6026_);
if (v___x_6027_ == 0)
{
lean_object* v___x_6028_; uint8_t v___x_6029_; 
v___x_6028_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_6026_);
v___x_6029_ = l_Lean_Syntax_matchesNull(v___x_6026_, v___x_6028_);
if (v___x_6029_ == 0)
{
lean_dec(v___x_6026_);
lean_dec(v___x_5995_);
lean_dec_ref(v_keepIdentParam_5993_);
goto v___jp_5973_;
}
else
{
lean_object* v_mod_x3f_6030_; 
v_mod_x3f_6030_ = l_Lean_Syntax_getArg(v___x_6026_, v___x_5994_);
lean_dec(v___x_6026_);
if (v___x_6027_ == 0)
{
lean_object* v___x_6035_; uint8_t v___x_6036_; 
v___x_6035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v_mod_x3f_6030_);
v___x_6036_ = l_Lean_Syntax_isOfKind(v_mod_x3f_6030_, v___x_6035_);
if (v___x_6036_ == 0)
{
lean_dec(v_mod_x3f_6030_);
lean_dec(v___x_5995_);
lean_dec_ref(v_keepIdentParam_5993_);
goto v___jp_5973_;
}
else
{
goto v___jp_6031_;
}
}
else
{
goto v___jp_6031_;
}
v___jp_6031_:
{
lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; 
v___x_6032_ = lean_box(0);
v___x_6033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6033_, 0, v_mod_x3f_6030_);
v___x_6034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(v___x_5995_, v___x_5990_, v_keepIdentParam_5993_, v___x_6032_, v___x_6033_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_);
lean_dec(v___x_5995_);
v___y_5978_ = v___x_6034_;
goto v___jp_5977_;
}
}
}
else
{
lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; 
lean_dec(v___x_6026_);
v___x_6037_ = lean_box(0);
v___x_6038_ = lean_box(0);
v___x_6039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___lam__2(v___x_5995_, v___x_5990_, v_keepIdentParam_5993_, v___x_6037_, v___x_6038_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_);
lean_dec(v___x_5995_);
v___y_5978_ = v___x_6039_;
goto v___jp_5977_;
}
}
}
v___jp_5973_:
{
lean_object* v___x_5974_; 
lean_inc(v___x_5972_);
v___x_5974_ = lean_array_push(v_b_5958_, v___x_5972_);
v_a_5967_ = v___x_5974_;
goto v___jp_5966_;
}
v___jp_5975_:
{
if (v_a_5976_ == 0)
{
v_a_5967_ = v_b_5958_;
goto v___jp_5966_;
}
else
{
goto v___jp_5973_;
}
}
v___jp_5977_:
{
if (lean_obj_tag(v___y_5978_) == 0)
{
lean_object* v_a_5979_; uint8_t v___x_5980_; 
v_a_5979_ = lean_ctor_get(v___y_5978_, 0);
lean_inc(v_a_5979_);
lean_dec_ref_known(v___y_5978_, 1);
v___x_5980_ = lean_unbox(v_a_5979_);
lean_dec(v_a_5979_);
v_a_5976_ = v___x_5980_;
goto v___jp_5975_;
}
else
{
lean_object* v_a_5981_; lean_object* v___x_5983_; uint8_t v_isShared_5984_; uint8_t v_isSharedCheck_5988_; 
lean_dec_ref(v_b_5958_);
v_a_5981_ = lean_ctor_get(v___y_5978_, 0);
v_isSharedCheck_5988_ = !lean_is_exclusive(v___y_5978_);
if (v_isSharedCheck_5988_ == 0)
{
v___x_5983_ = v___y_5978_;
v_isShared_5984_ = v_isSharedCheck_5988_;
goto v_resetjp_5982_;
}
else
{
lean_inc(v_a_5981_);
lean_dec(v___y_5978_);
v___x_5983_ = lean_box(0);
v_isShared_5984_ = v_isSharedCheck_5988_;
goto v_resetjp_5982_;
}
v_resetjp_5982_:
{
lean_object* v___x_5986_; 
if (v_isShared_5984_ == 0)
{
v___x_5986_ = v___x_5983_;
goto v_reusejp_5985_;
}
else
{
lean_object* v_reuseFailAlloc_5987_; 
v_reuseFailAlloc_5987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5987_, 0, v_a_5981_);
v___x_5986_ = v_reuseFailAlloc_5987_;
goto v_reusejp_5985_;
}
v_reusejp_5985_:
{
return v___x_5986_;
}
}
}
}
}
else
{
lean_object* v___x_6040_; 
v___x_6040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6040_, 0, v_b_5958_);
return v___x_6040_;
}
v___jp_5966_:
{
size_t v___x_5968_; size_t v___x_5969_; 
v___x_5968_ = ((size_t)1ULL);
v___x_5969_ = lean_usize_add(v_i_5956_, v___x_5968_);
v_i_5956_ = v___x_5969_;
v_b_5958_ = v_a_5967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0___boxed(lean_object* v_as_6041_, lean_object* v_i_6042_, lean_object* v_stop_6043_, lean_object* v_b_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_){
_start:
{
size_t v_i_boxed_6052_; size_t v_stop_boxed_6053_; lean_object* v_res_6054_; 
v_i_boxed_6052_ = lean_unbox_usize(v_i_6042_);
lean_dec(v_i_6042_);
v_stop_boxed_6053_ = lean_unbox_usize(v_stop_6043_);
lean_dec(v_stop_6043_);
v_res_6054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(v_as_6041_, v_i_boxed_6052_, v_stop_boxed_6053_, v_b_6044_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_);
lean_dec(v___y_6050_);
lean_dec_ref(v___y_6049_);
lean_dec(v___y_6048_);
lean_dec_ref(v___y_6047_);
lean_dec(v___y_6046_);
lean_dec_ref(v___y_6045_);
lean_dec_ref(v_as_6041_);
return v_res_6054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_getPreservedParams(lean_object* v_params_6057_, lean_object* v_a_6058_, lean_object* v_a_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_){
_start:
{
lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; uint8_t v___x_6068_; 
v___x_6065_ = lean_unsigned_to_nat(0u);
v___x_6066_ = lean_array_get_size(v_params_6057_);
v___x_6067_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_getPreservedParams___closed__0));
v___x_6068_ = lean_nat_dec_lt(v___x_6065_, v___x_6066_);
if (v___x_6068_ == 0)
{
lean_object* v___x_6069_; 
v___x_6069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6067_);
return v___x_6069_;
}
else
{
uint8_t v___x_6070_; 
v___x_6070_ = lean_nat_dec_le(v___x_6066_, v___x_6066_);
if (v___x_6070_ == 0)
{
if (v___x_6068_ == 0)
{
lean_object* v___x_6071_; 
v___x_6071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6067_);
return v___x_6071_;
}
else
{
size_t v___x_6072_; size_t v___x_6073_; lean_object* v___x_6074_; 
v___x_6072_ = ((size_t)0ULL);
v___x_6073_ = lean_usize_of_nat(v___x_6066_);
v___x_6074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(v_params_6057_, v___x_6072_, v___x_6073_, v___x_6067_, v_a_6058_, v_a_6059_, v_a_6060_, v_a_6061_, v_a_6062_, v_a_6063_);
return v___x_6074_;
}
}
else
{
size_t v___x_6075_; size_t v___x_6076_; lean_object* v___x_6077_; 
v___x_6075_ = ((size_t)0ULL);
v___x_6076_ = lean_usize_of_nat(v___x_6066_);
v___x_6077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Grind_getPreservedParams_spec__0(v_params_6057_, v___x_6075_, v___x_6076_, v___x_6067_, v_a_6058_, v_a_6059_, v_a_6060_, v_a_6061_, v_a_6062_, v_a_6063_);
return v___x_6077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_getPreservedParams___boxed(lean_object* v_params_6078_, lean_object* v_a_6079_, lean_object* v_a_6080_, lean_object* v_a_6081_, lean_object* v_a_6082_, lean_object* v_a_6083_, lean_object* v_a_6084_, lean_object* v_a_6085_){
_start:
{
lean_object* v_res_6086_; 
v_res_6086_ = l_Lean_Elab_Tactic_Grind_getPreservedParams(v_params_6078_, v_a_6079_, v_a_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_);
lean_dec(v_a_6084_);
lean_dec_ref(v_a_6083_);
lean_dec(v_a_6082_);
lean_dec_ref(v_a_6081_);
lean_dec(v_a_6080_);
lean_dec_ref(v_a_6079_);
lean_dec_ref(v_params_6078_);
return v_res_6086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_6089_, lean_object* v_newThms_6090_, lean_object* v_gmt_6091_, lean_object* v_numInstances_6092_, lean_object* v_numDelayedInstances_6093_, lean_object* v_num_6094_, lean_object* v_preInstances_6095_, lean_object* v_nextThmIdx_6096_, lean_object* v_matchEqNames_6097_, lean_object* v_delayedThmInsts_6098_, lean_object* v_nextDeclIdx_6099_, lean_object* v_enodeMap_6100_, lean_object* v_exprs_6101_, lean_object* v_parents_6102_, lean_object* v_congrTable_6103_, lean_object* v_appMap_6104_, lean_object* v_indicesFound_6105_, lean_object* v_toProcess_6106_, lean_object* v_internalizing_6107_, uint8_t v_inconsistent_6108_, lean_object* v_nextIdx_6109_, lean_object* v_newRawFacts_6110_, lean_object* v_facts_6111_, lean_object* v_extThms_6112_, lean_object* v_inj_6113_, lean_object* v_split_6114_, lean_object* v_clean_6115_, lean_object* v_sstates_6116_, lean_object* v_mvarId_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_){
_start:
{
lean_object* v___x_6128_; 
v___x_6128_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_6089_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_);
if (lean_obj_tag(v___x_6128_) == 0)
{
lean_object* v_a_6129_; lean_object* v___x_6130_; 
v_a_6129_ = lean_ctor_get(v___x_6128_, 0);
lean_inc(v_a_6129_);
lean_dec_ref_known(v___x_6128_, 1);
v___x_6130_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_6090_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_);
if (lean_obj_tag(v___x_6130_) == 0)
{
lean_object* v_a_6131_; lean_object* v___x_6133_; uint8_t v_isShared_6134_; uint8_t v_isSharedCheck_6142_; 
v_a_6131_ = lean_ctor_get(v___x_6130_, 0);
v_isSharedCheck_6142_ = !lean_is_exclusive(v___x_6130_);
if (v_isSharedCheck_6142_ == 0)
{
v___x_6133_ = v___x_6130_;
v_isShared_6134_ = v_isSharedCheck_6142_;
goto v_resetjp_6132_;
}
else
{
lean_inc(v_a_6131_);
lean_dec(v___x_6130_);
v___x_6133_ = lean_box(0);
v_isShared_6134_ = v_isSharedCheck_6142_;
goto v_resetjp_6132_;
}
v_resetjp_6132_:
{
lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6140_; 
v___x_6135_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_6136_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6136_, 0, v___x_6135_);
lean_ctor_set(v___x_6136_, 1, v_gmt_6091_);
lean_ctor_set(v___x_6136_, 2, v_a_6129_);
lean_ctor_set(v___x_6136_, 3, v_a_6131_);
lean_ctor_set(v___x_6136_, 4, v_numInstances_6092_);
lean_ctor_set(v___x_6136_, 5, v_numDelayedInstances_6093_);
lean_ctor_set(v___x_6136_, 6, v_num_6094_);
lean_ctor_set(v___x_6136_, 7, v_preInstances_6095_);
lean_ctor_set(v___x_6136_, 8, v_nextThmIdx_6096_);
lean_ctor_set(v___x_6136_, 9, v_matchEqNames_6097_);
lean_ctor_set(v___x_6136_, 10, v_delayedThmInsts_6098_);
v___x_6137_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v___x_6137_, 0, v_nextDeclIdx_6099_);
lean_ctor_set(v___x_6137_, 1, v_enodeMap_6100_);
lean_ctor_set(v___x_6137_, 2, v_exprs_6101_);
lean_ctor_set(v___x_6137_, 3, v_parents_6102_);
lean_ctor_set(v___x_6137_, 4, v_congrTable_6103_);
lean_ctor_set(v___x_6137_, 5, v_appMap_6104_);
lean_ctor_set(v___x_6137_, 6, v_indicesFound_6105_);
lean_ctor_set(v___x_6137_, 7, v_toProcess_6106_);
lean_ctor_set(v___x_6137_, 8, v_internalizing_6107_);
lean_ctor_set(v___x_6137_, 9, v_nextIdx_6109_);
lean_ctor_set(v___x_6137_, 10, v_newRawFacts_6110_);
lean_ctor_set(v___x_6137_, 11, v_facts_6111_);
lean_ctor_set(v___x_6137_, 12, v_extThms_6112_);
lean_ctor_set(v___x_6137_, 13, v___x_6136_);
lean_ctor_set(v___x_6137_, 14, v_inj_6113_);
lean_ctor_set(v___x_6137_, 15, v_split_6114_);
lean_ctor_set(v___x_6137_, 16, v_clean_6115_);
lean_ctor_set(v___x_6137_, 17, v_sstates_6116_);
lean_ctor_set_uint8(v___x_6137_, sizeof(void*)*18, v_inconsistent_6108_);
v___x_6138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6138_, 0, v___x_6137_);
lean_ctor_set(v___x_6138_, 1, v_mvarId_6117_);
if (v_isShared_6134_ == 0)
{
lean_ctor_set(v___x_6133_, 0, v___x_6138_);
v___x_6140_ = v___x_6133_;
goto v_reusejp_6139_;
}
else
{
lean_object* v_reuseFailAlloc_6141_; 
v_reuseFailAlloc_6141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6141_, 0, v___x_6138_);
v___x_6140_ = v_reuseFailAlloc_6141_;
goto v_reusejp_6139_;
}
v_reusejp_6139_:
{
return v___x_6140_;
}
}
}
else
{
lean_object* v_a_6143_; lean_object* v___x_6145_; uint8_t v_isShared_6146_; uint8_t v_isSharedCheck_6150_; 
lean_dec(v_a_6129_);
lean_dec(v_mvarId_6117_);
lean_dec_ref(v_sstates_6116_);
lean_dec_ref(v_clean_6115_);
lean_dec_ref(v_split_6114_);
lean_dec_ref(v_inj_6113_);
lean_dec_ref(v_extThms_6112_);
lean_dec_ref(v_facts_6111_);
lean_dec_ref(v_newRawFacts_6110_);
lean_dec(v_nextIdx_6109_);
lean_dec_ref(v_internalizing_6107_);
lean_dec_ref(v_toProcess_6106_);
lean_dec_ref(v_indicesFound_6105_);
lean_dec_ref(v_appMap_6104_);
lean_dec_ref(v_congrTable_6103_);
lean_dec_ref(v_parents_6102_);
lean_dec_ref(v_exprs_6101_);
lean_dec_ref(v_enodeMap_6100_);
lean_dec(v_nextDeclIdx_6099_);
lean_dec_ref(v_delayedThmInsts_6098_);
lean_dec_ref(v_matchEqNames_6097_);
lean_dec(v_nextThmIdx_6096_);
lean_dec_ref(v_preInstances_6095_);
lean_dec(v_num_6094_);
lean_dec(v_numDelayedInstances_6093_);
lean_dec(v_numInstances_6092_);
lean_dec(v_gmt_6091_);
v_a_6143_ = lean_ctor_get(v___x_6130_, 0);
v_isSharedCheck_6150_ = !lean_is_exclusive(v___x_6130_);
if (v_isSharedCheck_6150_ == 0)
{
v___x_6145_ = v___x_6130_;
v_isShared_6146_ = v_isSharedCheck_6150_;
goto v_resetjp_6144_;
}
else
{
lean_inc(v_a_6143_);
lean_dec(v___x_6130_);
v___x_6145_ = lean_box(0);
v_isShared_6146_ = v_isSharedCheck_6150_;
goto v_resetjp_6144_;
}
v_resetjp_6144_:
{
lean_object* v___x_6148_; 
if (v_isShared_6146_ == 0)
{
v___x_6148_ = v___x_6145_;
goto v_reusejp_6147_;
}
else
{
lean_object* v_reuseFailAlloc_6149_; 
v_reuseFailAlloc_6149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6149_, 0, v_a_6143_);
v___x_6148_ = v_reuseFailAlloc_6149_;
goto v_reusejp_6147_;
}
v_reusejp_6147_:
{
return v___x_6148_;
}
}
}
}
else
{
lean_object* v_a_6151_; lean_object* v___x_6153_; uint8_t v_isShared_6154_; uint8_t v_isSharedCheck_6158_; 
lean_dec(v_mvarId_6117_);
lean_dec_ref(v_sstates_6116_);
lean_dec_ref(v_clean_6115_);
lean_dec_ref(v_split_6114_);
lean_dec_ref(v_inj_6113_);
lean_dec_ref(v_extThms_6112_);
lean_dec_ref(v_facts_6111_);
lean_dec_ref(v_newRawFacts_6110_);
lean_dec(v_nextIdx_6109_);
lean_dec_ref(v_internalizing_6107_);
lean_dec_ref(v_toProcess_6106_);
lean_dec_ref(v_indicesFound_6105_);
lean_dec_ref(v_appMap_6104_);
lean_dec_ref(v_congrTable_6103_);
lean_dec_ref(v_parents_6102_);
lean_dec_ref(v_exprs_6101_);
lean_dec_ref(v_enodeMap_6100_);
lean_dec(v_nextDeclIdx_6099_);
lean_dec_ref(v_delayedThmInsts_6098_);
lean_dec_ref(v_matchEqNames_6097_);
lean_dec(v_nextThmIdx_6096_);
lean_dec_ref(v_preInstances_6095_);
lean_dec(v_num_6094_);
lean_dec(v_numDelayedInstances_6093_);
lean_dec(v_numInstances_6092_);
lean_dec(v_gmt_6091_);
v_a_6151_ = lean_ctor_get(v___x_6128_, 0);
v_isSharedCheck_6158_ = !lean_is_exclusive(v___x_6128_);
if (v_isSharedCheck_6158_ == 0)
{
v___x_6153_ = v___x_6128_;
v_isShared_6154_ = v_isSharedCheck_6158_;
goto v_resetjp_6152_;
}
else
{
lean_inc(v_a_6151_);
lean_dec(v___x_6128_);
v___x_6153_ = lean_box(0);
v_isShared_6154_ = v_isSharedCheck_6158_;
goto v_resetjp_6152_;
}
v_resetjp_6152_:
{
lean_object* v___x_6156_; 
if (v_isShared_6154_ == 0)
{
v___x_6156_ = v___x_6153_;
goto v_reusejp_6155_;
}
else
{
lean_object* v_reuseFailAlloc_6157_; 
v_reuseFailAlloc_6157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6157_, 0, v_a_6151_);
v___x_6156_ = v_reuseFailAlloc_6157_;
goto v_reusejp_6155_;
}
v_reusejp_6155_:
{
return v___x_6156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_6159_ = _args[0];
lean_object* v_newThms_6160_ = _args[1];
lean_object* v_gmt_6161_ = _args[2];
lean_object* v_numInstances_6162_ = _args[3];
lean_object* v_numDelayedInstances_6163_ = _args[4];
lean_object* v_num_6164_ = _args[5];
lean_object* v_preInstances_6165_ = _args[6];
lean_object* v_nextThmIdx_6166_ = _args[7];
lean_object* v_matchEqNames_6167_ = _args[8];
lean_object* v_delayedThmInsts_6168_ = _args[9];
lean_object* v_nextDeclIdx_6169_ = _args[10];
lean_object* v_enodeMap_6170_ = _args[11];
lean_object* v_exprs_6171_ = _args[12];
lean_object* v_parents_6172_ = _args[13];
lean_object* v_congrTable_6173_ = _args[14];
lean_object* v_appMap_6174_ = _args[15];
lean_object* v_indicesFound_6175_ = _args[16];
lean_object* v_toProcess_6176_ = _args[17];
lean_object* v_internalizing_6177_ = _args[18];
lean_object* v_inconsistent_6178_ = _args[19];
lean_object* v_nextIdx_6179_ = _args[20];
lean_object* v_newRawFacts_6180_ = _args[21];
lean_object* v_facts_6181_ = _args[22];
lean_object* v_extThms_6182_ = _args[23];
lean_object* v_inj_6183_ = _args[24];
lean_object* v_split_6184_ = _args[25];
lean_object* v_clean_6185_ = _args[26];
lean_object* v_sstates_6186_ = _args[27];
lean_object* v_mvarId_6187_ = _args[28];
lean_object* v___y_6188_ = _args[29];
lean_object* v___y_6189_ = _args[30];
lean_object* v___y_6190_ = _args[31];
lean_object* v___y_6191_ = _args[32];
lean_object* v___y_6192_ = _args[33];
lean_object* v___y_6193_ = _args[34];
lean_object* v___y_6194_ = _args[35];
lean_object* v___y_6195_ = _args[36];
lean_object* v___y_6196_ = _args[37];
lean_object* v___y_6197_ = _args[38];
_start:
{
uint8_t v_inconsistent_boxed_6198_; lean_object* v_res_6199_; 
v_inconsistent_boxed_6198_ = lean_unbox(v_inconsistent_6178_);
v_res_6199_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_6159_, v_newThms_6160_, v_gmt_6161_, v_numInstances_6162_, v_numDelayedInstances_6163_, v_num_6164_, v_preInstances_6165_, v_nextThmIdx_6166_, v_matchEqNames_6167_, v_delayedThmInsts_6168_, v_nextDeclIdx_6169_, v_enodeMap_6170_, v_exprs_6171_, v_parents_6172_, v_congrTable_6173_, v_appMap_6174_, v_indicesFound_6175_, v_toProcess_6176_, v_internalizing_6177_, v_inconsistent_boxed_6198_, v_nextIdx_6179_, v_newRawFacts_6180_, v_facts_6181_, v_extThms_6182_, v_inj_6183_, v_split_6184_, v_clean_6185_, v_sstates_6186_, v_mvarId_6187_, v___y_6188_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_, v___y_6196_);
lean_dec(v___y_6196_);
lean_dec_ref(v___y_6195_);
lean_dec(v___y_6194_);
lean_dec_ref(v___y_6193_);
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
lean_dec(v___y_6190_);
lean_dec_ref(v___y_6189_);
lean_dec(v___y_6188_);
lean_dec_ref(v_newThms_6160_);
lean_dec_ref(v_thms_6159_);
return v_res_6199_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_6200_; 
v___x_6200_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_6200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_6201_, size_t v_i_6202_, lean_object* v_bs_6203_){
_start:
{
uint8_t v___x_6204_; 
v___x_6204_ = lean_usize_dec_lt(v_i_6202_, v_sz_6201_);
if (v___x_6204_ == 0)
{
return v_bs_6203_;
}
else
{
lean_object* v_v_6205_; lean_object* v_casesTypes_6206_; lean_object* v_extThms_6207_; lean_object* v_funCC_6208_; lean_object* v_inj_6209_; lean_object* v___x_6211_; uint8_t v_isShared_6212_; uint8_t v_isSharedCheck_6223_; 
v_v_6205_ = lean_array_uget(v_bs_6203_, v_i_6202_);
v_casesTypes_6206_ = lean_ctor_get(v_v_6205_, 0);
v_extThms_6207_ = lean_ctor_get(v_v_6205_, 1);
v_funCC_6208_ = lean_ctor_get(v_v_6205_, 2);
v_inj_6209_ = lean_ctor_get(v_v_6205_, 4);
v_isSharedCheck_6223_ = !lean_is_exclusive(v_v_6205_);
if (v_isSharedCheck_6223_ == 0)
{
lean_object* v_unused_6224_; 
v_unused_6224_ = lean_ctor_get(v_v_6205_, 3);
lean_dec(v_unused_6224_);
v___x_6211_ = v_v_6205_;
v_isShared_6212_ = v_isSharedCheck_6223_;
goto v_resetjp_6210_;
}
else
{
lean_inc(v_inj_6209_);
lean_inc(v_funCC_6208_);
lean_inc(v_extThms_6207_);
lean_inc(v_casesTypes_6206_);
lean_dec(v_v_6205_);
v___x_6211_ = lean_box(0);
v_isShared_6212_ = v_isSharedCheck_6223_;
goto v_resetjp_6210_;
}
v_resetjp_6210_:
{
lean_object* v___x_6213_; lean_object* v_bs_x27_6214_; lean_object* v___x_6215_; lean_object* v___x_6217_; 
v___x_6213_ = lean_unsigned_to_nat(0u);
v_bs_x27_6214_ = lean_array_uset(v_bs_6203_, v_i_6202_, v___x_6213_);
v___x_6215_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_6212_ == 0)
{
lean_ctor_set(v___x_6211_, 3, v___x_6215_);
v___x_6217_ = v___x_6211_;
goto v_reusejp_6216_;
}
else
{
lean_object* v_reuseFailAlloc_6222_; 
v_reuseFailAlloc_6222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6222_, 0, v_casesTypes_6206_);
lean_ctor_set(v_reuseFailAlloc_6222_, 1, v_extThms_6207_);
lean_ctor_set(v_reuseFailAlloc_6222_, 2, v_funCC_6208_);
lean_ctor_set(v_reuseFailAlloc_6222_, 3, v___x_6215_);
lean_ctor_set(v_reuseFailAlloc_6222_, 4, v_inj_6209_);
v___x_6217_ = v_reuseFailAlloc_6222_;
goto v_reusejp_6216_;
}
v_reusejp_6216_:
{
size_t v___x_6218_; size_t v___x_6219_; lean_object* v___x_6220_; 
v___x_6218_ = ((size_t)1ULL);
v___x_6219_ = lean_usize_add(v_i_6202_, v___x_6218_);
v___x_6220_ = lean_array_uset(v_bs_x27_6214_, v_i_6202_, v___x_6217_);
v_i_6202_ = v___x_6219_;
v_bs_6203_ = v___x_6220_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_6225_, lean_object* v_i_6226_, lean_object* v_bs_6227_){
_start:
{
size_t v_sz_boxed_6228_; size_t v_i_boxed_6229_; lean_object* v_res_6230_; 
v_sz_boxed_6228_ = lean_unbox_usize(v_sz_6225_);
lean_dec(v_sz_6225_);
v_i_boxed_6229_ = lean_unbox_usize(v_i_6226_);
lean_dec(v_i_6226_);
v_res_6230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_6228_, v_i_boxed_6229_, v_bs_6227_);
return v_res_6230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_6231_, lean_object* v_ps_6232_, uint8_t v_only_6233_, lean_object* v_k_6234_, lean_object* v_a_6235_, lean_object* v_a_6236_, lean_object* v_a_6237_, lean_object* v_a_6238_, lean_object* v_a_6239_, lean_object* v_a_6240_, lean_object* v_a_6241_, lean_object* v_a_6242_){
_start:
{
lean_object* v___y_6245_; lean_object* v___y_6246_; lean_object* v___y_6247_; lean_object* v___y_6248_; lean_object* v___y_6249_; lean_object* v___y_6250_; lean_object* v___y_6251_; lean_object* v___y_6252_; lean_object* v___y_6253_; uint8_t v___y_6266_; uint8_t v___y_6267_; lean_object* v_params_6268_; lean_object* v___y_6269_; lean_object* v___y_6270_; lean_object* v___y_6271_; lean_object* v___y_6272_; lean_object* v___y_6273_; lean_object* v___y_6274_; lean_object* v___y_6275_; lean_object* v___y_6276_; uint8_t v___y_6380_; 
if (v_only_6233_ == 0)
{
lean_object* v___x_6402_; lean_object* v___x_6403_; uint8_t v___x_6404_; 
v___x_6402_ = lean_array_get_size(v_ps_6232_);
v___x_6403_ = lean_unsigned_to_nat(0u);
v___x_6404_ = lean_nat_dec_eq(v___x_6402_, v___x_6403_);
if (v___x_6404_ == 0)
{
v___y_6380_ = v___x_6404_;
goto v___jp_6379_;
}
else
{
lean_object* v___x_6405_; 
lean_dec_ref(v_params_6231_);
lean_inc(v_a_6242_);
lean_inc_ref(v_a_6241_);
lean_inc(v_a_6240_);
lean_inc_ref(v_a_6239_);
lean_inc(v_a_6238_);
lean_inc_ref(v_a_6237_);
lean_inc(v_a_6236_);
lean_inc_ref(v_a_6235_);
v___x_6405_ = lean_apply_9(v_k_6234_, v_a_6235_, v_a_6236_, v_a_6237_, v_a_6238_, v_a_6239_, v_a_6240_, v_a_6241_, v_a_6242_, lean_box(0));
return v___x_6405_;
}
}
else
{
uint8_t v___x_6406_; 
v___x_6406_ = 0;
v___y_6380_ = v___x_6406_;
goto v___jp_6379_;
}
v___jp_6244_:
{
lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6254_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_6254_, 0, v___y_6245_);
v___x_6255_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_6254_, v___y_6246_, v___y_6247_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_);
if (lean_obj_tag(v___x_6255_) == 0)
{
lean_object* v___x_6256_; 
lean_dec_ref_known(v___x_6255_, 1);
lean_inc(v___y_6253_);
lean_inc_ref(v___y_6252_);
lean_inc(v___y_6251_);
lean_inc_ref(v___y_6250_);
lean_inc(v___y_6249_);
lean_inc_ref(v___y_6248_);
lean_inc(v___y_6247_);
v___x_6256_ = lean_apply_9(v_k_6234_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_, lean_box(0));
return v___x_6256_;
}
else
{
lean_object* v_a_6257_; lean_object* v___x_6259_; uint8_t v_isShared_6260_; uint8_t v_isSharedCheck_6264_; 
lean_dec_ref(v___y_6246_);
lean_dec_ref(v_k_6234_);
v_a_6257_ = lean_ctor_get(v___x_6255_, 0);
v_isSharedCheck_6264_ = !lean_is_exclusive(v___x_6255_);
if (v_isSharedCheck_6264_ == 0)
{
v___x_6259_ = v___x_6255_;
v_isShared_6260_ = v_isSharedCheck_6264_;
goto v_resetjp_6258_;
}
else
{
lean_inc(v_a_6257_);
lean_dec(v___x_6255_);
v___x_6259_ = lean_box(0);
v_isShared_6260_ = v_isSharedCheck_6264_;
goto v_resetjp_6258_;
}
v_resetjp_6258_:
{
lean_object* v___x_6262_; 
if (v_isShared_6260_ == 0)
{
v___x_6262_ = v___x_6259_;
goto v_reusejp_6261_;
}
else
{
lean_object* v_reuseFailAlloc_6263_; 
v_reuseFailAlloc_6263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6263_, 0, v_a_6257_);
v___x_6262_ = v_reuseFailAlloc_6263_;
goto v_reusejp_6261_;
}
v_reusejp_6261_:
{
return v___x_6262_;
}
}
}
}
v___jp_6265_:
{
lean_object* v___x_6277_; 
v___x_6277_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_6268_, v_ps_6232_, v_only_6233_, v___y_6267_, v___y_6266_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_);
if (lean_obj_tag(v___x_6277_) == 0)
{
lean_object* v_a_6278_; lean_object* v_ctx_6279_; lean_object* v_anchorRefs_x3f_6280_; lean_object* v_toContext_6281_; lean_object* v_sctx_6282_; lean_object* v_methods_6283_; uint8_t v_sym_6284_; lean_object* v_simp_6285_; lean_object* v_simpMethods_6286_; lean_object* v_symSimpMethods_6287_; lean_object* v_symDSimpMethods_6288_; lean_object* v_config_6289_; uint8_t v_cheapCases_6290_; uint8_t v_reportMVarIssue_6291_; lean_object* v_splitSource_6292_; lean_object* v_ematchDiagSource_6293_; lean_object* v_symPrios_6294_; lean_object* v_extensions_6295_; uint8_t v_debug_6296_; uint8_t v_ematchDiag_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; 
v_a_6278_ = lean_ctor_get(v___x_6277_, 0);
lean_inc_n(v_a_6278_, 2);
lean_dec_ref_known(v___x_6277_, 1);
v_ctx_6279_ = lean_ctor_get(v___y_6269_, 1);
v_anchorRefs_x3f_6280_ = lean_ctor_get(v_a_6278_, 8);
v_toContext_6281_ = lean_ctor_get(v___y_6269_, 0);
v_sctx_6282_ = lean_ctor_get(v___y_6269_, 2);
v_methods_6283_ = lean_ctor_get(v___y_6269_, 3);
v_sym_6284_ = lean_ctor_get_uint8(v___y_6269_, sizeof(void*)*5);
v_simp_6285_ = lean_ctor_get(v_ctx_6279_, 0);
v_simpMethods_6286_ = lean_ctor_get(v_ctx_6279_, 1);
v_symSimpMethods_6287_ = lean_ctor_get(v_ctx_6279_, 2);
v_symDSimpMethods_6288_ = lean_ctor_get(v_ctx_6279_, 3);
v_config_6289_ = lean_ctor_get(v_ctx_6279_, 4);
v_cheapCases_6290_ = lean_ctor_get_uint8(v_ctx_6279_, sizeof(void*)*10);
v_reportMVarIssue_6291_ = lean_ctor_get_uint8(v_ctx_6279_, sizeof(void*)*10 + 1);
v_splitSource_6292_ = lean_ctor_get(v_ctx_6279_, 6);
v_ematchDiagSource_6293_ = lean_ctor_get(v_ctx_6279_, 7);
v_symPrios_6294_ = lean_ctor_get(v_ctx_6279_, 8);
v_extensions_6295_ = lean_ctor_get(v_ctx_6279_, 9);
v_debug_6296_ = lean_ctor_get_uint8(v_ctx_6279_, sizeof(void*)*10 + 2);
v_ematchDiag_6297_ = lean_ctor_get_uint8(v_ctx_6279_, sizeof(void*)*10 + 3);
lean_inc_ref(v_extensions_6295_);
lean_inc_ref(v_symPrios_6294_);
lean_inc(v_ematchDiagSource_6293_);
lean_inc(v_splitSource_6292_);
lean_inc(v_anchorRefs_x3f_6280_);
lean_inc_ref(v_config_6289_);
lean_inc_ref(v_symDSimpMethods_6288_);
lean_inc_ref(v_symSimpMethods_6287_);
lean_inc_ref(v_simpMethods_6286_);
lean_inc_ref(v_simp_6285_);
v___x_6298_ = lean_alloc_ctor(0, 10, 4);
lean_ctor_set(v___x_6298_, 0, v_simp_6285_);
lean_ctor_set(v___x_6298_, 1, v_simpMethods_6286_);
lean_ctor_set(v___x_6298_, 2, v_symSimpMethods_6287_);
lean_ctor_set(v___x_6298_, 3, v_symDSimpMethods_6288_);
lean_ctor_set(v___x_6298_, 4, v_config_6289_);
lean_ctor_set(v___x_6298_, 5, v_anchorRefs_x3f_6280_);
lean_ctor_set(v___x_6298_, 6, v_splitSource_6292_);
lean_ctor_set(v___x_6298_, 7, v_ematchDiagSource_6293_);
lean_ctor_set(v___x_6298_, 8, v_symPrios_6294_);
lean_ctor_set(v___x_6298_, 9, v_extensions_6295_);
lean_ctor_set_uint8(v___x_6298_, sizeof(void*)*10, v_cheapCases_6290_);
lean_ctor_set_uint8(v___x_6298_, sizeof(void*)*10 + 1, v_reportMVarIssue_6291_);
lean_ctor_set_uint8(v___x_6298_, sizeof(void*)*10 + 2, v_debug_6296_);
lean_ctor_set_uint8(v___x_6298_, sizeof(void*)*10 + 3, v_ematchDiag_6297_);
lean_inc_ref(v_methods_6283_);
lean_inc_ref(v_sctx_6282_);
lean_inc_ref(v_toContext_6281_);
v___x_6299_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_6299_, 0, v_toContext_6281_);
lean_ctor_set(v___x_6299_, 1, v___x_6298_);
lean_ctor_set(v___x_6299_, 2, v_sctx_6282_);
lean_ctor_set(v___x_6299_, 3, v_methods_6283_);
lean_ctor_set(v___x_6299_, 4, v_a_6278_);
lean_ctor_set_uint8(v___x_6299_, sizeof(void*)*5, v_sym_6284_);
if (v_only_6233_ == 0)
{
v___y_6245_ = v_a_6278_;
v___y_6246_ = v___x_6299_;
v___y_6247_ = v___y_6270_;
v___y_6248_ = v___y_6271_;
v___y_6249_ = v___y_6272_;
v___y_6250_ = v___y_6273_;
v___y_6251_ = v___y_6274_;
v___y_6252_ = v___y_6275_;
v___y_6253_ = v___y_6276_;
goto v___jp_6244_;
}
else
{
lean_object* v___x_6300_; 
v___x_6300_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_6270_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_);
if (lean_obj_tag(v___x_6300_) == 0)
{
lean_object* v_a_6301_; lean_object* v_toGoalState_6302_; lean_object* v_ematch_6303_; lean_object* v_mvarId_6304_; lean_object* v___x_6306_; uint8_t v_isShared_6307_; uint8_t v_isSharedCheck_6361_; 
v_a_6301_ = lean_ctor_get(v___x_6300_, 0);
lean_inc(v_a_6301_);
lean_dec_ref_known(v___x_6300_, 1);
v_toGoalState_6302_ = lean_ctor_get(v_a_6301_, 0);
lean_inc_ref(v_toGoalState_6302_);
v_ematch_6303_ = lean_ctor_get(v_toGoalState_6302_, 13);
lean_inc_ref(v_ematch_6303_);
v_mvarId_6304_ = lean_ctor_get(v_a_6301_, 1);
v_isSharedCheck_6361_ = !lean_is_exclusive(v_a_6301_);
if (v_isSharedCheck_6361_ == 0)
{
lean_object* v_unused_6362_; 
v_unused_6362_ = lean_ctor_get(v_a_6301_, 0);
lean_dec(v_unused_6362_);
v___x_6306_ = v_a_6301_;
v_isShared_6307_ = v_isSharedCheck_6361_;
goto v_resetjp_6305_;
}
else
{
lean_inc(v_mvarId_6304_);
lean_dec(v_a_6301_);
v___x_6306_ = lean_box(0);
v_isShared_6307_ = v_isSharedCheck_6361_;
goto v_resetjp_6305_;
}
v_resetjp_6305_:
{
lean_object* v_nextDeclIdx_6308_; lean_object* v_enodeMap_6309_; lean_object* v_exprs_6310_; lean_object* v_parents_6311_; lean_object* v_congrTable_6312_; lean_object* v_appMap_6313_; lean_object* v_indicesFound_6314_; lean_object* v_toProcess_6315_; lean_object* v_internalizing_6316_; uint8_t v_inconsistent_6317_; lean_object* v_nextIdx_6318_; lean_object* v_newRawFacts_6319_; lean_object* v_facts_6320_; lean_object* v_extThms_6321_; lean_object* v_inj_6322_; lean_object* v_split_6323_; lean_object* v_clean_6324_; lean_object* v_sstates_6325_; lean_object* v_gmt_6326_; lean_object* v_thms_6327_; lean_object* v_newThms_6328_; lean_object* v_numInstances_6329_; lean_object* v_numDelayedInstances_6330_; lean_object* v_num_6331_; lean_object* v_preInstances_6332_; lean_object* v_nextThmIdx_6333_; lean_object* v_matchEqNames_6334_; lean_object* v_delayedThmInsts_6335_; lean_object* v___x_6336_; lean_object* v___f_6337_; lean_object* v___x_6338_; 
v_nextDeclIdx_6308_ = lean_ctor_get(v_toGoalState_6302_, 0);
lean_inc(v_nextDeclIdx_6308_);
v_enodeMap_6309_ = lean_ctor_get(v_toGoalState_6302_, 1);
lean_inc_ref(v_enodeMap_6309_);
v_exprs_6310_ = lean_ctor_get(v_toGoalState_6302_, 2);
lean_inc_ref(v_exprs_6310_);
v_parents_6311_ = lean_ctor_get(v_toGoalState_6302_, 3);
lean_inc_ref(v_parents_6311_);
v_congrTable_6312_ = lean_ctor_get(v_toGoalState_6302_, 4);
lean_inc_ref(v_congrTable_6312_);
v_appMap_6313_ = lean_ctor_get(v_toGoalState_6302_, 5);
lean_inc_ref(v_appMap_6313_);
v_indicesFound_6314_ = lean_ctor_get(v_toGoalState_6302_, 6);
lean_inc_ref(v_indicesFound_6314_);
v_toProcess_6315_ = lean_ctor_get(v_toGoalState_6302_, 7);
lean_inc_ref(v_toProcess_6315_);
v_internalizing_6316_ = lean_ctor_get(v_toGoalState_6302_, 8);
lean_inc_ref(v_internalizing_6316_);
v_inconsistent_6317_ = lean_ctor_get_uint8(v_toGoalState_6302_, sizeof(void*)*18);
v_nextIdx_6318_ = lean_ctor_get(v_toGoalState_6302_, 9);
lean_inc(v_nextIdx_6318_);
v_newRawFacts_6319_ = lean_ctor_get(v_toGoalState_6302_, 10);
lean_inc_ref(v_newRawFacts_6319_);
v_facts_6320_ = lean_ctor_get(v_toGoalState_6302_, 11);
lean_inc_ref(v_facts_6320_);
v_extThms_6321_ = lean_ctor_get(v_toGoalState_6302_, 12);
lean_inc_ref(v_extThms_6321_);
v_inj_6322_ = lean_ctor_get(v_toGoalState_6302_, 14);
lean_inc_ref(v_inj_6322_);
v_split_6323_ = lean_ctor_get(v_toGoalState_6302_, 15);
lean_inc_ref(v_split_6323_);
v_clean_6324_ = lean_ctor_get(v_toGoalState_6302_, 16);
lean_inc_ref(v_clean_6324_);
v_sstates_6325_ = lean_ctor_get(v_toGoalState_6302_, 17);
lean_inc_ref(v_sstates_6325_);
lean_dec_ref(v_toGoalState_6302_);
v_gmt_6326_ = lean_ctor_get(v_ematch_6303_, 1);
lean_inc(v_gmt_6326_);
v_thms_6327_ = lean_ctor_get(v_ematch_6303_, 2);
lean_inc_ref(v_thms_6327_);
v_newThms_6328_ = lean_ctor_get(v_ematch_6303_, 3);
lean_inc_ref(v_newThms_6328_);
v_numInstances_6329_ = lean_ctor_get(v_ematch_6303_, 4);
lean_inc(v_numInstances_6329_);
v_numDelayedInstances_6330_ = lean_ctor_get(v_ematch_6303_, 5);
lean_inc(v_numDelayedInstances_6330_);
v_num_6331_ = lean_ctor_get(v_ematch_6303_, 6);
lean_inc(v_num_6331_);
v_preInstances_6332_ = lean_ctor_get(v_ematch_6303_, 7);
lean_inc_ref(v_preInstances_6332_);
v_nextThmIdx_6333_ = lean_ctor_get(v_ematch_6303_, 8);
lean_inc(v_nextThmIdx_6333_);
v_matchEqNames_6334_ = lean_ctor_get(v_ematch_6303_, 9);
lean_inc_ref(v_matchEqNames_6334_);
v_delayedThmInsts_6335_ = lean_ctor_get(v_ematch_6303_, 10);
lean_inc_ref(v_delayedThmInsts_6335_);
lean_dec_ref(v_ematch_6303_);
v___x_6336_ = lean_box(v_inconsistent_6317_);
v___f_6337_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 39, 29);
lean_closure_set(v___f_6337_, 0, v_thms_6327_);
lean_closure_set(v___f_6337_, 1, v_newThms_6328_);
lean_closure_set(v___f_6337_, 2, v_gmt_6326_);
lean_closure_set(v___f_6337_, 3, v_numInstances_6329_);
lean_closure_set(v___f_6337_, 4, v_numDelayedInstances_6330_);
lean_closure_set(v___f_6337_, 5, v_num_6331_);
lean_closure_set(v___f_6337_, 6, v_preInstances_6332_);
lean_closure_set(v___f_6337_, 7, v_nextThmIdx_6333_);
lean_closure_set(v___f_6337_, 8, v_matchEqNames_6334_);
lean_closure_set(v___f_6337_, 9, v_delayedThmInsts_6335_);
lean_closure_set(v___f_6337_, 10, v_nextDeclIdx_6308_);
lean_closure_set(v___f_6337_, 11, v_enodeMap_6309_);
lean_closure_set(v___f_6337_, 12, v_exprs_6310_);
lean_closure_set(v___f_6337_, 13, v_parents_6311_);
lean_closure_set(v___f_6337_, 14, v_congrTable_6312_);
lean_closure_set(v___f_6337_, 15, v_appMap_6313_);
lean_closure_set(v___f_6337_, 16, v_indicesFound_6314_);
lean_closure_set(v___f_6337_, 17, v_toProcess_6315_);
lean_closure_set(v___f_6337_, 18, v_internalizing_6316_);
lean_closure_set(v___f_6337_, 19, v___x_6336_);
lean_closure_set(v___f_6337_, 20, v_nextIdx_6318_);
lean_closure_set(v___f_6337_, 21, v_newRawFacts_6319_);
lean_closure_set(v___f_6337_, 22, v_facts_6320_);
lean_closure_set(v___f_6337_, 23, v_extThms_6321_);
lean_closure_set(v___f_6337_, 24, v_inj_6322_);
lean_closure_set(v___f_6337_, 25, v_split_6323_);
lean_closure_set(v___f_6337_, 26, v_clean_6324_);
lean_closure_set(v___f_6337_, 27, v_sstates_6325_);
lean_closure_set(v___f_6337_, 28, v_mvarId_6304_);
v___x_6338_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_6337_, v___x_6299_, v___y_6270_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_);
if (lean_obj_tag(v___x_6338_) == 0)
{
lean_object* v_a_6339_; lean_object* v___x_6340_; lean_object* v___x_6342_; 
v_a_6339_ = lean_ctor_get(v___x_6338_, 0);
lean_inc(v_a_6339_);
lean_dec_ref_known(v___x_6338_, 1);
v___x_6340_ = lean_box(0);
if (v_isShared_6307_ == 0)
{
lean_ctor_set_tag(v___x_6306_, 1);
lean_ctor_set(v___x_6306_, 1, v___x_6340_);
lean_ctor_set(v___x_6306_, 0, v_a_6339_);
v___x_6342_ = v___x_6306_;
goto v_reusejp_6341_;
}
else
{
lean_object* v_reuseFailAlloc_6352_; 
v_reuseFailAlloc_6352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6352_, 0, v_a_6339_);
lean_ctor_set(v_reuseFailAlloc_6352_, 1, v___x_6340_);
v___x_6342_ = v_reuseFailAlloc_6352_;
goto v_reusejp_6341_;
}
v_reusejp_6341_:
{
lean_object* v___x_6343_; 
v___x_6343_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_6342_, v___y_6270_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_);
if (lean_obj_tag(v___x_6343_) == 0)
{
lean_dec_ref_known(v___x_6343_, 1);
v___y_6245_ = v_a_6278_;
v___y_6246_ = v___x_6299_;
v___y_6247_ = v___y_6270_;
v___y_6248_ = v___y_6271_;
v___y_6249_ = v___y_6272_;
v___y_6250_ = v___y_6273_;
v___y_6251_ = v___y_6274_;
v___y_6252_ = v___y_6275_;
v___y_6253_ = v___y_6276_;
goto v___jp_6244_;
}
else
{
lean_object* v_a_6344_; lean_object* v___x_6346_; uint8_t v_isShared_6347_; uint8_t v_isSharedCheck_6351_; 
lean_dec_ref_known(v___x_6299_, 5);
lean_dec(v_a_6278_);
lean_dec_ref(v_k_6234_);
v_a_6344_ = lean_ctor_get(v___x_6343_, 0);
v_isSharedCheck_6351_ = !lean_is_exclusive(v___x_6343_);
if (v_isSharedCheck_6351_ == 0)
{
v___x_6346_ = v___x_6343_;
v_isShared_6347_ = v_isSharedCheck_6351_;
goto v_resetjp_6345_;
}
else
{
lean_inc(v_a_6344_);
lean_dec(v___x_6343_);
v___x_6346_ = lean_box(0);
v_isShared_6347_ = v_isSharedCheck_6351_;
goto v_resetjp_6345_;
}
v_resetjp_6345_:
{
lean_object* v___x_6349_; 
if (v_isShared_6347_ == 0)
{
v___x_6349_ = v___x_6346_;
goto v_reusejp_6348_;
}
else
{
lean_object* v_reuseFailAlloc_6350_; 
v_reuseFailAlloc_6350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6350_, 0, v_a_6344_);
v___x_6349_ = v_reuseFailAlloc_6350_;
goto v_reusejp_6348_;
}
v_reusejp_6348_:
{
return v___x_6349_;
}
}
}
}
}
else
{
lean_object* v_a_6353_; lean_object* v___x_6355_; uint8_t v_isShared_6356_; uint8_t v_isSharedCheck_6360_; 
lean_del_object(v___x_6306_);
lean_dec_ref_known(v___x_6299_, 5);
lean_dec(v_a_6278_);
lean_dec_ref(v_k_6234_);
v_a_6353_ = lean_ctor_get(v___x_6338_, 0);
v_isSharedCheck_6360_ = !lean_is_exclusive(v___x_6338_);
if (v_isSharedCheck_6360_ == 0)
{
v___x_6355_ = v___x_6338_;
v_isShared_6356_ = v_isSharedCheck_6360_;
goto v_resetjp_6354_;
}
else
{
lean_inc(v_a_6353_);
lean_dec(v___x_6338_);
v___x_6355_ = lean_box(0);
v_isShared_6356_ = v_isSharedCheck_6360_;
goto v_resetjp_6354_;
}
v_resetjp_6354_:
{
lean_object* v___x_6358_; 
if (v_isShared_6356_ == 0)
{
v___x_6358_ = v___x_6355_;
goto v_reusejp_6357_;
}
else
{
lean_object* v_reuseFailAlloc_6359_; 
v_reuseFailAlloc_6359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6359_, 0, v_a_6353_);
v___x_6358_ = v_reuseFailAlloc_6359_;
goto v_reusejp_6357_;
}
v_reusejp_6357_:
{
return v___x_6358_;
}
}
}
}
}
else
{
lean_object* v_a_6363_; lean_object* v___x_6365_; uint8_t v_isShared_6366_; uint8_t v_isSharedCheck_6370_; 
lean_dec_ref_known(v___x_6299_, 5);
lean_dec(v_a_6278_);
lean_dec_ref(v_k_6234_);
v_a_6363_ = lean_ctor_get(v___x_6300_, 0);
v_isSharedCheck_6370_ = !lean_is_exclusive(v___x_6300_);
if (v_isSharedCheck_6370_ == 0)
{
v___x_6365_ = v___x_6300_;
v_isShared_6366_ = v_isSharedCheck_6370_;
goto v_resetjp_6364_;
}
else
{
lean_inc(v_a_6363_);
lean_dec(v___x_6300_);
v___x_6365_ = lean_box(0);
v_isShared_6366_ = v_isSharedCheck_6370_;
goto v_resetjp_6364_;
}
v_resetjp_6364_:
{
lean_object* v___x_6368_; 
if (v_isShared_6366_ == 0)
{
v___x_6368_ = v___x_6365_;
goto v_reusejp_6367_;
}
else
{
lean_object* v_reuseFailAlloc_6369_; 
v_reuseFailAlloc_6369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6369_, 0, v_a_6363_);
v___x_6368_ = v_reuseFailAlloc_6369_;
goto v_reusejp_6367_;
}
v_reusejp_6367_:
{
return v___x_6368_;
}
}
}
}
}
else
{
lean_object* v_a_6371_; lean_object* v___x_6373_; uint8_t v_isShared_6374_; uint8_t v_isSharedCheck_6378_; 
lean_dec_ref(v_k_6234_);
v_a_6371_ = lean_ctor_get(v___x_6277_, 0);
v_isSharedCheck_6378_ = !lean_is_exclusive(v___x_6277_);
if (v_isSharedCheck_6378_ == 0)
{
v___x_6373_ = v___x_6277_;
v_isShared_6374_ = v_isSharedCheck_6378_;
goto v_resetjp_6372_;
}
else
{
lean_inc(v_a_6371_);
lean_dec(v___x_6277_);
v___x_6373_ = lean_box(0);
v_isShared_6374_ = v_isSharedCheck_6378_;
goto v_resetjp_6372_;
}
v_resetjp_6372_:
{
lean_object* v___x_6376_; 
if (v_isShared_6374_ == 0)
{
v___x_6376_ = v___x_6373_;
goto v_reusejp_6375_;
}
else
{
lean_object* v_reuseFailAlloc_6377_; 
v_reuseFailAlloc_6377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6377_, 0, v_a_6371_);
v___x_6376_ = v_reuseFailAlloc_6377_;
goto v_reusejp_6375_;
}
v_reusejp_6375_:
{
return v___x_6376_;
}
}
}
}
v___jp_6379_:
{
uint8_t v___x_6381_; 
v___x_6381_ = 1;
if (v_only_6233_ == 0)
{
v___y_6266_ = v___x_6381_;
v___y_6267_ = v___y_6380_;
v_params_6268_ = v_params_6231_;
v___y_6269_ = v_a_6235_;
v___y_6270_ = v_a_6236_;
v___y_6271_ = v_a_6237_;
v___y_6272_ = v_a_6238_;
v___y_6273_ = v_a_6239_;
v___y_6274_ = v_a_6240_;
v___y_6275_ = v_a_6241_;
v___y_6276_ = v_a_6242_;
goto v___jp_6265_;
}
else
{
lean_object* v_config_6382_; lean_object* v_extensions_6383_; lean_object* v_extra_6384_; lean_object* v_extraInj_6385_; lean_object* v_extraFacts_6386_; lean_object* v_symPrios_6387_; lean_object* v_norm_6388_; lean_object* v_normProcs_6389_; lean_object* v___x_6391_; uint8_t v_isShared_6392_; uint8_t v_isSharedCheck_6400_; 
v_config_6382_ = lean_ctor_get(v_params_6231_, 0);
v_extensions_6383_ = lean_ctor_get(v_params_6231_, 1);
v_extra_6384_ = lean_ctor_get(v_params_6231_, 2);
v_extraInj_6385_ = lean_ctor_get(v_params_6231_, 3);
v_extraFacts_6386_ = lean_ctor_get(v_params_6231_, 4);
v_symPrios_6387_ = lean_ctor_get(v_params_6231_, 5);
v_norm_6388_ = lean_ctor_get(v_params_6231_, 6);
v_normProcs_6389_ = lean_ctor_get(v_params_6231_, 7);
v_isSharedCheck_6400_ = !lean_is_exclusive(v_params_6231_);
if (v_isSharedCheck_6400_ == 0)
{
lean_object* v_unused_6401_; 
v_unused_6401_ = lean_ctor_get(v_params_6231_, 8);
lean_dec(v_unused_6401_);
v___x_6391_ = v_params_6231_;
v_isShared_6392_ = v_isSharedCheck_6400_;
goto v_resetjp_6390_;
}
else
{
lean_inc(v_normProcs_6389_);
lean_inc(v_norm_6388_);
lean_inc(v_symPrios_6387_);
lean_inc(v_extraFacts_6386_);
lean_inc(v_extraInj_6385_);
lean_inc(v_extra_6384_);
lean_inc(v_extensions_6383_);
lean_inc(v_config_6382_);
lean_dec(v_params_6231_);
v___x_6391_ = lean_box(0);
v_isShared_6392_ = v_isSharedCheck_6400_;
goto v_resetjp_6390_;
}
v_resetjp_6390_:
{
size_t v_sz_6393_; size_t v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; lean_object* v_params_6398_; 
v_sz_6393_ = lean_array_size(v_extensions_6383_);
v___x_6394_ = ((size_t)0ULL);
v___x_6395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_6393_, v___x_6394_, v_extensions_6383_);
v___x_6396_ = lean_box(0);
if (v_isShared_6392_ == 0)
{
lean_ctor_set(v___x_6391_, 8, v___x_6396_);
lean_ctor_set(v___x_6391_, 1, v___x_6395_);
v_params_6398_ = v___x_6391_;
goto v_reusejp_6397_;
}
else
{
lean_object* v_reuseFailAlloc_6399_; 
v_reuseFailAlloc_6399_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6399_, 0, v_config_6382_);
lean_ctor_set(v_reuseFailAlloc_6399_, 1, v___x_6395_);
lean_ctor_set(v_reuseFailAlloc_6399_, 2, v_extra_6384_);
lean_ctor_set(v_reuseFailAlloc_6399_, 3, v_extraInj_6385_);
lean_ctor_set(v_reuseFailAlloc_6399_, 4, v_extraFacts_6386_);
lean_ctor_set(v_reuseFailAlloc_6399_, 5, v_symPrios_6387_);
lean_ctor_set(v_reuseFailAlloc_6399_, 6, v_norm_6388_);
lean_ctor_set(v_reuseFailAlloc_6399_, 7, v_normProcs_6389_);
lean_ctor_set(v_reuseFailAlloc_6399_, 8, v___x_6396_);
v_params_6398_ = v_reuseFailAlloc_6399_;
goto v_reusejp_6397_;
}
v_reusejp_6397_:
{
v___y_6266_ = v___x_6381_;
v___y_6267_ = v___y_6380_;
v_params_6268_ = v_params_6398_;
v___y_6269_ = v_a_6235_;
v___y_6270_ = v_a_6236_;
v___y_6271_ = v_a_6237_;
v___y_6272_ = v_a_6238_;
v___y_6273_ = v_a_6239_;
v___y_6274_ = v_a_6240_;
v___y_6275_ = v_a_6241_;
v___y_6276_ = v_a_6242_;
goto v___jp_6265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_6407_, lean_object* v_ps_6408_, lean_object* v_only_6409_, lean_object* v_k_6410_, lean_object* v_a_6411_, lean_object* v_a_6412_, lean_object* v_a_6413_, lean_object* v_a_6414_, lean_object* v_a_6415_, lean_object* v_a_6416_, lean_object* v_a_6417_, lean_object* v_a_6418_, lean_object* v_a_6419_){
_start:
{
uint8_t v_only_boxed_6420_; lean_object* v_res_6421_; 
v_only_boxed_6420_ = lean_unbox(v_only_6409_);
v_res_6421_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_6407_, v_ps_6408_, v_only_boxed_6420_, v_k_6410_, v_a_6411_, v_a_6412_, v_a_6413_, v_a_6414_, v_a_6415_, v_a_6416_, v_a_6417_, v_a_6418_);
lean_dec(v_a_6418_);
lean_dec_ref(v_a_6417_);
lean_dec(v_a_6416_);
lean_dec_ref(v_a_6415_);
lean_dec(v_a_6414_);
lean_dec_ref(v_a_6413_);
lean_dec(v_a_6412_);
lean_dec_ref(v_a_6411_);
lean_dec_ref(v_ps_6408_);
return v_res_6421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_6422_, lean_object* v_params_6423_, lean_object* v_ps_6424_, uint8_t v_only_6425_, lean_object* v_k_6426_, lean_object* v_a_6427_, lean_object* v_a_6428_, lean_object* v_a_6429_, lean_object* v_a_6430_, lean_object* v_a_6431_, lean_object* v_a_6432_, lean_object* v_a_6433_, lean_object* v_a_6434_){
_start:
{
lean_object* v___x_6436_; 
v___x_6436_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_6423_, v_ps_6424_, v_only_6425_, v_k_6426_, v_a_6427_, v_a_6428_, v_a_6429_, v_a_6430_, v_a_6431_, v_a_6432_, v_a_6433_, v_a_6434_);
return v___x_6436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_6437_, lean_object* v_params_6438_, lean_object* v_ps_6439_, lean_object* v_only_6440_, lean_object* v_k_6441_, lean_object* v_a_6442_, lean_object* v_a_6443_, lean_object* v_a_6444_, lean_object* v_a_6445_, lean_object* v_a_6446_, lean_object* v_a_6447_, lean_object* v_a_6448_, lean_object* v_a_6449_, lean_object* v_a_6450_){
_start:
{
uint8_t v_only_boxed_6451_; lean_object* v_res_6452_; 
v_only_boxed_6451_ = lean_unbox(v_only_6440_);
v_res_6452_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_6437_, v_params_6438_, v_ps_6439_, v_only_boxed_6451_, v_k_6441_, v_a_6442_, v_a_6443_, v_a_6444_, v_a_6445_, v_a_6446_, v_a_6447_, v_a_6448_, v_a_6449_);
lean_dec(v_a_6449_);
lean_dec_ref(v_a_6448_);
lean_dec(v_a_6447_);
lean_dec_ref(v_a_6446_);
lean_dec(v_a_6445_);
lean_dec_ref(v_a_6444_);
lean_dec(v_a_6443_);
lean_dec_ref(v_a_6442_);
lean_dec_ref(v_ps_6439_);
return v_res_6452_;
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
