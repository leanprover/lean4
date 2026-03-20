// Lean compiler output
// Module: Lean.LibrarySuggestions.Basic
// Imports: public import Lean.Meta.Eval public import Lean.Meta.CompletionName public import Init.Data.Random public import Lean.Elab.Tactic.Grind.Annotated import Init.Omega
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
lean_object* lean_array_get_size(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedParamInfo_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_isImplicitReducibleCore(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Grind_isGrindAnnotatedModule(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint64_t lean_string_hash(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_mul(double, double);
uint32_t lean_float_to_uint32(double);
lean_object* lean_uint32_to_nat(uint32_t);
double lean_float_sub(double, double);
double lean_float_add(double, double);
uint8_t lean_float_decLe(double, double);
double lean_float_div(double, double);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object*);
lean_object* lean_float_to_string(double);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_anyS(lean_object*, lean_object*);
uint8_t l_Lean_Linter_isDeprecated(lean_object*, lean_object*);
uint8_t l_Lean_Name_isInternalDetail(lean_object*);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_beq(double, double);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_rand(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_IO_stdGenRef;
lean_object* l_Lean_Environment_const2ModIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__0;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__1;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__2;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_relevantConstants___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_relevantConstants___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_relevantConstants___closed__0 = (const lean_object*)&l_Lean_Expr_relevantConstants___closed__0_value;
static const lean_array_object l_Lean_Expr_relevantConstants___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Expr_relevantConstants___closed__1 = (const lean_object*)&l_Lean_Expr_relevantConstants___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_relevantConstantsAsSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_relevantConstantsAsSet___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_relevantConstantsAsSet___closed__0 = (const lean_object*)&l_Lean_Expr_relevantConstantsAsSet___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getConstants_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getConstants_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___closed__0 = (const lean_object*)&l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getRelevantConstants_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getRelevantConstants_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_ppSelector(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_ppSelector___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_Selector_postFilter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_Selector_postFilter___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_Selector_postFilter___closed__0_value;
static const lean_array_object l_Lean_LibrarySuggestions_Selector_postFilter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_Selector_postFilter___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_maxSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_maxSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_Selector_combine_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_LibrarySuggestions_Selector_combine___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_Selector_combine___closed__0;
static lean_once_cell_t l_Lean_LibrarySuggestions_Selector_combine___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_Selector_combine___closed__1;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_combine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_combine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__0_value)}};
static const lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg(double, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_LibrarySuggestions_Selector_intersperse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_LibrarySuggestions_Selector_intersperse___closed__0;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___closed__1___boxed__const__1;
static lean_once_cell_t l_Lean_LibrarySuggestions_Selector_intersperse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___closed__1;
static lean_once_cell_t l_Lean_LibrarySuggestions_Selector_intersperse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___closed__2;
static lean_once_cell_t l_Lean_LibrarySuggestions_Selector_intersperse___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___closed__3;
static lean_once_cell_t l_Lean_LibrarySuggestions_Selector_intersperse___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___closed__4;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_intersperse(lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0(double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LibrarySuggestions"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "moduleDenyListExt"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(230, 123, 203, 142, 120, 156, 209, 106)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__10_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__10_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__10_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__11_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__10_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__11_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__11_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__12_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__11_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__12_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__12_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__13_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__12_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__13_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__13_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__14_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__13_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__14_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__14_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_moduleDenyListExt;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nameDenyListExt"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 26, 152, 186, 195, 69, 163, 18)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__13_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_nameDenyListExt;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "typePrefixDenyListExt"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 199, 197, 114, 42, 156, 103, 187)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_typePrefixDenyListExt;
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedModule___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedModule___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedModule___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedModule___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedPremise___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedPremise___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_isDeniedPremise___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_isDeniedPremise___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_isDeniedPremise___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_isDeniedPremise___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_isDeniedPremise___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedPremise(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_random_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "librarySuggestionsExt"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 152, 201, 31, 243, 26, 178, 82)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_librarySuggestionsExt;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_LibrarySuggestions_initFn___lam__0___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___lam__0___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Selector"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 39, 7, 240, 9, 153, 37, 224)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_LibrarySuggestions_initFn___lam__0___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___lam__0___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declaration '"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_LibrarySuggestions_initFn___lam__0___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___lam__0___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "' must have type `Selector`"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_LibrarySuggestions_initFn___lam__0___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "library_suggestions"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(112, 230, 242, 174, 112, 244, 220, 236)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "library suggestions selector"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "librarySuggestionsAttr"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 31, 118, 101, 75, 194, 175, 121)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_librarySuggestionsAttr;
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_getSelectorImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_getSelectorImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_select___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 180, .m_capacity = 180, .m_length = 179, .m_data = "No library suggestions engine registered. (Add `import Lean.LibrarySuggestions.Default` to use Lean's built-in engine, or use `set_library_suggestions` to configure a custom one.)"};
static const lean_object* l_Lean_LibrarySuggestions_select___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_select___closed__0_value;
static lean_once_cell_t l_Lean_LibrarySuggestions_select___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_select___closed__1;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_select(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_select___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "setLibrarySuggestionsCmd"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 118, 147, 72, 144, 22, 225, 39)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__4 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__4_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__4_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__6 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__6_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__8 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__8_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__9 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__9_value;
static lean_once_cell_t l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__10;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__12 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__12_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__12_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__14 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__14_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__15 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__15_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__15_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__17 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__17_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__17_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__19 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__19_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__20 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__20_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__19_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__20_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value;
static lean_once_cell_t l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__22;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__23 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__23_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24_value_aux_2),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__17_value),LEAN_SCALAR_PTR_LITERAL(99, 134, 241, 204, 211, 206, 124, 144)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25_value_aux_2),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__15_value),LEAN_SCALAR_PTR_LITERAL(124, 247, 59, 43, 44, 177, 111, 66)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__26 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__26_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__26_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__29 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__29_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__29_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value;
static const lean_array_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__31 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__31_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__9_value),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__31_value)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__32 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__32_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__35 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__35_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__35_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__37 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__37_value;
static lean_once_cell_t l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(206, 17, 56, 16, 127, 134, 149, 116)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__39 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__39_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__41 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__41_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__41_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__42 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__42_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40_value),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__42_value)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__43 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__43_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__44 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__44_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__44_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__46 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__46_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__47 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__47_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__48 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__48_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__47_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__48_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_librarySuggestions"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__50 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__50_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__50_value),LEAN_SCALAR_PTR_LITERAL(147, 241, 103, 239, 116, 245, 70, 103)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__51 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__51_value;
static const lean_closure_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Macro_addMacroScope, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__51_value)} };
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__52 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__52_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__54_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__54_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53_value),LEAN_SCALAR_PTR_LITERAL(198, 90, 67, 198, 19, 167, 19, 166)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__54 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__54_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "Add `import Lean.LibrarySuggestions.Basic` before using the `set_library_suggestions` command."};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__55 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__55_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__55_value)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__56 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__56_value;
static lean_once_cell_t l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__57;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "elabSetLibrarySuggestions"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 220, 99, 96, 165, 4, 120, 100)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__3_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " (score: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Library suggestions:"};
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_evalSuggestions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_Selector_postFilter___closed__0_value)} };
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "suggestions"};
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 205, 204, 217, 194, 115, 0, 147)}};
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value;
static const lean_string_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalSuggestions"};
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__2 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__2_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 185, 91, 28, 225, 145, 246, 66)}};
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v_b_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_7(v_k_1_, v_b_3_, v___y_2_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v___y_11_, lean_object* v_b_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0(v_k_10_, v___y_11_, v_b_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg(lean_object* v_name_19_, uint8_t v_bi_20_, lean_object* v_type_21_, lean_object* v_k_22_, uint8_t v_kind_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v___f_30_; lean_object* v___x_31_; 
v___f_30_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_30_, 0, v_k_22_);
lean_closure_set(v___f_30_, 1, v___y_24_);
v___x_31_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_19_, v_bi_20_, v_type_21_, v___f_30_, v_kind_23_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
v_a_40_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v___x_31_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_31_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___boxed(lean_object* v_name_48_, lean_object* v_bi_49_, lean_object* v_type_50_, lean_object* v_k_51_, lean_object* v_kind_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
uint8_t v_bi_boxed_59_; uint8_t v_kind_boxed_60_; lean_object* v_res_61_; 
v_bi_boxed_59_ = lean_unbox(v_bi_49_);
v_kind_boxed_60_ = lean_unbox(v_kind_52_);
v_res_61_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg(v_name_48_, v_bi_boxed_59_, v_type_50_, v_k_51_, v_kind_boxed_60_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0(lean_object* v_00_u03b1_62_, lean_object* v_name_63_, uint8_t v_bi_64_, lean_object* v_type_65_, lean_object* v_k_66_, uint8_t v_kind_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg(v_name_63_, v_bi_64_, v_type_65_, v_k_66_, v_kind_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___boxed(lean_object* v_00_u03b1_75_, lean_object* v_name_76_, lean_object* v_bi_77_, lean_object* v_type_78_, lean_object* v_k_79_, lean_object* v_kind_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
uint8_t v_bi_boxed_87_; uint8_t v_kind_boxed_88_; lean_object* v_res_89_; 
v_bi_boxed_87_ = lean_unbox(v_bi_77_);
v_kind_boxed_88_ = lean_unbox(v_kind_80_);
v_res_89_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0(v_00_u03b1_75_, v_name_76_, v_bi_boxed_87_, v_type_78_, v_k_79_, v_kind_boxed_88_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg(lean_object* v_name_90_, lean_object* v_type_91_, lean_object* v_val_92_, lean_object* v_k_93_, uint8_t v_nondep_94_, uint8_t v_kind_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___f_102_; lean_object* v___x_103_; 
v___f_102_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_102_, 0, v_k_93_);
lean_closure_set(v___f_102_, 1, v___y_96_);
v___x_103_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_90_, v_type_91_, v_val_92_, v___f_102_, v_nondep_94_, v_kind_95_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
v_a_112_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_103_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_103_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg___boxed(lean_object* v_name_120_, lean_object* v_type_121_, lean_object* v_val_122_, lean_object* v_k_123_, lean_object* v_nondep_124_, lean_object* v_kind_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
uint8_t v_nondep_boxed_132_; uint8_t v_kind_boxed_133_; lean_object* v_res_134_; 
v_nondep_boxed_132_ = lean_unbox(v_nondep_124_);
v_kind_boxed_133_ = lean_unbox(v_kind_125_);
v_res_134_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg(v_name_120_, v_type_121_, v_val_122_, v_k_123_, v_nondep_boxed_132_, v_kind_boxed_133_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3(lean_object* v_00_u03b1_135_, lean_object* v_name_136_, lean_object* v_type_137_, lean_object* v_val_138_, lean_object* v_k_139_, uint8_t v_nondep_140_, uint8_t v_kind_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg(v_name_136_, v_type_137_, v_val_138_, v_k_139_, v_nondep_140_, v_kind_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___boxed(lean_object* v_00_u03b1_149_, lean_object* v_name_150_, lean_object* v_type_151_, lean_object* v_val_152_, lean_object* v_k_153_, lean_object* v_nondep_154_, lean_object* v_kind_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
uint8_t v_nondep_boxed_162_; uint8_t v_kind_boxed_163_; lean_object* v_res_164_; 
v_nondep_boxed_162_ = lean_unbox(v_nondep_154_);
v_kind_boxed_163_ = lean_unbox(v_kind_155_);
v_res_164_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3(v_00_u03b1_149_, v_name_150_, v_type_151_, v_val_152_, v_k_153_, v_nondep_boxed_162_, v_kind_boxed_163_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg(lean_object* v_declName_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; lean_object* v_env_170_; uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_169_ = lean_st_ref_get(v___y_167_);
v_env_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc_ref(v_env_170_);
lean_dec(v___x_169_);
v___x_171_ = l_Lean_isImplicitReducibleCore(v_env_170_, v_declName_165_);
v___x_172_ = lean_box(v___x_171_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___y_166_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg___boxed(lean_object* v_declName_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_isImplicitReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg(v_declName_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4(lean_object* v_declName_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_isImplicitReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg(v_declName_180_, v___y_181_, v___y_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_isImplicitReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___boxed(lean_object* v_declName_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_isImplicitReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4(v_declName_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6_spec__7___redArg(lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
return v_x_196_;
}
else
{
lean_object* v_key_198_; lean_object* v_value_199_; lean_object* v_tail_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_226_; 
v_key_198_ = lean_ctor_get(v_x_197_, 0);
v_value_199_ = lean_ctor_get(v_x_197_, 1);
v_tail_200_ = lean_ctor_get(v_x_197_, 2);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_197_);
if (v_isSharedCheck_226_ == 0)
{
v___x_202_ = v_x_197_;
v_isShared_203_ = v_isSharedCheck_226_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_tail_200_);
lean_inc(v_value_199_);
lean_inc(v_key_198_);
lean_dec(v_x_197_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_226_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; size_t v___x_205_; uint64_t v___x_206_; uint64_t v___x_207_; uint64_t v___x_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v_fold_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_204_ = lean_array_get_size(v_x_196_);
v___x_205_ = lean_ptr_addr(v_key_198_);
v___x_206_ = lean_usize_to_uint64(v___x_205_);
v___x_207_ = 11ULL;
v___x_208_ = lean_uint64_mix_hash(v___x_206_, v___x_207_);
v___x_209_ = 32ULL;
v___x_210_ = lean_uint64_shift_right(v___x_208_, v___x_209_);
v_fold_211_ = lean_uint64_xor(v___x_208_, v___x_210_);
v___x_212_ = 16ULL;
v___x_213_ = lean_uint64_shift_right(v_fold_211_, v___x_212_);
v___x_214_ = lean_uint64_xor(v_fold_211_, v___x_213_);
v___x_215_ = lean_uint64_to_usize(v___x_214_);
v___x_216_ = lean_usize_of_nat(v___x_204_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_sub(v___x_216_, v___x_217_);
v___x_219_ = lean_usize_land(v___x_215_, v___x_218_);
v___x_220_ = lean_array_uget_borrowed(v_x_196_, v___x_219_);
lean_inc(v___x_220_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 2, v___x_220_);
v___x_222_ = v___x_202_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_key_198_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_value_199_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v___x_220_);
v___x_222_ = v_reuseFailAlloc_225_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; 
v___x_223_ = lean_array_uset(v_x_196_, v___x_219_, v___x_222_);
v_x_196_ = v___x_223_;
v_x_197_ = v_tail_200_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6___redArg(lean_object* v_i_227_, lean_object* v_source_228_, lean_object* v_target_229_){
_start:
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_array_get_size(v_source_228_);
v___x_231_ = lean_nat_dec_lt(v_i_227_, v___x_230_);
if (v___x_231_ == 0)
{
lean_dec_ref(v_source_228_);
lean_dec(v_i_227_);
return v_target_229_;
}
else
{
lean_object* v_es_232_; lean_object* v___x_233_; lean_object* v_source_234_; lean_object* v_target_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_es_232_ = lean_array_fget(v_source_228_, v_i_227_);
v___x_233_ = lean_box(0);
v_source_234_ = lean_array_fset(v_source_228_, v_i_227_, v___x_233_);
v_target_235_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6_spec__7___redArg(v_target_229_, v_es_232_);
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_i_227_, v___x_236_);
lean_dec(v_i_227_);
v_i_227_ = v___x_237_;
v_source_228_ = v_source_234_;
v_target_229_ = v_target_235_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3___redArg(lean_object* v_data_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v_nbuckets_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_240_ = lean_array_get_size(v_data_239_);
v___x_241_ = lean_unsigned_to_nat(2u);
v_nbuckets_242_ = lean_nat_mul(v___x_240_, v___x_241_);
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = lean_box(0);
v___x_245_ = lean_mk_array(v_nbuckets_242_, v___x_244_);
v___x_246_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6___redArg(v___x_243_, v_data_239_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg(lean_object* v_a_247_, lean_object* v_x_248_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
uint8_t v___x_249_; 
v___x_249_ = 0;
return v___x_249_;
}
else
{
lean_object* v_key_250_; lean_object* v_tail_251_; size_t v___x_252_; size_t v___x_253_; uint8_t v___x_254_; 
v_key_250_ = lean_ctor_get(v_x_248_, 0);
v_tail_251_ = lean_ctor_get(v_x_248_, 2);
v___x_252_ = lean_ptr_addr(v_key_250_);
v___x_253_ = lean_ptr_addr(v_a_247_);
v___x_254_ = lean_usize_dec_eq(v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
v_x_248_ = v_tail_251_;
goto _start;
}
else
{
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg___boxed(lean_object* v_a_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg(v_a_256_, v_x_257_);
lean_dec(v_x_257_);
lean_dec_ref(v_a_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2___redArg(lean_object* v_m_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
lean_object* v_size_263_; lean_object* v_buckets_264_; lean_object* v___x_265_; size_t v___x_266_; uint64_t v___x_267_; uint64_t v___x_268_; uint64_t v___x_269_; uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v_fold_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; lean_object* v_bkt_281_; uint8_t v___x_282_; 
v_size_263_ = lean_ctor_get(v_m_260_, 0);
v_buckets_264_ = lean_ctor_get(v_m_260_, 1);
v___x_265_ = lean_array_get_size(v_buckets_264_);
v___x_266_ = lean_ptr_addr(v_a_261_);
v___x_267_ = lean_usize_to_uint64(v___x_266_);
v___x_268_ = 11ULL;
v___x_269_ = lean_uint64_mix_hash(v___x_267_, v___x_268_);
v___x_270_ = 32ULL;
v___x_271_ = lean_uint64_shift_right(v___x_269_, v___x_270_);
v_fold_272_ = lean_uint64_xor(v___x_269_, v___x_271_);
v___x_273_ = 16ULL;
v___x_274_ = lean_uint64_shift_right(v_fold_272_, v___x_273_);
v___x_275_ = lean_uint64_xor(v_fold_272_, v___x_274_);
v___x_276_ = lean_uint64_to_usize(v___x_275_);
v___x_277_ = lean_usize_of_nat(v___x_265_);
v___x_278_ = ((size_t)1ULL);
v___x_279_ = lean_usize_sub(v___x_277_, v___x_278_);
v___x_280_ = lean_usize_land(v___x_276_, v___x_279_);
v_bkt_281_ = lean_array_uget_borrowed(v_buckets_264_, v___x_280_);
v___x_282_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg(v_a_261_, v_bkt_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_303_; 
lean_inc_ref(v_buckets_264_);
lean_inc(v_size_263_);
v_isSharedCheck_303_ = !lean_is_exclusive(v_m_260_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; lean_object* v_unused_305_; 
v_unused_304_ = lean_ctor_get(v_m_260_, 1);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_m_260_, 0);
lean_dec(v_unused_305_);
v___x_284_ = v_m_260_;
v_isShared_285_ = v_isSharedCheck_303_;
goto v_resetjp_283_;
}
else
{
lean_dec(v_m_260_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_303_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v_size_x27_287_; lean_object* v___x_288_; lean_object* v_buckets_x27_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_286_ = lean_unsigned_to_nat(1u);
v_size_x27_287_ = lean_nat_add(v_size_263_, v___x_286_);
lean_dec(v_size_263_);
lean_inc(v_bkt_281_);
v___x_288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_288_, 0, v_a_261_);
lean_ctor_set(v___x_288_, 1, v_b_262_);
lean_ctor_set(v___x_288_, 2, v_bkt_281_);
v_buckets_x27_289_ = lean_array_uset(v_buckets_264_, v___x_280_, v___x_288_);
v___x_290_ = lean_unsigned_to_nat(4u);
v___x_291_ = lean_nat_mul(v_size_x27_287_, v___x_290_);
v___x_292_ = lean_unsigned_to_nat(3u);
v___x_293_ = lean_nat_div(v___x_291_, v___x_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_array_get_size(v_buckets_x27_289_);
v___x_295_ = lean_nat_dec_le(v___x_293_, v___x_294_);
lean_dec(v___x_293_);
if (v___x_295_ == 0)
{
lean_object* v_val_296_; lean_object* v___x_298_; 
v_val_296_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3___redArg(v_buckets_x27_289_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v_val_296_);
lean_ctor_set(v___x_284_, 0, v_size_x27_287_);
v___x_298_ = v___x_284_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_size_x27_287_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_val_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
else
{
lean_object* v___x_301_; 
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v_buckets_x27_289_);
lean_ctor_set(v___x_284_, 0, v_size_x27_287_);
v___x_301_ = v___x_284_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_size_x27_287_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_buckets_x27_289_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_dec(v_b_262_);
lean_dec_ref(v_a_261_);
return v_m_260_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg(lean_object* v_m_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_buckets_308_; lean_object* v___x_309_; size_t v___x_310_; uint64_t v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v_fold_316_; uint64_t v___x_317_; uint64_t v___x_318_; uint64_t v___x_319_; size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_buckets_308_ = lean_ctor_get(v_m_306_, 1);
v___x_309_ = lean_array_get_size(v_buckets_308_);
v___x_310_ = lean_ptr_addr(v_a_307_);
v___x_311_ = lean_usize_to_uint64(v___x_310_);
v___x_312_ = 11ULL;
v___x_313_ = lean_uint64_mix_hash(v___x_311_, v___x_312_);
v___x_314_ = 32ULL;
v___x_315_ = lean_uint64_shift_right(v___x_313_, v___x_314_);
v_fold_316_ = lean_uint64_xor(v___x_313_, v___x_315_);
v___x_317_ = 16ULL;
v___x_318_ = lean_uint64_shift_right(v_fold_316_, v___x_317_);
v___x_319_ = lean_uint64_xor(v_fold_316_, v___x_318_);
v___x_320_ = lean_uint64_to_usize(v___x_319_);
v___x_321_ = lean_usize_of_nat(v___x_309_);
v___x_322_ = ((size_t)1ULL);
v___x_323_ = lean_usize_sub(v___x_321_, v___x_322_);
v___x_324_ = lean_usize_land(v___x_320_, v___x_323_);
v___x_325_ = lean_array_uget_borrowed(v_buckets_308_, v___x_324_);
v___x_326_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg(v_a_307_, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg___boxed(lean_object* v_m_327_, lean_object* v_a_328_){
_start:
{
uint8_t v_res_329_; lean_object* v_r_330_; 
v_res_329_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg(v_m_327_, v_a_328_);
lean_dec_ref(v_a_328_);
lean_dec_ref(v_m_327_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__0___boxed(lean_object* v_b_331_, lean_object* v_f_332_, lean_object* v_fst_333_, lean_object* v_x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__0(v_b_331_, v_f_332_, v_fst_333_, v_x_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec_ref(v_x_334_);
lean_dec_ref(v_b_331_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1(lean_object* v_body_342_, lean_object* v_f_343_, lean_object* v_fst_344_, lean_object* v_x_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_expr_instantiate1(v_body_342_, v_x_345_);
v___x_353_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v_f_343_, v___x_352_, v_fst_344_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1___boxed(lean_object* v_body_354_, lean_object* v_f_355_, lean_object* v_fst_356_, lean_object* v_x_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1(v_body_354_, v_f_355_, v_fst_356_, v_x_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec_ref(v_x_357_);
lean_dec_ref(v_body_354_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(lean_object* v_f_367_, lean_object* v_e_368_, lean_object* v_acc_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_n_377_; lean_object* v_d_378_; lean_object* v_b_379_; uint8_t v_bi_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v_visited_393_; lean_object* v_visitedConsts_394_; uint8_t v___x_395_; 
v_visited_393_ = lean_ctor_get(v_a_370_, 0);
v_visitedConsts_394_ = lean_ctor_get(v_a_370_, 1);
v___x_395_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg(v_visited_393_, v_e_368_);
if (v___x_395_ == 0)
{
lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_541_; 
lean_inc_ref(v_visitedConsts_394_);
lean_inc_ref(v_visited_393_);
v_isSharedCheck_541_ = !lean_is_exclusive(v_a_370_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; lean_object* v_unused_543_; 
v_unused_542_ = lean_ctor_get(v_a_370_, 1);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_a_370_, 0);
lean_dec(v_unused_543_);
v___x_397_ = v_a_370_;
v_isShared_398_ = v_isSharedCheck_541_;
goto v_resetjp_396_;
}
else
{
lean_dec(v_a_370_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_541_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_box(0);
lean_inc_ref(v_e_368_);
v___x_400_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2___redArg(v_visited_393_, v_e_368_, v___x_399_);
lean_inc(v_a_374_);
lean_inc_ref(v_a_373_);
lean_inc(v_a_372_);
lean_inc_ref(v_a_371_);
lean_inc_ref(v_e_368_);
v___x_401_ = l_Lean_Meta_isProof(v_e_368_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_532_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_532_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_532_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_532_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
lean_inc_ref(v_visitedConsts_394_);
lean_inc_ref(v___x_400_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_400_);
v___x_407_ = v___x_397_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_visitedConsts_394_);
v___x_407_ = v_reuseFailAlloc_531_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
uint8_t v___x_408_; 
v___x_408_ = lean_unbox(v_a_402_);
lean_dec(v_a_402_);
if (v___x_408_ == 0)
{
switch(lean_obj_tag(v_e_368_))
{
case 7:
{
lean_object* v_binderName_409_; lean_object* v_binderType_410_; lean_object* v_body_411_; uint8_t v_binderInfo_412_; 
lean_del_object(v___x_404_);
lean_dec_ref(v___x_400_);
lean_dec_ref(v_visitedConsts_394_);
v_binderName_409_ = lean_ctor_get(v_e_368_, 0);
lean_inc(v_binderName_409_);
v_binderType_410_ = lean_ctor_get(v_e_368_, 1);
lean_inc_ref(v_binderType_410_);
v_body_411_ = lean_ctor_get(v_e_368_, 2);
lean_inc_ref(v_body_411_);
v_binderInfo_412_ = lean_ctor_get_uint8(v_e_368_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_368_);
v_n_377_ = v_binderName_409_;
v_d_378_ = v_binderType_410_;
v_b_379_ = v_body_411_;
v_bi_380_ = v_binderInfo_412_;
v___y_381_ = v___x_407_;
v___y_382_ = v_a_371_;
v___y_383_ = v_a_372_;
v___y_384_ = v_a_373_;
v___y_385_ = v_a_374_;
goto v___jp_376_;
}
case 6:
{
lean_object* v_binderName_413_; lean_object* v_binderType_414_; lean_object* v_body_415_; uint8_t v_binderInfo_416_; 
lean_del_object(v___x_404_);
lean_dec_ref(v___x_400_);
lean_dec_ref(v_visitedConsts_394_);
v_binderName_413_ = lean_ctor_get(v_e_368_, 0);
lean_inc(v_binderName_413_);
v_binderType_414_ = lean_ctor_get(v_e_368_, 1);
lean_inc_ref(v_binderType_414_);
v_body_415_ = lean_ctor_get(v_e_368_, 2);
lean_inc_ref(v_body_415_);
v_binderInfo_416_ = lean_ctor_get_uint8(v_e_368_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_368_);
v_n_377_ = v_binderName_413_;
v_d_378_ = v_binderType_414_;
v_b_379_ = v_body_415_;
v_bi_380_ = v_binderInfo_416_;
v___y_381_ = v___x_407_;
v___y_382_ = v_a_371_;
v___y_383_ = v_a_372_;
v___y_384_ = v_a_373_;
v___y_385_ = v_a_374_;
goto v___jp_376_;
}
case 10:
{
lean_object* v_expr_417_; 
lean_del_object(v___x_404_);
lean_dec_ref(v___x_400_);
lean_dec_ref(v_visitedConsts_394_);
v_expr_417_ = lean_ctor_get(v_e_368_, 1);
lean_inc_ref(v_expr_417_);
lean_dec_ref(v_e_368_);
v_e_368_ = v_expr_417_;
v_a_370_ = v___x_407_;
goto _start;
}
case 8:
{
lean_object* v_declName_419_; lean_object* v_type_420_; lean_object* v_value_421_; lean_object* v_body_422_; uint8_t v_nondep_423_; lean_object* v___x_424_; 
lean_del_object(v___x_404_);
lean_dec_ref(v___x_400_);
lean_dec_ref(v_visitedConsts_394_);
v_declName_419_ = lean_ctor_get(v_e_368_, 0);
lean_inc(v_declName_419_);
v_type_420_ = lean_ctor_get(v_e_368_, 1);
lean_inc_ref(v_type_420_);
v_value_421_ = lean_ctor_get(v_e_368_, 2);
lean_inc_ref(v_value_421_);
v_body_422_ = lean_ctor_get(v_e_368_, 3);
lean_inc_ref(v_body_422_);
v_nondep_423_ = lean_ctor_get_uint8(v_e_368_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_368_);
lean_inc(v_a_374_);
lean_inc_ref(v_a_373_);
lean_inc(v_a_372_);
lean_inc_ref(v_a_371_);
lean_inc_ref(v_type_420_);
lean_inc_ref(v_f_367_);
v___x_424_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v_f_367_, v_type_420_, v_acc_369_, v___x_407_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v_fst_426_; lean_object* v_snd_427_; lean_object* v___x_428_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref(v___x_424_);
v_fst_426_ = lean_ctor_get(v_a_425_, 0);
lean_inc(v_fst_426_);
v_snd_427_ = lean_ctor_get(v_a_425_, 1);
lean_inc(v_snd_427_);
lean_dec(v_a_425_);
lean_inc(v_a_374_);
lean_inc_ref(v_a_373_);
lean_inc(v_a_372_);
lean_inc_ref(v_a_371_);
lean_inc_ref(v_value_421_);
lean_inc_ref(v_f_367_);
v___x_428_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v_f_367_, v_value_421_, v_fst_426_, v_snd_427_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___f_432_; uint8_t v___x_433_; lean_object* v___x_434_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref(v___x_428_);
v_fst_430_ = lean_ctor_get(v_a_429_, 0);
lean_inc(v_fst_430_);
v_snd_431_ = lean_ctor_get(v_a_429_, 1);
lean_inc(v_snd_431_);
lean_dec(v_a_429_);
v___f_432_ = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_432_, 0, v_body_422_);
lean_closure_set(v___f_432_, 1, v_f_367_);
lean_closure_set(v___f_432_, 2, v_fst_430_);
v___x_433_ = 0;
v___x_434_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg(v_declName_419_, v_type_420_, v_value_421_, v___f_432_, v_nondep_423_, v___x_433_, v_snd_431_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
return v___x_434_;
}
else
{
lean_dec_ref(v_body_422_);
lean_dec_ref(v_value_421_);
lean_dec_ref(v_type_420_);
lean_dec(v_declName_419_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec_ref(v_f_367_);
return v___x_428_;
}
}
else
{
lean_dec_ref(v_body_422_);
lean_dec_ref(v_value_421_);
lean_dec_ref(v_type_420_);
lean_dec(v_declName_419_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec_ref(v_f_367_);
return v___x_424_;
}
}
case 5:
{
lean_object* v_fn_435_; lean_object* v_arg_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
lean_del_object(v___x_404_);
lean_dec_ref(v___x_400_);
lean_dec_ref(v_visitedConsts_394_);
v_fn_435_ = lean_ctor_get(v_e_368_, 0);
lean_inc_ref(v_fn_435_);
v_arg_436_ = lean_ctor_get(v_e_368_, 1);
lean_inc_ref(v_arg_436_);
lean_dec_ref(v_e_368_);
v___x_437_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___closed__0));
lean_inc(v_a_374_);
lean_inc_ref(v_a_373_);
lean_inc(v_a_372_);
lean_inc_ref(v_a_371_);
lean_inc_ref(v_fn_435_);
v___x_438_ = l_Lean_Meta_getFunInfo(v_fn_435_, v___x_437_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v_paramInfo_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref(v___x_438_);
v_paramInfo_440_ = lean_ctor_get(v_a_439_, 0);
lean_inc_ref(v_paramInfo_440_);
lean_dec(v_a_439_);
v___x_441_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_array_get(v___x_441_, v_paramInfo_440_, v___x_442_);
lean_dec_ref(v_paramInfo_440_);
v___x_444_ = l_Lean_Meta_ParamInfo_isInstImplicit(v___x_443_);
lean_dec(v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_inc(v_a_374_);
lean_inc_ref(v_a_373_);
lean_inc(v_a_372_);
lean_inc_ref(v_a_371_);
lean_inc_ref(v_f_367_);
v___x_445_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v_f_367_, v_fn_435_, v_acc_369_, v___x_407_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v_fst_447_; lean_object* v_snd_448_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref(v___x_445_);
v_fst_447_ = lean_ctor_get(v_a_446_, 0);
lean_inc(v_fst_447_);
v_snd_448_ = lean_ctor_get(v_a_446_, 1);
lean_inc(v_snd_448_);
lean_dec(v_a_446_);
v_e_368_ = v_arg_436_;
v_acc_369_ = v_fst_447_;
v_a_370_ = v_snd_448_;
goto _start;
}
else
{
lean_dec_ref(v_arg_436_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec_ref(v_f_367_);
return v___x_445_;
}
}
else
{
lean_dec_ref(v_arg_436_);
v_e_368_ = v_fn_435_;
v_a_370_ = v___x_407_;
goto _start;
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v_arg_436_);
lean_dec_ref(v_fn_435_);
lean_dec_ref(v___x_407_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_acc_369_);
lean_dec_ref(v_f_367_);
v_a_451_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_438_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_438_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
case 11:
{
lean_object* v_struct_459_; 
lean_del_object(v___x_404_);
lean_dec_ref(v___x_400_);
lean_dec_ref(v_visitedConsts_394_);
v_struct_459_ = lean_ctor_get(v_e_368_, 2);
lean_inc_ref(v_struct_459_);
lean_dec_ref(v_e_368_);
v_e_368_ = v_struct_459_;
v_a_370_ = v___x_407_;
goto _start;
}
case 4:
{
lean_object* v_declName_461_; uint8_t v___x_462_; 
v_declName_461_ = lean_ctor_get(v_e_368_, 0);
lean_inc(v_declName_461_);
lean_dec_ref(v_e_368_);
v___x_462_ = l_Lean_NameHashSet_contains(v_visitedConsts_394_, v_declName_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec_ref(v___x_407_);
lean_del_object(v___x_404_);
lean_inc(v_declName_461_);
v___x_463_ = l_Lean_NameHashSet_insert(v_visitedConsts_394_, v_declName_461_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_400_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
lean_inc(v_declName_461_);
v___x_465_ = l_Lean_isImplicitReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg(v_declName_461_, v___x_464_, v_a_374_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_510_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_510_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_510_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_510_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v_fst_470_; uint8_t v___x_471_; 
v_fst_470_ = lean_ctor_get(v_a_466_, 0);
v___x_471_ = lean_unbox(v_fst_470_);
if (v___x_471_ == 0)
{
lean_object* v_snd_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_496_; 
lean_del_object(v___x_468_);
v_snd_472_ = lean_ctor_get(v_a_466_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_a_466_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v_a_466_, 0);
lean_dec(v_unused_497_);
v___x_474_ = v_a_466_;
v_isShared_475_ = v_isSharedCheck_496_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snd_472_);
lean_dec(v_a_466_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_496_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; 
v___x_476_ = lean_apply_7(v_f_367_, v_declName_461_, v_acc_369_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, lean_box(0));
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_487_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_487_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v_a_477_);
v___x_482_ = v___x_474_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_477_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_snd_472_);
v___x_482_ = v_reuseFailAlloc_486_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_484_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_482_);
v___x_484_ = v___x_479_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_del_object(v___x_474_);
lean_dec(v_snd_472_);
v_a_488_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_476_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_476_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
else
{
lean_object* v_snd_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_508_; 
lean_dec(v_declName_461_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec_ref(v_f_367_);
v_snd_498_ = lean_ctor_get(v_a_466_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_a_466_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v_a_466_, 0);
lean_dec(v_unused_509_);
v___x_500_ = v_a_466_;
v_isShared_501_ = v_isSharedCheck_508_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snd_498_);
lean_dec(v_a_466_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_508_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v_acc_369_);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_acc_369_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_snd_498_);
v___x_503_ = v_reuseFailAlloc_507_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_505_; 
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_503_);
v___x_505_ = v___x_468_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec(v_declName_461_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_acc_369_);
lean_dec_ref(v_f_367_);
v_a_511_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_465_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_465_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_dec(v_declName_461_);
lean_dec_ref(v___x_400_);
lean_dec_ref(v_visitedConsts_394_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec_ref(v_f_367_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v_acc_369_);
lean_ctor_set(v___x_519_, 1, v___x_407_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_519_);
v___x_521_ = v___x_404_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
default: 
{
lean_object* v___x_523_; lean_object* v___x_525_; 
lean_dec_ref(v___x_400_);
lean_dec_ref(v_visitedConsts_394_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec_ref(v_e_368_);
lean_dec_ref(v_f_367_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v_acc_369_);
lean_ctor_set(v___x_523_, 1, v___x_407_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_523_);
v___x_525_ = v___x_404_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_529_; 
lean_dec_ref(v___x_400_);
lean_dec_ref(v_visitedConsts_394_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec_ref(v_e_368_);
lean_dec_ref(v_f_367_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v_acc_369_);
lean_ctor_set(v___x_527_, 1, v___x_407_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_527_);
v___x_529_ = v___x_404_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v___x_400_);
lean_del_object(v___x_397_);
lean_dec_ref(v_visitedConsts_394_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_acc_369_);
lean_dec_ref(v_e_368_);
lean_dec_ref(v_f_367_);
v_a_533_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_401_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_401_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec_ref(v_e_368_);
lean_dec_ref(v_f_367_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v_acc_369_);
lean_ctor_set(v___x_544_, 1, v_a_370_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
v___jp_376_:
{
lean_object* v___x_386_; 
lean_inc(v___y_385_);
lean_inc_ref(v___y_384_);
lean_inc(v___y_383_);
lean_inc_ref(v___y_382_);
lean_inc_ref(v_d_378_);
lean_inc_ref(v_f_367_);
v___x_386_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v_f_367_, v_d_378_, v_acc_369_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v_fst_388_; lean_object* v_snd_389_; lean_object* v___f_390_; uint8_t v___x_391_; lean_object* v___x_392_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref(v___x_386_);
v_fst_388_ = lean_ctor_get(v_a_387_, 0);
lean_inc(v_fst_388_);
v_snd_389_ = lean_ctor_get(v_a_387_, 1);
lean_inc(v_snd_389_);
lean_dec(v_a_387_);
v___f_390_ = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_390_, 0, v_b_379_);
lean_closure_set(v___f_390_, 1, v_f_367_);
lean_closure_set(v___f_390_, 2, v_fst_388_);
v___x_391_ = 0;
v___x_392_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg(v_n_377_, v_bi_380_, v_d_378_, v___f_390_, v___x_391_, v_snd_389_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
return v___x_392_;
}
else
{
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec_ref(v_b_379_);
lean_dec_ref(v_d_378_);
lean_dec(v_n_377_);
lean_dec_ref(v_f_367_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__0(lean_object* v_b_546_, lean_object* v_f_547_, lean_object* v_fst_548_, lean_object* v_x_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_expr_instantiate1(v_b_546_, v_x_549_);
v___x_557_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v_f_547_, v___x_556_, v_fst_548_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___boxed(lean_object* v_f_558_, lean_object* v_e_559_, lean_object* v_acc_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v_f_558_, v_e_559_, v_acc_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(lean_object* v_00_u03b1_568_, lean_object* v_f_569_, lean_object* v_e_570_, lean_object* v_acc_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v_f_569_, v_e_570_, v_acc_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___boxed(lean_object* v_00_u03b1_579_, lean_object* v_f_580_, lean_object* v_e_581_, lean_object* v_acc_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(v_00_u03b1_579_, v_f_580_, v_e_581_, v_acc_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
return v_res_589_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1(lean_object* v_00_u03b2_590_, lean_object* v_m_591_, lean_object* v_a_592_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg(v_m_591_, v_a_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___boxed(lean_object* v_00_u03b2_594_, lean_object* v_m_595_, lean_object* v_a_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1(v_00_u03b2_594_, v_m_595_, v_a_596_);
lean_dec_ref(v_a_596_);
lean_dec_ref(v_m_595_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2(lean_object* v_00_u03b2_599_, lean_object* v_m_600_, lean_object* v_a_601_, lean_object* v_b_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2___redArg(v_m_600_, v_a_601_, v_b_602_);
return v___x_603_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1(lean_object* v_00_u03b2_604_, lean_object* v_a_605_, lean_object* v_x_606_){
_start:
{
uint8_t v___x_607_; 
v___x_607_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg(v_a_605_, v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___boxed(lean_object* v_00_u03b2_608_, lean_object* v_a_609_, lean_object* v_x_610_){
_start:
{
uint8_t v_res_611_; lean_object* v_r_612_; 
v_res_611_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1(v_00_u03b2_608_, v_a_609_, v_x_610_);
lean_dec(v_x_610_);
lean_dec_ref(v_a_609_);
v_r_612_ = lean_box(v_res_611_);
return v_r_612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3(lean_object* v_00_u03b2_613_, lean_object* v_data_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3___redArg(v_data_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_616_, lean_object* v_i_617_, lean_object* v_source_618_, lean_object* v_target_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6___redArg(v_i_617_, v_source_618_, v_target_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_621_, lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6_spec__7___redArg(v_x_622_, v_x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___redArg(lean_object* v_f_625_, lean_object* v_e_626_, lean_object* v_acc_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v_f_625_, v_e_626_, v_acc_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___redArg___boxed(lean_object* v_f_635_, lean_object* v_e_636_, lean_object* v_acc_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___redArg(v_f_635_, v_e_636_, v_acc_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold(lean_object* v_00_u03b1_645_, lean_object* v_f_646_, lean_object* v_e_647_, lean_object* v_acc_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v_f_646_, v_e_647_, v_acc_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___boxed(lean_object* v_00_u03b1_656_, lean_object* v_f_657_, lean_object* v_e_658_, lean_object* v_acc_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold(v_00_u03b1_656_, v_f_657_, v_e_658_, v_acc_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
return v_res_666_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__0(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(64u);
v___x_668_ = l_Lean_mkPtrSet___redArg(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__1(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_box(0);
v___x_670_ = lean_unsigned_to_nat(16u);
v___x_671_ = lean_mk_array(v___x_670_, v___x_669_);
return v___x_671_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__2(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__1, &l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__1_once, _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__1);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_672_);
return v___x_674_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__2, &l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__2_once, _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__2);
v___x_676_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__0, &l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__0_once, _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__0);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v___x_675_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg(lean_object* v_e_678_, lean_object* v_init_679_, lean_object* v_f_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3, &l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3_once, _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3);
v___x_687_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v_f_680_, v_e_678_, v_init_679_, v___x_686_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_696_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_696_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_fst_692_; lean_object* v___x_694_; 
v_fst_692_ = lean_ctor_get(v_a_688_, 0);
lean_inc(v_fst_692_);
lean_dec(v_a_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v_fst_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_fst_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
v_a_697_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_687_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_687_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___boxed(lean_object* v_e_705_, lean_object* v_init_706_, lean_object* v_f_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg(v_e_705_, v_init_706_, v_f_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe(lean_object* v_00_u03b1_714_, lean_object* v_e_715_, lean_object* v_init_716_, lean_object* v_f_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3, &l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3_once, _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3);
v___x_724_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v_f_717_, v_e_715_, v_init_716_, v___x_723_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_733_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_733_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_fst_729_; lean_object* v___x_731_; 
v_fst_729_ = lean_ctor_get(v_a_725_, 0);
lean_inc(v_fst_729_);
lean_dec(v_a_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v_fst_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_fst_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
v_a_734_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_724_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_724_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___boxed(lean_object* v_00_u03b1_742_, lean_object* v_e_743_, lean_object* v_init_744_, lean_object* v_f_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe(v_00_u03b1_742_, v_e_743_, v_init_744_, v_f_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants___lam__0(lean_object* v_n_752_, lean_object* v_ns_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_array_push(v_ns_753_, v_n_752_);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants___lam__0___boxed(lean_object* v_n_761_, lean_object* v_ns_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Expr_relevantConstants___lam__0(v_n_761_, v_ns_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants(lean_object* v_e_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___f_778_ = ((lean_object*)(l_Lean_Expr_relevantConstants___closed__0));
v___x_779_ = ((lean_object*)(l_Lean_Expr_relevantConstants___closed__1));
v___x_780_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3, &l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3_once, _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3);
v___x_781_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v___f_778_, v_e_772_, v___x_779_, v___x_780_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_790_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_790_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_fst_786_; lean_object* v___x_788_; 
v_fst_786_ = lean_ctor_get(v_a_782_, 0);
lean_inc(v_fst_786_);
lean_dec(v_a_782_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v_fst_786_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_fst_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_a_791_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_781_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_781_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants___boxed(lean_object* v_e_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Expr_relevantConstants(v_e_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet___lam__0(lean_object* v_n_806_, lean_object* v_ns_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = l_Lean_NameSet_insert(v_ns_807_, v_n_806_);
v___x_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet___lam__0___boxed(lean_object* v_n_815_, lean_object* v_ns_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Expr_relevantConstantsAsSet___lam__0(v_n_815_, v_ns_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet(lean_object* v_e_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___f_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___f_830_ = ((lean_object*)(l_Lean_Expr_relevantConstantsAsSet___closed__0));
v___x_831_ = l_Lean_NameSet_empty;
v___x_832_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3, &l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3_once, _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3);
v___x_833_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(v___f_830_, v_e_824_, v___x_831_, v___x_832_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_842_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_fst_838_; lean_object* v___x_840_; 
v_fst_838_ = lean_ctor_get(v_a_834_, 0);
lean_inc(v_fst_838_);
lean_dec(v_a_834_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v_fst_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_fst_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v_a_843_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_833_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_833_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet___boxed(lean_object* v_e_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Expr_relevantConstantsAsSet(v_e_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg(lean_object* v_mvarId_858_, lean_object* v_x_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_858_, v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_a_874_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_865_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_865_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg___boxed(lean_object* v_mvarId_882_, lean_object* v_x_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg(v_mvarId_882_, v_x_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2(lean_object* v_00_u03b1_890_, lean_object* v_mvarId_891_, lean_object* v_x_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg(v_mvarId_891_, v_x_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___boxed(lean_object* v_00_u03b1_899_, lean_object* v_mvarId_900_, lean_object* v_x_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2(v_00_u03b1_899_, v_mvarId_900_, v_x_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getConstants_spec__1(lean_object* v_as_908_, size_t v_sz_909_, size_t v_i_910_, lean_object* v_b_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
uint8_t v___x_917_; 
v___x_917_ = lean_usize_dec_lt(v_i_910_, v_sz_909_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; 
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v_b_911_);
return v___x_918_;
}
else
{
lean_object* v_a_919_; lean_object* v___x_920_; 
v_a_919_ = lean_array_uget_borrowed(v_as_908_, v_i_910_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
lean_inc(v___y_913_);
lean_inc_ref(v___y_912_);
lean_inc(v_a_919_);
v___x_920_ = lean_infer_type(v_a_919_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; lean_object* v___x_923_; size_t v___x_924_; size_t v___x_925_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref(v___x_920_);
v___x_922_ = l_Lean_Expr_getUsedConstantsAsSet(v_a_921_);
v___x_923_ = l_Lean_NameSet_append(v_b_911_, v___x_922_);
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_add(v_i_910_, v___x_924_);
v_i_910_ = v___x_925_;
v_b_911_ = v___x_923_;
goto _start;
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v_b_911_);
v_a_927_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_920_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_920_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getConstants_spec__1___boxed(lean_object* v_as_935_, lean_object* v_sz_936_, lean_object* v_i_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
size_t v_sz_boxed_944_; size_t v_i_boxed_945_; lean_object* v_res_946_; 
v_sz_boxed_944_ = lean_unbox_usize(v_sz_936_);
lean_dec(v_sz_936_);
v_i_boxed_945_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getConstants_spec__1(v_as_935_, v_sz_boxed_944_, v_i_boxed_945_, v_b_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec_ref(v_as_935_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object* v_as_947_, size_t v_sz_948_, size_t v_i_949_, lean_object* v_b_950_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = lean_usize_dec_lt(v_i_949_, v_sz_948_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_b_950_);
return v___x_953_;
}
else
{
lean_object* v_snd_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_972_; 
v_snd_954_ = lean_ctor_get(v_b_950_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v_b_950_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v_b_950_, 0);
lean_dec(v_unused_973_);
v___x_956_ = v_b_950_;
v_isShared_957_ = v_isSharedCheck_972_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_snd_954_);
lean_dec(v_b_950_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_972_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v_a_960_; lean_object* v_a_967_; 
v___x_958_ = lean_box(0);
v_a_967_ = lean_array_uget_borrowed(v_as_947_, v_i_949_);
if (lean_obj_tag(v_a_967_) == 0)
{
v_a_960_ = v_snd_954_;
goto v___jp_959_;
}
else
{
lean_object* v_val_968_; uint8_t v___x_969_; 
v_val_968_ = lean_ctor_get(v_a_967_, 0);
v___x_969_ = l_Lean_LocalDecl_isImplementationDetail(v_val_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; 
lean_inc(v_val_968_);
v___x_970_ = l_Lean_LocalDecl_toExpr(v_val_968_);
v___x_971_ = lean_array_push(v_snd_954_, v___x_970_);
v_a_960_ = v___x_971_;
goto v___jp_959_;
}
else
{
v_a_960_ = v_snd_954_;
goto v___jp_959_;
}
}
v___jp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v_a_960_);
lean_ctor_set(v___x_956_, 0, v___x_958_);
v___x_962_ = v___x_956_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_a_960_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
size_t v___x_963_; size_t v___x_964_; 
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_add(v_i_949_, v___x_963_);
v_i_949_ = v___x_964_;
v_b_950_ = v___x_962_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_as_974_, lean_object* v_sz_975_, lean_object* v_i_976_, lean_object* v_b_977_, lean_object* v___y_978_){
_start:
{
size_t v_sz_boxed_979_; size_t v_i_boxed_980_; lean_object* v_res_981_; 
v_sz_boxed_979_ = lean_unbox_usize(v_sz_975_);
lean_dec(v_sz_975_);
v_i_boxed_980_ = lean_unbox_usize(v_i_976_);
lean_dec(v_i_976_);
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_as_974_, v_sz_boxed_979_, v_i_boxed_980_, v_b_977_);
lean_dec_ref(v_as_974_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5(lean_object* v_as_982_, size_t v_sz_983_, size_t v_i_984_, lean_object* v_b_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = lean_usize_dec_lt(v_i_984_, v_sz_983_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_b_985_);
return v___x_992_;
}
else
{
lean_object* v_snd_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1011_; 
v_snd_993_ = lean_ctor_get(v_b_985_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_b_985_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v_b_985_, 0);
lean_dec(v_unused_1012_);
v___x_995_ = v_b_985_;
v_isShared_996_ = v_isSharedCheck_1011_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_snd_993_);
lean_dec(v_b_985_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1011_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v_a_999_; lean_object* v_a_1006_; 
v___x_997_ = lean_box(0);
v_a_1006_ = lean_array_uget_borrowed(v_as_982_, v_i_984_);
if (lean_obj_tag(v_a_1006_) == 0)
{
v_a_999_ = v_snd_993_;
goto v___jp_998_;
}
else
{
lean_object* v_val_1007_; uint8_t v___x_1008_; 
v_val_1007_ = lean_ctor_get(v_a_1006_, 0);
v___x_1008_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_inc(v_val_1007_);
v___x_1009_ = l_Lean_LocalDecl_toExpr(v_val_1007_);
v___x_1010_ = lean_array_push(v_snd_993_, v___x_1009_);
v_a_999_ = v___x_1010_;
goto v___jp_998_;
}
else
{
v_a_999_ = v_snd_993_;
goto v___jp_998_;
}
}
v___jp_998_:
{
lean_object* v___x_1001_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v_a_999_);
lean_ctor_set(v___x_995_, 0, v___x_997_);
v___x_1001_ = v___x_995_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_a_999_);
v___x_1001_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
size_t v___x_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_add(v_i_984_, v___x_1002_);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_as_982_, v_sz_983_, v___x_1003_, v___x_1001_);
return v___x_1004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_as_1013_, lean_object* v_sz_1014_, lean_object* v_i_1015_, lean_object* v_b_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
size_t v_sz_boxed_1022_; size_t v_i_boxed_1023_; lean_object* v_res_1024_; 
v_sz_boxed_1022_ = lean_unbox_usize(v_sz_1014_);
lean_dec(v_sz_1014_);
v_i_boxed_1023_ = lean_unbox_usize(v_i_1015_);
lean_dec(v_i_1015_);
v_res_1024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5(v_as_1013_, v_sz_boxed_1022_, v_i_boxed_1023_, v_b_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_as_1013_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2(lean_object* v_inh_1025_, lean_object* v_n_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
if (lean_obj_tag(v_n_1026_) == 0)
{
lean_object* v_cs_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1067_; 
v_cs_1033_ = lean_ctor_get(v_n_1026_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_n_1026_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1035_ = v_n_1026_;
v_isShared_1036_ = v_isSharedCheck_1067_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_cs_1033_);
lean_dec(v_n_1026_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1067_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; size_t v_sz_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v_b_1027_);
v_sz_1039_ = lean_array_size(v_cs_1033_);
v___x_1040_ = ((size_t)0ULL);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4(v_inh_1025_, v_cs_1033_, v_sz_1039_, v___x_1040_, v___x_1038_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec_ref(v_cs_1033_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1058_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1058_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1058_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_fst_1046_; 
v_fst_1046_ = lean_ctor_get(v_a_1042_, 0);
if (lean_obj_tag(v_fst_1046_) == 0)
{
lean_object* v_snd_1047_; lean_object* v___x_1049_; 
v_snd_1047_ = lean_ctor_get(v_a_1042_, 1);
lean_inc(v_snd_1047_);
lean_dec(v_a_1042_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set_tag(v___x_1035_, 1);
lean_ctor_set(v___x_1035_, 0, v_snd_1047_);
v___x_1049_ = v___x_1035_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_snd_1047_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1049_);
v___x_1051_ = v___x_1044_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
else
{
lean_object* v_val_1054_; lean_object* v___x_1056_; 
lean_inc_ref(v_fst_1046_);
lean_dec(v_a_1042_);
lean_del_object(v___x_1035_);
v_val_1054_ = lean_ctor_get(v_fst_1046_, 0);
lean_inc(v_val_1054_);
lean_dec_ref(v_fst_1046_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v_val_1054_);
v___x_1056_ = v___x_1044_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_val_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_del_object(v___x_1035_);
v_a_1059_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1041_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1041_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
else
{
lean_object* v_vs_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1102_; 
v_vs_1068_ = lean_ctor_get(v_n_1026_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_n_1026_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1070_ = v_n_1026_;
v_isShared_1071_ = v_isSharedCheck_1102_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_vs_1068_);
lean_dec(v_n_1026_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1102_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; size_t v_sz_1074_; size_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v_b_1027_);
v_sz_1074_ = lean_array_size(v_vs_1068_);
v___x_1075_ = ((size_t)0ULL);
v___x_1076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5(v_vs_1068_, v_sz_1074_, v___x_1075_, v___x_1073_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec_ref(v_vs_1068_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1093_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1093_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1093_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_fst_1081_; 
v_fst_1081_ = lean_ctor_get(v_a_1077_, 0);
if (lean_obj_tag(v_fst_1081_) == 0)
{
lean_object* v_snd_1082_; lean_object* v___x_1084_; 
v_snd_1082_ = lean_ctor_get(v_a_1077_, 1);
lean_inc(v_snd_1082_);
lean_dec(v_a_1077_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v_snd_1082_);
v___x_1084_ = v___x_1070_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_snd_1082_);
v___x_1084_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1086_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1084_);
v___x_1086_ = v___x_1079_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
else
{
lean_object* v_val_1089_; lean_object* v___x_1091_; 
lean_inc_ref(v_fst_1081_);
lean_dec(v_a_1077_);
lean_del_object(v___x_1070_);
v_val_1089_ = lean_ctor_get(v_fst_1081_, 0);
lean_inc(v_val_1089_);
lean_dec_ref(v_fst_1081_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v_val_1089_);
v___x_1091_ = v___x_1079_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_val_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_del_object(v___x_1070_);
v_a_1094_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1076_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1076_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4(lean_object* v_inh_1103_, lean_object* v_as_1104_, size_t v_sz_1105_, size_t v_i_1106_, lean_object* v_b_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_usize_dec_lt(v_i_1106_, v_sz_1105_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v_b_1107_);
return v___x_1114_;
}
else
{
lean_object* v_snd_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1149_; 
v_snd_1115_ = lean_ctor_get(v_b_1107_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_b_1107_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v_b_1107_, 0);
lean_dec(v_unused_1150_);
v___x_1117_ = v_b_1107_;
v_isShared_1118_ = v_isSharedCheck_1149_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_snd_1115_);
lean_dec(v_b_1107_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1149_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v_a_1119_; lean_object* v___x_1120_; 
v_a_1119_ = lean_array_uget_borrowed(v_as_1104_, v_i_1106_);
lean_inc(v_snd_1115_);
lean_inc(v_a_1119_);
v___x_1120_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2(v_inh_1103_, v_a_1119_, v_snd_1115_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1140_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1140_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1140_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
if (lean_obj_tag(v_a_1121_) == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_a_1121_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1125_);
v___x_1127_ = v___x_1117_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_snd_1115_);
v___x_1127_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1129_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1127_);
v___x_1129_ = v___x_1123_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
lean_del_object(v___x_1123_);
lean_dec(v_snd_1115_);
v_a_1132_ = lean_ctor_get(v_a_1121_, 0);
lean_inc(v_a_1132_);
lean_dec_ref(v_a_1121_);
v___x_1133_ = lean_box(0);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 1, v_a_1132_);
lean_ctor_set(v___x_1117_, 0, v___x_1133_);
v___x_1135_ = v___x_1117_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_a_1132_);
v___x_1135_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
size_t v___x_1136_; size_t v___x_1137_; 
v___x_1136_ = ((size_t)1ULL);
v___x_1137_ = lean_usize_add(v_i_1106_, v___x_1136_);
v_i_1106_ = v___x_1137_;
v_b_1107_ = v___x_1135_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_del_object(v___x_1117_);
lean_dec(v_snd_1115_);
v_a_1141_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1120_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1120_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_inh_1151_, lean_object* v_as_1152_, lean_object* v_sz_1153_, lean_object* v_i_1154_, lean_object* v_b_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
size_t v_sz_boxed_1161_; size_t v_i_boxed_1162_; lean_object* v_res_1163_; 
v_sz_boxed_1161_ = lean_unbox_usize(v_sz_1153_);
lean_dec(v_sz_1153_);
v_i_boxed_1162_ = lean_unbox_usize(v_i_1154_);
lean_dec(v_i_1154_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4(v_inh_1151_, v_as_1152_, v_sz_boxed_1161_, v_i_boxed_1162_, v_b_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec_ref(v_as_1152_);
lean_dec_ref(v_inh_1151_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2___boxed(lean_object* v_inh_1164_, lean_object* v_n_1165_, lean_object* v_b_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2(v_inh_1164_, v_n_1165_, v_b_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v_inh_1164_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_as_1173_, size_t v_sz_1174_, size_t v_i_1175_, lean_object* v_b_1176_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_usize_dec_lt(v_i_1175_, v_sz_1174_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_b_1176_);
return v___x_1179_;
}
else
{
lean_object* v_snd_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1198_; 
v_snd_1180_ = lean_ctor_get(v_b_1176_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_b_1176_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v_b_1176_, 0);
lean_dec(v_unused_1199_);
v___x_1182_ = v_b_1176_;
v_isShared_1183_ = v_isSharedCheck_1198_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snd_1180_);
lean_dec(v_b_1176_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1198_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v_a_1186_; lean_object* v_a_1193_; 
v___x_1184_ = lean_box(0);
v_a_1193_ = lean_array_uget_borrowed(v_as_1173_, v_i_1175_);
if (lean_obj_tag(v_a_1193_) == 0)
{
v_a_1186_ = v_snd_1180_;
goto v___jp_1185_;
}
else
{
lean_object* v_val_1194_; uint8_t v___x_1195_; 
v_val_1194_ = lean_ctor_get(v_a_1193_, 0);
v___x_1195_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_inc(v_val_1194_);
v___x_1196_ = l_Lean_LocalDecl_toExpr(v_val_1194_);
v___x_1197_ = lean_array_push(v_snd_1180_, v___x_1196_);
v_a_1186_ = v___x_1197_;
goto v___jp_1185_;
}
else
{
v_a_1186_ = v_snd_1180_;
goto v___jp_1185_;
}
}
v___jp_1185_:
{
lean_object* v___x_1188_; 
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v_a_1186_);
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1188_ = v___x_1182_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_a_1186_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
size_t v___x_1189_; size_t v___x_1190_; 
v___x_1189_ = ((size_t)1ULL);
v___x_1190_ = lean_usize_add(v_i_1175_, v___x_1189_);
v_i_1175_ = v___x_1190_;
v_b_1176_ = v___x_1188_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* v_as_1200_, lean_object* v_sz_1201_, lean_object* v_i_1202_, lean_object* v_b_1203_, lean_object* v___y_1204_){
_start:
{
size_t v_sz_boxed_1205_; size_t v_i_boxed_1206_; lean_object* v_res_1207_; 
v_sz_boxed_1205_ = lean_unbox_usize(v_sz_1201_);
lean_dec(v_sz_1201_);
v_i_boxed_1206_ = lean_unbox_usize(v_i_1202_);
lean_dec(v_i_1202_);
v_res_1207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg(v_as_1200_, v_sz_boxed_1205_, v_i_boxed_1206_, v_b_1203_);
lean_dec_ref(v_as_1200_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3(lean_object* v_as_1208_, size_t v_sz_1209_, size_t v_i_1210_, lean_object* v_b_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_usize_dec_lt(v_i_1210_, v_sz_1209_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_b_1211_);
return v___x_1218_;
}
else
{
lean_object* v_snd_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1237_; 
v_snd_1219_ = lean_ctor_get(v_b_1211_, 1);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_b_1211_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v_b_1211_, 0);
lean_dec(v_unused_1238_);
v___x_1221_ = v_b_1211_;
v_isShared_1222_ = v_isSharedCheck_1237_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_snd_1219_);
lean_dec(v_b_1211_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1237_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v_a_1225_; lean_object* v_a_1232_; 
v___x_1223_ = lean_box(0);
v_a_1232_ = lean_array_uget_borrowed(v_as_1208_, v_i_1210_);
if (lean_obj_tag(v_a_1232_) == 0)
{
v_a_1225_ = v_snd_1219_;
goto v___jp_1224_;
}
else
{
lean_object* v_val_1233_; uint8_t v___x_1234_; 
v_val_1233_ = lean_ctor_get(v_a_1232_, 0);
v___x_1234_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_inc(v_val_1233_);
v___x_1235_ = l_Lean_LocalDecl_toExpr(v_val_1233_);
v___x_1236_ = lean_array_push(v_snd_1219_, v___x_1235_);
v_a_1225_ = v___x_1236_;
goto v___jp_1224_;
}
else
{
v_a_1225_ = v_snd_1219_;
goto v___jp_1224_;
}
}
v___jp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v_a_1225_);
lean_ctor_set(v___x_1221_, 0, v___x_1223_);
v___x_1227_ = v___x_1221_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_a_1225_);
v___x_1227_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_add(v_i_1210_, v___x_1228_);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg(v_as_1208_, v_sz_1209_, v___x_1229_, v___x_1227_);
return v___x_1230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3___boxed(lean_object* v_as_1239_, lean_object* v_sz_1240_, lean_object* v_i_1241_, lean_object* v_b_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
size_t v_sz_boxed_1248_; size_t v_i_boxed_1249_; lean_object* v_res_1250_; 
v_sz_boxed_1248_ = lean_unbox_usize(v_sz_1240_);
lean_dec(v_sz_1240_);
v_i_boxed_1249_ = lean_unbox_usize(v_i_1241_);
lean_dec(v_i_1241_);
v_res_1250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3(v_as_1239_, v_sz_boxed_1248_, v_i_boxed_1249_, v_b_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v_as_1239_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0(lean_object* v_t_1251_, lean_object* v_init_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_root_1258_; lean_object* v_tail_1259_; lean_object* v___x_1260_; 
v_root_1258_ = lean_ctor_get(v_t_1251_, 0);
lean_inc_ref(v_root_1258_);
v_tail_1259_ = lean_ctor_get(v_t_1251_, 1);
lean_inc_ref(v_tail_1259_);
lean_dec_ref(v_t_1251_);
lean_inc_ref(v_init_1252_);
v___x_1260_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2(v_init_1252_, v_root_1258_, v_init_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec_ref(v_init_1252_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1297_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1297_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1297_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
if (lean_obj_tag(v_a_1261_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; 
lean_dec_ref(v_tail_1259_);
v_a_1265_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_a_1265_);
lean_dec_ref(v_a_1261_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v_a_1265_);
v___x_1267_ = v___x_1263_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; size_t v_sz_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
lean_del_object(v___x_1263_);
v_a_1269_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_a_1269_);
lean_dec_ref(v_a_1261_);
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v_a_1269_);
v_sz_1272_ = lean_array_size(v_tail_1259_);
v___x_1273_ = ((size_t)0ULL);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3(v_tail_1259_, v_sz_1272_, v___x_1273_, v___x_1271_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec_ref(v_tail_1259_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1288_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1288_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1288_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v_fst_1279_; 
v_fst_1279_ = lean_ctor_get(v_a_1275_, 0);
if (lean_obj_tag(v_fst_1279_) == 0)
{
lean_object* v_snd_1280_; lean_object* v___x_1282_; 
v_snd_1280_ = lean_ctor_get(v_a_1275_, 1);
lean_inc(v_snd_1280_);
lean_dec(v_a_1275_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v_snd_1280_);
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_snd_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
else
{
lean_object* v_val_1284_; lean_object* v___x_1286_; 
lean_inc_ref(v_fst_1279_);
lean_dec(v_a_1275_);
v_val_1284_ = lean_ctor_get(v_fst_1279_, 0);
lean_inc(v_val_1284_);
lean_dec_ref(v_fst_1279_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v_val_1284_);
v___x_1286_ = v___x_1277_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_val_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1274_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1274_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec_ref(v_tail_1259_);
v_a_1298_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1260_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1260_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0___boxed(lean_object* v_t_1306_, lean_object* v_init_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0(v_t_1306_, v_init_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0(lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_lctx_1321_; lean_object* v_decls_1322_; lean_object* v_hs_1323_; lean_object* v___x_1324_; 
v_lctx_1321_ = lean_ctor_get(v___y_1316_, 2);
v_decls_1322_ = lean_ctor_get(v_lctx_1321_, 1);
lean_inc_ref(v_decls_1322_);
v_hs_1323_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___closed__0));
v___x_1324_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0(v_decls_1322_, v_hs_1323_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec_ref(v___y_1316_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___boxed(lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0(v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants___lam__0(lean_object* v_g_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_MVarId_getType(v_g_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1339_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1337_);
lean_inc_ref(v___y_1332_);
v___x_1339_ = l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0(v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; size_t v_sz_1342_; size_t v___x_1343_; lean_object* v___x_1344_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = l_Lean_Expr_getUsedConstantsAsSet(v_a_1338_);
v_sz_1342_ = lean_array_size(v_a_1340_);
v___x_1343_ = ((size_t)0ULL);
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getConstants_spec__1(v_a_1340_, v_sz_1342_, v___x_1343_, v___x_1341_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v_a_1340_);
return v___x_1344_;
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v_a_1338_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
v_a_1345_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1339_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1339_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
v_a_1353_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1337_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1337_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants___lam__0___boxed(lean_object* v_g_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_MVarId_getConstants___lam__0(v_g_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants(lean_object* v_g_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v___f_1374_; lean_object* v___x_1375_; 
lean_inc(v_g_1368_);
v___f_1374_ = lean_alloc_closure((void*)(l_Lean_MVarId_getConstants___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1374_, 0, v_g_1368_);
v___x_1375_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg(v_g_1368_, v___f_1374_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants___boxed(lean_object* v_g_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_MVarId_getConstants(v_g_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7(lean_object* v_as_1383_, size_t v_sz_1384_, size_t v_i_1385_, lean_object* v_b_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg(v_as_1383_, v_sz_1384_, v_i_1385_, v_b_1386_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_as_1393_, lean_object* v_sz_1394_, lean_object* v_i_1395_, lean_object* v_b_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
size_t v_sz_boxed_1402_; size_t v_i_boxed_1403_; lean_object* v_res_1404_; 
v_sz_boxed_1402_ = lean_unbox_usize(v_sz_1394_);
lean_dec(v_sz_1394_);
v_i_boxed_1403_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_res_1404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7(v_as_1393_, v_sz_boxed_1402_, v_i_boxed_1403_, v_b_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec_ref(v_as_1393_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_as_1405_, size_t v_sz_1406_, size_t v_i_1407_, lean_object* v_b_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_as_1405_, v_sz_1406_, v_i_1407_, v_b_1408_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* v_as_1415_, lean_object* v_sz_1416_, lean_object* v_i_1417_, lean_object* v_b_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
size_t v_sz_boxed_1424_; size_t v_i_boxed_1425_; lean_object* v_res_1426_; 
v_sz_boxed_1424_ = lean_unbox_usize(v_sz_1416_);
lean_dec(v_sz_1416_);
v_i_boxed_1425_ = lean_unbox_usize(v_i_1417_);
lean_dec(v_i_1417_);
v_res_1426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6(v_as_1415_, v_sz_boxed_1424_, v_i_boxed_1425_, v_b_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec_ref(v_as_1415_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getRelevantConstants_spec__0(lean_object* v_as_1427_, size_t v_sz_1428_, size_t v_i_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_usize_dec_lt(v_i_1429_, v_sz_1428_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_b_1430_);
return v___x_1437_;
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1439_; 
v_a_1438_ = lean_array_uget_borrowed(v_as_1427_, v_i_1429_);
lean_inc(v___y_1434_);
lean_inc_ref(v___y_1433_);
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1431_);
lean_inc(v_a_1438_);
v___x_1439_ = lean_infer_type(v_a_1438_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1441_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref(v___x_1439_);
lean_inc(v___y_1434_);
lean_inc_ref(v___y_1433_);
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1431_);
v___x_1441_ = l_Lean_Expr_relevantConstantsAsSet(v_a_1440_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1443_; size_t v___x_1444_; size_t v___x_1445_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref(v___x_1441_);
v___x_1443_ = l_Lean_NameSet_append(v_b_1430_, v_a_1442_);
v___x_1444_ = ((size_t)1ULL);
v___x_1445_ = lean_usize_add(v_i_1429_, v___x_1444_);
v_i_1429_ = v___x_1445_;
v_b_1430_ = v___x_1443_;
goto _start;
}
else
{
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v_b_1430_);
return v___x_1441_;
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v_b_1430_);
v_a_1447_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1439_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1439_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getRelevantConstants_spec__0___boxed(lean_object* v_as_1455_, lean_object* v_sz_1456_, lean_object* v_i_1457_, lean_object* v_b_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
size_t v_sz_boxed_1464_; size_t v_i_boxed_1465_; lean_object* v_res_1466_; 
v_sz_boxed_1464_ = lean_unbox_usize(v_sz_1456_);
lean_dec(v_sz_1456_);
v_i_boxed_1465_ = lean_unbox_usize(v_i_1457_);
lean_dec(v_i_1457_);
v_res_1466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getRelevantConstants_spec__0(v_as_1455_, v_sz_boxed_1464_, v_i_boxed_1465_, v_b_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec_ref(v_as_1455_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants___lam__0(lean_object* v_g_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_MVarId_getType(v_g_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v___x_1473_);
lean_inc(v___y_1471_);
lean_inc_ref(v___y_1470_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
v___x_1475_ = l_Lean_Expr_relevantConstantsAsSet(v_a_1474_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref(v___x_1475_);
lean_inc_ref(v___y_1468_);
v___x_1477_ = l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0(v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; size_t v_sz_1479_; size_t v___x_1480_; lean_object* v___x_1481_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref(v___x_1477_);
v_sz_1479_ = lean_array_size(v_a_1478_);
v___x_1480_ = ((size_t)0ULL);
v___x_1481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getRelevantConstants_spec__0(v_a_1478_, v_sz_1479_, v___x_1480_, v_a_1476_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v_a_1478_);
return v___x_1481_;
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_a_1476_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
v_a_1482_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1477_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1477_);
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
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
return v___x_1475_;
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
v_a_1490_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1473_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1473_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants___lam__0___boxed(lean_object* v_g_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_MVarId_getRelevantConstants___lam__0(v_g_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants(lean_object* v_g_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v___f_1511_; lean_object* v___x_1512_; 
lean_inc(v_g_1505_);
v___f_1511_ = lean_alloc_closure((void*)(l_Lean_MVarId_getRelevantConstants___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1511_, 0, v_g_1505_);
v___x_1512_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg(v_g_1505_, v___f_1511_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants___boxed(lean_object* v_g_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_MVarId_getRelevantConstants(v_g_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_ppSelector(lean_object* v_selector_1520_, lean_object* v_g_1521_, lean_object* v_c_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; 
lean_inc(v_a_1526_);
lean_inc_ref(v_a_1525_);
lean_inc(v_a_1524_);
lean_inc_ref(v_a_1523_);
v___x_1528_ = l_Lean_Meta_ppGoal(v_g_1521_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref(v___x_1528_);
v___x_1530_ = l_Std_Format_defWidth;
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = l_Std_Format_pretty(v_a_1529_, v___x_1530_, v___x_1531_, v___x_1531_);
v___x_1533_ = lean_apply_7(v_selector_1520_, v___x_1532_, v_c_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, lean_box(0));
return v___x_1533_;
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec_ref(v_c_1522_);
lean_dec_ref(v_selector_1520_);
v_a_1534_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1528_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1528_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_ppSelector___boxed(lean_object* v_selector_1542_, lean_object* v_g_1543_, lean_object* v_c_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_LibrarySuggestions_ppSelector(v_selector_1542_, v_g_1543_, v_c_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
lean_dec(v_g_1543_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___lam__0(lean_object* v_x_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = 1;
v___x_1558_ = lean_box(v___x_1557_);
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___lam__0___boxed(lean_object* v_x_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_LibrarySuggestions_Selector_postFilter___lam__0(v_x_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v_x_1560_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0(lean_object* v_c_1567_, lean_object* v_as_1568_, size_t v_i_1569_, size_t v_stop_1570_, lean_object* v_b_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_usize_dec_eq(v_i_1569_, v_stop_1570_);
if (v___x_1577_ == 0)
{
lean_object* v_filter_1578_; lean_object* v___x_1579_; lean_object* v_name_1580_; lean_object* v___x_1581_; 
v_filter_1578_ = lean_ctor_get(v_c_1567_, 2);
v___x_1579_ = lean_array_uget_borrowed(v_as_1568_, v_i_1569_);
v_name_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc_ref(v_filter_1578_);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
lean_inc(v___y_1573_);
lean_inc_ref(v___y_1572_);
lean_inc(v_name_1580_);
v___x_1581_ = lean_apply_6(v_filter_1578_, v_name_1580_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, lean_box(0));
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v_a_1584_; uint8_t v___x_1588_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref(v___x_1581_);
v___x_1588_ = lean_unbox(v_a_1582_);
lean_dec(v_a_1582_);
if (v___x_1588_ == 0)
{
v_a_1584_ = v_b_1571_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1589_; 
lean_inc(v___x_1579_);
v___x_1589_ = lean_array_push(v_b_1571_, v___x_1579_);
v_a_1584_ = v___x_1589_;
goto v___jp_1583_;
}
v___jp_1583_:
{
size_t v___x_1585_; size_t v___x_1586_; 
v___x_1585_ = ((size_t)1ULL);
v___x_1586_ = lean_usize_add(v_i_1569_, v___x_1585_);
v_i_1569_ = v___x_1586_;
v_b_1571_ = v_a_1584_;
goto _start;
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_b_1571_);
lean_dec_ref(v_c_1567_);
v_a_1590_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1581_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1581_);
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
else
{
lean_object* v___x_1598_; 
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_c_1567_);
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v_b_1571_);
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0___boxed(lean_object* v_c_1599_, lean_object* v_as_1600_, lean_object* v_i_1601_, lean_object* v_stop_1602_, lean_object* v_b_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
size_t v_i_boxed_1609_; size_t v_stop_boxed_1610_; lean_object* v_res_1611_; 
v_i_boxed_1609_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_stop_boxed_1610_ = lean_unbox_usize(v_stop_1602_);
lean_dec(v_stop_1602_);
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0(v_c_1599_, v_as_1600_, v_i_boxed_1609_, v_stop_boxed_1610_, v_b_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec_ref(v_as_1600_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter(lean_object* v_selector_1615_, lean_object* v_g_1616_, lean_object* v_c_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_maxSuggestions_1623_; lean_object* v_caller_1624_; lean_object* v_hint_1625_; lean_object* v___f_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_maxSuggestions_1623_ = lean_ctor_get(v_c_1617_, 0);
v_caller_1624_ = lean_ctor_get(v_c_1617_, 1);
v_hint_1625_ = lean_ctor_get(v_c_1617_, 3);
v___f_1626_ = ((lean_object*)(l_Lean_LibrarySuggestions_Selector_postFilter___closed__0));
lean_inc(v_hint_1625_);
lean_inc(v_caller_1624_);
lean_inc(v_maxSuggestions_1623_);
v___x_1627_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1627_, 0, v_maxSuggestions_1623_);
lean_ctor_set(v___x_1627_, 1, v_caller_1624_);
lean_ctor_set(v___x_1627_, 2, v___f_1626_);
lean_ctor_set(v___x_1627_, 3, v_hint_1625_);
lean_inc(v_a_1621_);
lean_inc_ref(v_a_1620_);
lean_inc(v_a_1619_);
lean_inc_ref(v_a_1618_);
v___x_1628_ = lean_apply_7(v_selector_1615_, v_g_1616_, v___x_1627_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, lean_box(0));
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1650_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1650_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1650_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = lean_array_get_size(v_a_1629_);
v___x_1635_ = ((lean_object*)(l_Lean_LibrarySuggestions_Selector_postFilter___closed__1));
v___x_1636_ = lean_nat_dec_lt(v___x_1633_, v___x_1634_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1638_; 
lean_dec(v_a_1629_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec_ref(v_c_1617_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1635_);
v___x_1638_ = v___x_1631_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1635_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
else
{
uint8_t v___x_1640_; 
v___x_1640_ = lean_nat_dec_le(v___x_1634_, v___x_1634_);
if (v___x_1640_ == 0)
{
if (v___x_1636_ == 0)
{
lean_object* v___x_1642_; 
lean_dec(v_a_1629_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec_ref(v_c_1617_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1635_);
v___x_1642_ = v___x_1631_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1635_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
else
{
size_t v___x_1644_; size_t v___x_1645_; lean_object* v___x_1646_; 
lean_del_object(v___x_1631_);
v___x_1644_ = ((size_t)0ULL);
v___x_1645_ = lean_usize_of_nat(v___x_1634_);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0(v_c_1617_, v_a_1629_, v___x_1644_, v___x_1645_, v___x_1635_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1629_);
return v___x_1646_;
}
}
else
{
size_t v___x_1647_; size_t v___x_1648_; lean_object* v___x_1649_; 
lean_del_object(v___x_1631_);
v___x_1647_ = ((size_t)0ULL);
v___x_1648_ = lean_usize_of_nat(v___x_1634_);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0(v_c_1617_, v_a_1629_, v___x_1647_, v___x_1648_, v___x_1635_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1629_);
return v___x_1649_;
}
}
}
}
else
{
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec_ref(v_c_1617_);
return v___x_1628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___boxed(lean_object* v_selector_1651_, lean_object* v_g_1652_, lean_object* v_c_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_LibrarySuggestions_Selector_postFilter(v_selector_1651_, v_g_1652_, v_c_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_maxSuggestions(lean_object* v_selector_1660_, lean_object* v_g_1661_, lean_object* v_c_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1668_; 
lean_inc_ref(v_c_1662_);
v___x_1668_ = lean_apply_7(v_selector_1660_, v_g_1661_, v_c_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, lean_box(0));
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1679_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1679_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1679_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v_maxSuggestions_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v_maxSuggestions_1673_ = lean_ctor_get(v_c_1662_, 0);
lean_inc(v_maxSuggestions_1673_);
lean_dec_ref(v_c_1662_);
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = l_Array_extract___redArg(v_a_1669_, v___x_1674_, v_maxSuggestions_1673_);
lean_dec(v_a_1669_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1675_);
v___x_1677_ = v___x_1671_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
lean_dec_ref(v_c_1662_);
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_maxSuggestions___boxed(lean_object* v_selector_1680_, lean_object* v_g_1681_, lean_object* v_c_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_LibrarySuggestions_Selector_maxSuggestions(v_selector_1680_, v_g_1681_, v_c_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
return v_res_1688_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___lam__0(lean_object* v_s_u2081_1689_, lean_object* v_s_u2082_1690_){
_start:
{
double v_score_1691_; double v_score_1692_; uint8_t v___x_1693_; 
v_score_1691_ = lean_ctor_get_float(v_s_u2082_1690_, sizeof(void*)*2);
v_score_1692_ = lean_ctor_get_float(v_s_u2081_1689_, sizeof(void*)*2);
v___x_1693_ = lean_float_decLt(v_score_1691_, v_score_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___lam__0___boxed(lean_object* v_s_u2081_1694_, lean_object* v_s_u2082_1695_){
_start:
{
uint8_t v_res_1696_; lean_object* v_r_1697_; 
v_res_1696_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___lam__0(v_s_u2081_1694_, v_s_u2082_1695_);
lean_dec_ref(v_s_u2082_1695_);
lean_dec_ref(v_s_u2081_1694_);
v_r_1697_ = lean_box(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg(lean_object* v_as_1699_, lean_object* v_lo_1700_, lean_object* v_hi_1701_){
_start:
{
uint8_t v___x_1702_; 
v___x_1702_ = lean_nat_dec_lt(v_lo_1700_, v_hi_1701_);
if (v___x_1702_ == 0)
{
lean_dec(v_lo_1700_);
return v_as_1699_;
}
else
{
lean_object* v___f_1703_; lean_object* v___x_1704_; lean_object* v_fst_1705_; lean_object* v_snd_1706_; uint8_t v___x_1707_; 
v___f_1703_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___closed__0));
lean_inc(v_lo_1700_);
v___x_1704_ = l_Array_qpartition___redArg(v_as_1699_, v___f_1703_, v_lo_1700_, v_hi_1701_);
v_fst_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_fst_1705_);
v_snd_1706_ = lean_ctor_get(v___x_1704_, 1);
lean_inc(v_snd_1706_);
lean_dec_ref(v___x_1704_);
v___x_1707_ = lean_nat_dec_le(v_hi_1701_, v_fst_1705_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg(v_snd_1706_, v_lo_1700_, v_fst_1705_);
v___x_1709_ = lean_unsigned_to_nat(1u);
v___x_1710_ = lean_nat_add(v_fst_1705_, v___x_1709_);
lean_dec(v_fst_1705_);
v_as_1699_ = v___x_1708_;
v_lo_1700_ = v___x_1710_;
goto _start;
}
else
{
lean_dec(v_fst_1705_);
lean_dec(v_lo_1700_);
return v_snd_1706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___boxed(lean_object* v_as_1712_, lean_object* v_lo_1713_, lean_object* v_hi_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg(v_as_1712_, v_lo_1713_, v_hi_1714_);
lean_dec(v_hi_1714_);
return v_res_1715_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1716_; uint64_t v___x_1717_; 
v___x_1716_ = lean_unsigned_to_nat(1723u);
v___x_1717_ = lean_uint64_of_nat(v___x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_x_1718_, lean_object* v_x_1719_){
_start:
{
if (lean_obj_tag(v_x_1719_) == 0)
{
return v_x_1718_;
}
else
{
lean_object* v_key_1720_; lean_object* v_value_1721_; lean_object* v_tail_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1759_; 
v_key_1720_ = lean_ctor_get(v_x_1719_, 0);
v_value_1721_ = lean_ctor_get(v_x_1719_, 1);
v_tail_1722_ = lean_ctor_get(v_x_1719_, 2);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_x_1719_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1724_ = v_x_1719_;
v_isShared_1725_ = v_isSharedCheck_1759_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_tail_1722_);
lean_inc(v_value_1721_);
lean_inc(v_key_1720_);
lean_dec(v_x_1719_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1759_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_fst_1726_; lean_object* v_snd_1727_; lean_object* v___x_1728_; uint64_t v___y_1730_; uint64_t v___y_1731_; uint64_t v___y_1751_; 
v_fst_1726_ = lean_ctor_get(v_key_1720_, 0);
v_snd_1727_ = lean_ctor_get(v_key_1720_, 1);
v___x_1728_ = lean_array_get_size(v_x_1718_);
if (lean_obj_tag(v_fst_1726_) == 0)
{
uint64_t v___x_1757_; 
v___x_1757_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg___closed__0);
v___y_1751_ = v___x_1757_;
goto v___jp_1750_;
}
else
{
uint64_t v_hash_1758_; 
v_hash_1758_ = lean_ctor_get_uint64(v_fst_1726_, sizeof(void*)*2);
v___y_1751_ = v_hash_1758_;
goto v___jp_1750_;
}
v___jp_1729_:
{
uint64_t v___x_1732_; uint64_t v___x_1733_; uint64_t v___x_1734_; uint64_t v_fold_1735_; uint64_t v___x_1736_; uint64_t v___x_1737_; uint64_t v___x_1738_; size_t v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; size_t v___x_1742_; size_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1732_ = lean_uint64_mix_hash(v___y_1730_, v___y_1731_);
v___x_1733_ = 32ULL;
v___x_1734_ = lean_uint64_shift_right(v___x_1732_, v___x_1733_);
v_fold_1735_ = lean_uint64_xor(v___x_1732_, v___x_1734_);
v___x_1736_ = 16ULL;
v___x_1737_ = lean_uint64_shift_right(v_fold_1735_, v___x_1736_);
v___x_1738_ = lean_uint64_xor(v_fold_1735_, v___x_1737_);
v___x_1739_ = lean_uint64_to_usize(v___x_1738_);
v___x_1740_ = lean_usize_of_nat(v___x_1728_);
v___x_1741_ = ((size_t)1ULL);
v___x_1742_ = lean_usize_sub(v___x_1740_, v___x_1741_);
v___x_1743_ = lean_usize_land(v___x_1739_, v___x_1742_);
v___x_1744_ = lean_array_uget_borrowed(v_x_1718_, v___x_1743_);
lean_inc(v___x_1744_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 2, v___x_1744_);
v___x_1746_ = v___x_1724_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_key_1720_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_value_1721_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_array_uset(v_x_1718_, v___x_1743_, v___x_1746_);
v_x_1718_ = v___x_1747_;
v_x_1719_ = v_tail_1722_;
goto _start;
}
}
v___jp_1750_:
{
if (lean_obj_tag(v_snd_1727_) == 0)
{
uint64_t v___x_1752_; 
v___x_1752_ = 11ULL;
v___y_1730_ = v___y_1751_;
v___y_1731_ = v___x_1752_;
goto v___jp_1729_;
}
else
{
lean_object* v_val_1753_; uint64_t v___x_1754_; uint64_t v___x_1755_; uint64_t v___x_1756_; 
v_val_1753_ = lean_ctor_get(v_snd_1727_, 0);
v___x_1754_ = lean_string_hash(v_val_1753_);
v___x_1755_ = 13ULL;
v___x_1756_ = lean_uint64_mix_hash(v___x_1754_, v___x_1755_);
v___y_1730_ = v___y_1751_;
v___y_1731_ = v___x_1756_;
goto v___jp_1729_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3___redArg(lean_object* v_i_1760_, lean_object* v_source_1761_, lean_object* v_target_1762_){
_start:
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = lean_array_get_size(v_source_1761_);
v___x_1764_ = lean_nat_dec_lt(v_i_1760_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_dec_ref(v_source_1761_);
lean_dec(v_i_1760_);
return v_target_1762_;
}
else
{
lean_object* v_es_1765_; lean_object* v___x_1766_; lean_object* v_source_1767_; lean_object* v_target_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_es_1765_ = lean_array_fget(v_source_1761_, v_i_1760_);
v___x_1766_ = lean_box(0);
v_source_1767_ = lean_array_fset(v_source_1761_, v_i_1760_, v___x_1766_);
v_target_1768_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg(v_target_1762_, v_es_1765_);
v___x_1769_ = lean_unsigned_to_nat(1u);
v___x_1770_ = lean_nat_add(v_i_1760_, v___x_1769_);
lean_dec(v_i_1760_);
v_i_1760_ = v___x_1770_;
v_source_1761_ = v_source_1767_;
v_target_1762_ = v_target_1768_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1___redArg(lean_object* v_data_1772_){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_nbuckets_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1773_ = lean_array_get_size(v_data_1772_);
v___x_1774_ = lean_unsigned_to_nat(2u);
v_nbuckets_1775_ = lean_nat_mul(v___x_1773_, v___x_1774_);
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = lean_box(0);
v___x_1778_ = lean_mk_array(v_nbuckets_1775_, v___x_1777_);
v___x_1779_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3___redArg(v___x_1776_, v_data_1772_, v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2___lam__0(lean_object* v_a_1780_, lean_object* v_x_1781_){
_start:
{
if (lean_obj_tag(v_x_1781_) == 0)
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_a_1780_);
return v___x_1782_;
}
else
{
lean_object* v_val_1783_; double v_score_1784_; double v_score_1785_; uint8_t v___x_1786_; 
v_val_1783_ = lean_ctor_get(v_x_1781_, 0);
v_score_1784_ = lean_ctor_get_float(v_val_1783_, sizeof(void*)*2);
v_score_1785_ = lean_ctor_get_float(v_a_1780_, sizeof(void*)*2);
v___x_1786_ = lean_float_decLt(v_score_1784_, v_score_1785_);
if (v___x_1786_ == 0)
{
lean_dec_ref(v_a_1780_);
return v_x_1781_;
}
else
{
lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_isSharedCheck_1793_ = !lean_is_exclusive(v_x_1781_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; 
v_unused_1794_ = lean_ctor_get(v_x_1781_, 0);
lean_dec(v_unused_1794_);
v___x_1788_ = v_x_1781_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_dec(v_x_1781_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v_a_1780_);
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1780_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1(lean_object* v_x_1795_, lean_object* v_x_1796_){
_start:
{
if (lean_obj_tag(v_x_1795_) == 0)
{
if (lean_obj_tag(v_x_1796_) == 0)
{
uint8_t v___x_1797_; 
v___x_1797_ = 1;
return v___x_1797_;
}
else
{
uint8_t v___x_1798_; 
v___x_1798_ = 0;
return v___x_1798_;
}
}
else
{
if (lean_obj_tag(v_x_1796_) == 0)
{
uint8_t v___x_1799_; 
v___x_1799_ = 0;
return v___x_1799_;
}
else
{
lean_object* v_val_1800_; lean_object* v_val_1801_; uint8_t v___x_1802_; 
v_val_1800_ = lean_ctor_get(v_x_1795_, 0);
v_val_1801_ = lean_ctor_get(v_x_1796_, 0);
v___x_1802_ = lean_string_dec_eq(v_val_1800_, v_val_1801_);
return v___x_1802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1803_, lean_object* v_x_1804_){
_start:
{
uint8_t v_res_1805_; lean_object* v_r_1806_; 
v_res_1805_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1(v_x_1803_, v_x_1804_);
lean_dec(v_x_1804_);
lean_dec(v_x_1803_);
v_r_1806_ = lean_box(v_res_1805_);
return v_r_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2(lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_x_1809_){
_start:
{
if (lean_obj_tag(v_x_1809_) == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_box(0);
v___x_1811_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2___lam__0(v_a_1807_, v___x_1810_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_dec_ref(v_a_1808_);
return v_x_1809_;
}
else
{
lean_object* v_val_1812_; lean_object* v___x_1813_; 
v_val_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_val_1812_);
lean_dec_ref(v___x_1811_);
v___x_1813_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1813_, 0, v_a_1808_);
lean_ctor_set(v___x_1813_, 1, v_val_1812_);
lean_ctor_set(v___x_1813_, 2, v_x_1809_);
return v___x_1813_;
}
}
else
{
lean_object* v_key_1814_; lean_object* v_value_1815_; lean_object* v_tail_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1838_; 
v_key_1814_ = lean_ctor_get(v_x_1809_, 0);
v_value_1815_ = lean_ctor_get(v_x_1809_, 1);
v_tail_1816_ = lean_ctor_get(v_x_1809_, 2);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_x_1809_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1818_ = v_x_1809_;
v_isShared_1819_ = v_isSharedCheck_1838_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_tail_1816_);
lean_inc(v_value_1815_);
lean_inc(v_key_1814_);
lean_dec(v_x_1809_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1838_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
uint8_t v___y_1821_; lean_object* v_fst_1832_; lean_object* v_snd_1833_; lean_object* v_fst_1834_; lean_object* v_snd_1835_; uint8_t v___x_1836_; 
v_fst_1832_ = lean_ctor_get(v_key_1814_, 0);
v_snd_1833_ = lean_ctor_get(v_key_1814_, 1);
v_fst_1834_ = lean_ctor_get(v_a_1808_, 0);
v_snd_1835_ = lean_ctor_get(v_a_1808_, 1);
v___x_1836_ = lean_name_eq(v_fst_1832_, v_fst_1834_);
if (v___x_1836_ == 0)
{
v___y_1821_ = v___x_1836_;
goto v___jp_1820_;
}
else
{
uint8_t v___x_1837_; 
v___x_1837_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1(v_snd_1833_, v_snd_1835_);
v___y_1821_ = v___x_1837_;
goto v___jp_1820_;
}
v___jp_1820_:
{
if (v___y_1821_ == 0)
{
lean_object* v_tail_1822_; lean_object* v___x_1824_; 
v_tail_1822_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2(v_a_1807_, v_a_1808_, v_tail_1816_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 2, v_tail_1822_);
v___x_1824_ = v___x_1818_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_key_1814_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_value_1815_);
lean_ctor_set(v_reuseFailAlloc_1825_, 2, v_tail_1822_);
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
lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec(v_key_1814_);
v___x_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_value_1815_);
v___x_1827_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2___lam__0(v_a_1807_, v___x_1826_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_del_object(v___x_1818_);
lean_dec_ref(v_a_1808_);
return v_tail_1816_;
}
else
{
lean_object* v_val_1828_; lean_object* v___x_1830_; 
v_val_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_val_1828_);
lean_dec_ref(v___x_1827_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v_val_1828_);
lean_ctor_set(v___x_1818_, 0, v_a_1808_);
v___x_1830_ = v___x_1818_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1808_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_val_1828_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_tail_1816_);
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
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg(lean_object* v_a_1839_, lean_object* v_x_1840_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
uint8_t v___x_1841_; 
v___x_1841_ = 0;
return v___x_1841_;
}
else
{
lean_object* v_key_1842_; lean_object* v_tail_1843_; uint8_t v___y_1845_; lean_object* v_fst_1847_; lean_object* v_snd_1848_; lean_object* v_fst_1849_; lean_object* v_snd_1850_; uint8_t v___x_1851_; 
v_key_1842_ = lean_ctor_get(v_x_1840_, 0);
v_tail_1843_ = lean_ctor_get(v_x_1840_, 2);
v_fst_1847_ = lean_ctor_get(v_key_1842_, 0);
v_snd_1848_ = lean_ctor_get(v_key_1842_, 1);
v_fst_1849_ = lean_ctor_get(v_a_1839_, 0);
v_snd_1850_ = lean_ctor_get(v_a_1839_, 1);
v___x_1851_ = lean_name_eq(v_fst_1847_, v_fst_1849_);
if (v___x_1851_ == 0)
{
v___y_1845_ = v___x_1851_;
goto v___jp_1844_;
}
else
{
uint8_t v___x_1852_; 
v___x_1852_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1(v_snd_1848_, v_snd_1850_);
v___y_1845_ = v___x_1852_;
goto v___jp_1844_;
}
v___jp_1844_:
{
if (v___y_1845_ == 0)
{
v_x_1840_ = v_tail_1843_;
goto _start;
}
else
{
return v___y_1845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg___boxed(lean_object* v_a_1853_, lean_object* v_x_1854_){
_start:
{
uint8_t v_res_1855_; lean_object* v_r_1856_; 
v_res_1855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg(v_a_1853_, v_x_1854_);
lean_dec(v_x_1854_);
lean_dec_ref(v_a_1853_);
v_r_1856_ = lean_box(v_res_1855_);
return v_r_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0(lean_object* v_a_1857_, lean_object* v_m_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v___y_1861_; lean_object* v___y_1862_; size_t v___y_1863_; lean_object* v___y_1864_; lean_object* v_size_1867_; lean_object* v_buckets_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1924_; 
v_size_1867_ = lean_ctor_get(v_m_1858_, 0);
v_buckets_1868_ = lean_ctor_get(v_m_1858_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_m_1858_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1870_ = v_m_1858_;
v_isShared_1871_ = v_isSharedCheck_1924_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_buckets_1868_);
lean_inc(v_size_1867_);
lean_dec(v_m_1858_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1924_;
goto v_resetjp_1869_;
}
v___jp_1860_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_array_uset(v___y_1862_, v___y_1863_, v___y_1861_);
v___x_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___y_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
return v___x_1866_;
}
v_resetjp_1869_:
{
lean_object* v_fst_1872_; lean_object* v_snd_1873_; lean_object* v___x_1874_; uint64_t v___y_1876_; uint64_t v___y_1877_; uint64_t v___y_1916_; 
v_fst_1872_ = lean_ctor_get(v_a_1859_, 0);
v_snd_1873_ = lean_ctor_get(v_a_1859_, 1);
v___x_1874_ = lean_array_get_size(v_buckets_1868_);
if (lean_obj_tag(v_fst_1872_) == 0)
{
uint64_t v___x_1922_; 
v___x_1922_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg___closed__0);
v___y_1916_ = v___x_1922_;
goto v___jp_1915_;
}
else
{
uint64_t v_hash_1923_; 
v_hash_1923_ = lean_ctor_get_uint64(v_fst_1872_, sizeof(void*)*2);
v___y_1916_ = v_hash_1923_;
goto v___jp_1915_;
}
v___jp_1875_:
{
uint64_t v___x_1878_; uint64_t v___x_1879_; uint64_t v___x_1880_; uint64_t v_fold_1881_; uint64_t v___x_1882_; uint64_t v___x_1883_; uint64_t v___x_1884_; size_t v___x_1885_; size_t v___x_1886_; size_t v___x_1887_; size_t v___x_1888_; size_t v___x_1889_; lean_object* v_bkt_1890_; uint8_t v___x_1891_; 
v___x_1878_ = lean_uint64_mix_hash(v___y_1876_, v___y_1877_);
v___x_1879_ = 32ULL;
v___x_1880_ = lean_uint64_shift_right(v___x_1878_, v___x_1879_);
v_fold_1881_ = lean_uint64_xor(v___x_1878_, v___x_1880_);
v___x_1882_ = 16ULL;
v___x_1883_ = lean_uint64_shift_right(v_fold_1881_, v___x_1882_);
v___x_1884_ = lean_uint64_xor(v_fold_1881_, v___x_1883_);
v___x_1885_ = lean_uint64_to_usize(v___x_1884_);
v___x_1886_ = lean_usize_of_nat(v___x_1874_);
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_sub(v___x_1886_, v___x_1887_);
v___x_1889_ = lean_usize_land(v___x_1885_, v___x_1888_);
v_bkt_1890_ = lean_array_uget_borrowed(v_buckets_1868_, v___x_1889_);
v___x_1891_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg(v_a_1859_, v_bkt_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v_size_x27_1893_; lean_object* v___x_1894_; lean_object* v_buckets_x27_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1892_ = lean_unsigned_to_nat(1u);
v_size_x27_1893_ = lean_nat_add(v_size_1867_, v___x_1892_);
lean_dec(v_size_1867_);
lean_inc(v_bkt_1890_);
v___x_1894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1894_, 0, v_a_1859_);
lean_ctor_set(v___x_1894_, 1, v_a_1857_);
lean_ctor_set(v___x_1894_, 2, v_bkt_1890_);
v_buckets_x27_1895_ = lean_array_uset(v_buckets_1868_, v___x_1889_, v___x_1894_);
v___x_1896_ = lean_unsigned_to_nat(4u);
v___x_1897_ = lean_nat_mul(v_size_x27_1893_, v___x_1896_);
v___x_1898_ = lean_unsigned_to_nat(3u);
v___x_1899_ = lean_nat_div(v___x_1897_, v___x_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_array_get_size(v_buckets_x27_1895_);
v___x_1901_ = lean_nat_dec_le(v___x_1899_, v___x_1900_);
lean_dec(v___x_1899_);
if (v___x_1901_ == 0)
{
lean_object* v_val_1902_; lean_object* v___x_1904_; 
v_val_1902_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1___redArg(v_buckets_x27_1895_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 1, v_val_1902_);
lean_ctor_set(v___x_1870_, 0, v_size_x27_1893_);
v___x_1904_ = v___x_1870_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_size_x27_1893_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_val_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
else
{
lean_object* v___x_1907_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 1, v_buckets_x27_1895_);
lean_ctor_set(v___x_1870_, 0, v_size_x27_1893_);
v___x_1907_ = v___x_1870_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_size_x27_1893_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_buckets_x27_1895_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
else
{
lean_object* v___x_1909_; lean_object* v_buckets_x27_1910_; lean_object* v_bkt_x27_1911_; uint8_t v___x_1912_; 
lean_inc(v_bkt_1890_);
lean_del_object(v___x_1870_);
v___x_1909_ = lean_box(0);
v_buckets_x27_1910_ = lean_array_uset(v_buckets_1868_, v___x_1889_, v___x_1909_);
lean_inc_ref(v_a_1859_);
v_bkt_x27_1911_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2(v_a_1857_, v_a_1859_, v_bkt_1890_);
v___x_1912_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg(v_a_1859_, v_bkt_x27_1911_);
lean_dec_ref(v_a_1859_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_unsigned_to_nat(1u);
v___x_1914_ = lean_nat_sub(v_size_1867_, v___x_1913_);
lean_dec(v_size_1867_);
v___y_1861_ = v_bkt_x27_1911_;
v___y_1862_ = v_buckets_x27_1910_;
v___y_1863_ = v___x_1889_;
v___y_1864_ = v___x_1914_;
goto v___jp_1860_;
}
else
{
v___y_1861_ = v_bkt_x27_1911_;
v___y_1862_ = v_buckets_x27_1910_;
v___y_1863_ = v___x_1889_;
v___y_1864_ = v_size_1867_;
goto v___jp_1860_;
}
}
}
v___jp_1915_:
{
if (lean_obj_tag(v_snd_1873_) == 0)
{
uint64_t v___x_1917_; 
v___x_1917_ = 11ULL;
v___y_1876_ = v___y_1916_;
v___y_1877_ = v___x_1917_;
goto v___jp_1875_;
}
else
{
lean_object* v_val_1918_; uint64_t v___x_1919_; uint64_t v___x_1920_; uint64_t v___x_1921_; 
v_val_1918_ = lean_ctor_get(v_snd_1873_, 0);
v___x_1919_ = lean_string_hash(v_val_1918_);
v___x_1920_ = 13ULL;
v___x_1921_ = lean_uint64_mix_hash(v___x_1919_, v___x_1920_);
v___y_1876_ = v___y_1916_;
v___y_1877_ = v___x_1921_;
goto v___jp_1875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg(lean_object* v_as_1925_, size_t v_sz_1926_, size_t v_i_1927_, lean_object* v_b_1928_){
_start:
{
uint8_t v___x_1930_; 
v___x_1930_ = lean_usize_dec_lt(v_i_1927_, v_sz_1926_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v_b_1928_);
return v___x_1931_;
}
else
{
lean_object* v_a_1932_; lean_object* v_name_1933_; lean_object* v_flag_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; size_t v___x_1937_; size_t v___x_1938_; 
v_a_1932_ = lean_array_uget_borrowed(v_as_1925_, v_i_1927_);
v_name_1933_ = lean_ctor_get(v_a_1932_, 0);
v_flag_1934_ = lean_ctor_get(v_a_1932_, 1);
lean_inc(v_flag_1934_);
lean_inc(v_name_1933_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v_name_1933_);
lean_ctor_set(v___x_1935_, 1, v_flag_1934_);
lean_inc(v_a_1932_);
v___x_1936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0(v_a_1932_, v_b_1928_, v___x_1935_);
v___x_1937_ = ((size_t)1ULL);
v___x_1938_ = lean_usize_add(v_i_1927_, v___x_1937_);
v_i_1927_ = v___x_1938_;
v_b_1928_ = v___x_1936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg___boxed(lean_object* v_as_1940_, lean_object* v_sz_1941_, lean_object* v_i_1942_, lean_object* v_b_1943_, lean_object* v___y_1944_){
_start:
{
size_t v_sz_boxed_1945_; size_t v_i_boxed_1946_; lean_object* v_res_1947_; 
v_sz_boxed_1945_ = lean_unbox_usize(v_sz_1941_);
lean_dec(v_sz_1941_);
v_i_boxed_1946_ = lean_unbox_usize(v_i_1942_);
lean_dec(v_i_1942_);
v_res_1947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg(v_as_1940_, v_sz_boxed_1945_, v_i_boxed_1946_, v_b_1943_);
lean_dec_ref(v_as_1940_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_Selector_combine_spec__3(lean_object* v_x_1948_, lean_object* v_x_1949_){
_start:
{
if (lean_obj_tag(v_x_1949_) == 0)
{
return v_x_1948_;
}
else
{
lean_object* v_value_1950_; lean_object* v_tail_1951_; lean_object* v___x_1952_; 
v_value_1950_ = lean_ctor_get(v_x_1949_, 1);
lean_inc(v_value_1950_);
v_tail_1951_ = lean_ctor_get(v_x_1949_, 2);
lean_inc(v_tail_1951_);
lean_dec_ref(v_x_1949_);
v___x_1952_ = lean_array_push(v_x_1948_, v_value_1950_);
v_x_1948_ = v___x_1952_;
v_x_1949_ = v_tail_1951_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4(lean_object* v_as_1954_, size_t v_i_1955_, size_t v_stop_1956_, lean_object* v_b_1957_){
_start:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_usize_dec_eq(v_i_1955_, v_stop_1956_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; size_t v___x_1961_; size_t v___x_1962_; 
v___x_1959_ = lean_array_uget_borrowed(v_as_1954_, v_i_1955_);
lean_inc(v___x_1959_);
v___x_1960_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_Selector_combine_spec__3(v_b_1957_, v___x_1959_);
v___x_1961_ = ((size_t)1ULL);
v___x_1962_ = lean_usize_add(v_i_1955_, v___x_1961_);
v_i_1955_ = v___x_1962_;
v_b_1957_ = v___x_1960_;
goto _start;
}
else
{
return v_b_1957_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4___boxed(lean_object* v_as_1964_, lean_object* v_i_1965_, lean_object* v_stop_1966_, lean_object* v_b_1967_){
_start:
{
size_t v_i_boxed_1968_; size_t v_stop_boxed_1969_; lean_object* v_res_1970_; 
v_i_boxed_1968_ = lean_unbox_usize(v_i_1965_);
lean_dec(v_i_1965_);
v_stop_boxed_1969_ = lean_unbox_usize(v_stop_1966_);
lean_dec(v_stop_1966_);
v_res_1970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4(v_as_1964_, v_i_boxed_1968_, v_stop_boxed_1969_, v_b_1967_);
lean_dec_ref(v_as_1964_);
return v_res_1970_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_combine___closed__0(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = lean_box(0);
v___x_1972_ = lean_unsigned_to_nat(16u);
v___x_1973_ = lean_mk_array(v___x_1972_, v___x_1971_);
return v___x_1973_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_combine___closed__1(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = lean_obj_once(&l_Lean_LibrarySuggestions_Selector_combine___closed__0, &l_Lean_LibrarySuggestions_Selector_combine___closed__0_once, _init_l_Lean_LibrarySuggestions_Selector_combine___closed__0);
v___x_1975_ = lean_unsigned_to_nat(0u);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v___x_1974_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_combine(lean_object* v_selector_u2081_1977_, lean_object* v_selector_u2082_1978_, lean_object* v_g_1979_, lean_object* v_c_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1986_; 
lean_inc(v_a_1984_);
lean_inc_ref(v_a_1983_);
lean_inc(v_a_1982_);
lean_inc_ref(v_a_1981_);
lean_inc_ref(v_c_1980_);
lean_inc(v_g_1979_);
v___x_1986_ = lean_apply_7(v_selector_u2081_1977_, v_g_1979_, v_c_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, lean_box(0));
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1988_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1986_);
lean_inc_ref(v_c_1980_);
v___x_1988_ = lean_apply_7(v_selector_u2082_1978_, v_g_1979_, v_c_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, lean_box(0));
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; size_t v_sz_1993_; size_t v___x_1994_; lean_object* v___x_1995_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref(v___x_1988_);
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = lean_obj_once(&l_Lean_LibrarySuggestions_Selector_combine___closed__1, &l_Lean_LibrarySuggestions_Selector_combine___closed__1_once, _init_l_Lean_LibrarySuggestions_Selector_combine___closed__1);
v___x_1992_ = l_Array_append___redArg(v_a_1987_, v_a_1989_);
lean_dec(v_a_1989_);
v_sz_1993_ = lean_array_size(v___x_1992_);
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg(v___x_1992_, v_sz_1993_, v___x_1994_, v___x_1991_);
lean_dec_ref(v___x_1992_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2036_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2036_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2036_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___y_2001_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2020_; lean_object* v_size_2026_; lean_object* v_buckets_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v_size_2026_ = lean_ctor_get(v_a_1996_, 0);
lean_inc(v_size_2026_);
v_buckets_2027_ = lean_ctor_get(v_a_1996_, 1);
lean_inc_ref(v_buckets_2027_);
lean_dec(v_a_1996_);
v___x_2028_ = lean_mk_empty_array_with_capacity(v_size_2026_);
lean_dec(v_size_2026_);
v___x_2029_ = lean_array_get_size(v_buckets_2027_);
v___x_2030_ = lean_nat_dec_lt(v___x_1990_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_dec_ref(v_buckets_2027_);
v___y_2020_ = v___x_2028_;
goto v___jp_2019_;
}
else
{
uint8_t v___x_2031_; 
v___x_2031_ = lean_nat_dec_le(v___x_2029_, v___x_2029_);
if (v___x_2031_ == 0)
{
if (v___x_2030_ == 0)
{
lean_dec_ref(v_buckets_2027_);
v___y_2020_ = v___x_2028_;
goto v___jp_2019_;
}
else
{
size_t v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_usize_of_nat(v___x_2029_);
v___x_2033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4(v_buckets_2027_, v___x_1994_, v___x_2032_, v___x_2028_);
lean_dec_ref(v_buckets_2027_);
v___y_2020_ = v___x_2033_;
goto v___jp_2019_;
}
}
else
{
size_t v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_usize_of_nat(v___x_2029_);
v___x_2035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4(v_buckets_2027_, v___x_1994_, v___x_2034_, v___x_2028_);
lean_dec_ref(v_buckets_2027_);
v___y_2020_ = v___x_2035_;
goto v___jp_2019_;
}
}
v___jp_2000_:
{
lean_object* v_maxSuggestions_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v_maxSuggestions_2002_ = lean_ctor_get(v_c_1980_, 0);
lean_inc(v_maxSuggestions_2002_);
lean_dec_ref(v_c_1980_);
v___x_2003_ = l_Array_extract___redArg(v___y_2001_, v___x_1990_, v_maxSuggestions_2002_);
lean_dec_ref(v___y_2001_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2003_);
v___x_2005_ = v___x_1998_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
v___jp_2007_:
{
lean_object* v___x_2012_; 
lean_dec(v___y_2010_);
v___x_2012_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg(v___y_2009_, v___y_2008_, v___y_2011_);
lean_dec(v___y_2011_);
v___y_2001_ = v___x_2012_;
goto v___jp_2000_;
}
v___jp_2013_:
{
uint8_t v___x_2018_; 
v___x_2018_ = lean_nat_dec_le(v___y_2017_, v___y_2016_);
if (v___x_2018_ == 0)
{
lean_dec(v___y_2016_);
lean_inc(v___y_2017_);
v___y_2008_ = v___y_2017_;
v___y_2009_ = v___y_2014_;
v___y_2010_ = v___y_2015_;
v___y_2011_ = v___y_2017_;
goto v___jp_2007_;
}
else
{
v___y_2008_ = v___y_2017_;
v___y_2009_ = v___y_2014_;
v___y_2010_ = v___y_2015_;
v___y_2011_ = v___y_2016_;
goto v___jp_2007_;
}
}
v___jp_2019_:
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = lean_array_get_size(v___y_2020_);
v___x_2022_ = lean_nat_dec_eq(v___x_2021_, v___x_1990_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = lean_nat_sub(v___x_2021_, v___x_2023_);
v___x_2025_ = lean_nat_dec_le(v___x_1990_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_inc(v___x_2024_);
v___y_2014_ = v___y_2020_;
v___y_2015_ = v___x_2021_;
v___y_2016_ = v___x_2024_;
v___y_2017_ = v___x_2024_;
goto v___jp_2013_;
}
else
{
v___y_2014_ = v___y_2020_;
v___y_2015_ = v___x_2021_;
v___y_2016_ = v___x_2024_;
v___y_2017_ = v___x_1990_;
goto v___jp_2013_;
}
}
else
{
v___y_2001_ = v___y_2020_;
goto v___jp_2000_;
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec_ref(v_c_1980_);
v_a_2037_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_1995_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_1995_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_dec(v_a_1987_);
lean_dec_ref(v_c_1980_);
return v___x_1988_;
}
}
else
{
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec_ref(v_c_1980_);
lean_dec(v_g_1979_);
lean_dec_ref(v_selector_u2082_1978_);
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_combine___boxed(lean_object* v_selector_u2081_2045_, lean_object* v_selector_u2082_2046_, lean_object* v_g_2047_, lean_object* v_c_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_LibrarySuggestions_Selector_combine(v_selector_u2081_2045_, v_selector_u2082_2046_, v_g_2047_, v_c_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1(lean_object* v_as_2055_, size_t v_sz_2056_, size_t v_i_2057_, lean_object* v_b_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg(v_as_2055_, v_sz_2056_, v_i_2057_, v_b_2058_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___boxed(lean_object* v_as_2065_, lean_object* v_sz_2066_, lean_object* v_i_2067_, lean_object* v_b_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
size_t v_sz_boxed_2074_; size_t v_i_boxed_2075_; lean_object* v_res_2076_; 
v_sz_boxed_2074_ = lean_unbox_usize(v_sz_2066_);
lean_dec(v_sz_2066_);
v_i_boxed_2075_ = lean_unbox_usize(v_i_2067_);
lean_dec(v_i_2067_);
v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1(v_as_2065_, v_sz_boxed_2074_, v_i_boxed_2075_, v_b_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec_ref(v_as_2065_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2(lean_object* v_n_2077_, lean_object* v_as_2078_, lean_object* v_lo_2079_, lean_object* v_hi_2080_, lean_object* v_w_2081_, lean_object* v_hlo_2082_, lean_object* v_hhi_2083_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg(v_as_2078_, v_lo_2079_, v_hi_2080_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___boxed(lean_object* v_n_2085_, lean_object* v_as_2086_, lean_object* v_lo_2087_, lean_object* v_hi_2088_, lean_object* v_w_2089_, lean_object* v_hlo_2090_, lean_object* v_hhi_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2(v_n_2085_, v_as_2086_, v_lo_2087_, v_hi_2088_, v_w_2089_, v_hlo_2090_, v_hhi_2091_);
lean_dec(v_hi_2088_);
lean_dec(v_n_2085_);
return v_res_2092_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0(lean_object* v_00_u03b2_2093_, lean_object* v_a_2094_, lean_object* v_x_2095_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg(v_a_2094_, v_x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2097_, lean_object* v_a_2098_, lean_object* v_x_2099_){
_start:
{
uint8_t v_res_2100_; lean_object* v_r_2101_; 
v_res_2100_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0(v_00_u03b2_2097_, v_a_2098_, v_x_2099_);
lean_dec(v_x_2099_);
lean_dec_ref(v_a_2098_);
v_r_2101_ = lean_box(v_res_2100_);
return v_r_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1(lean_object* v_00_u03b2_2102_, lean_object* v_data_2103_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1___redArg(v_data_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2105_, lean_object* v_i_2106_, lean_object* v_source_2107_, lean_object* v_target_2108_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3___redArg(v_i_2106_, v_source_2107_, v_target_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2110_, lean_object* v_x_2111_, lean_object* v_x_2112_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg(v_x_2111_, v_x_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(lean_object* v___x_2114_, lean_object* v_as_2115_, size_t v_i_2116_, size_t v_stop_2117_, lean_object* v_b_2118_){
_start:
{
lean_object* v_a_2121_; uint8_t v___x_2125_; 
v___x_2125_ = lean_usize_dec_eq(v_i_2116_, v_stop_2117_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v_name_2129_; lean_object* v___x_2130_; 
v___x_2126_ = lean_array_uget_borrowed(v_as_2115_, v_i_2116_);
v_name_2129_ = lean_ctor_get(v___x_2126_, 0);
v___x_2130_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_2114_, v_name_2129_);
if (lean_obj_tag(v___x_2130_) == 0)
{
goto v___jp_2127_;
}
else
{
lean_object* v_val_2131_; uint8_t v___x_2132_; 
v_val_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_val_2131_);
lean_dec_ref(v___x_2130_);
lean_inc_ref(v___x_2114_);
v___x_2132_ = l_Lean_Elab_Tactic_Grind_isGrindAnnotatedModule(v___x_2114_, v_val_2131_);
lean_dec(v_val_2131_);
if (v___x_2132_ == 0)
{
goto v___jp_2127_;
}
else
{
v_a_2121_ = v_b_2118_;
goto v___jp_2120_;
}
}
v___jp_2127_:
{
lean_object* v___x_2128_; 
lean_inc(v___x_2126_);
v___x_2128_ = lean_array_push(v_b_2118_, v___x_2126_);
v_a_2121_ = v___x_2128_;
goto v___jp_2120_;
}
}
else
{
lean_object* v___x_2133_; 
lean_dec_ref(v___x_2114_);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_b_2118_);
return v___x_2133_;
}
v___jp_2120_:
{
size_t v___x_2122_; size_t v___x_2123_; 
v___x_2122_ = ((size_t)1ULL);
v___x_2123_ = lean_usize_add(v_i_2116_, v___x_2122_);
v_i_2116_ = v___x_2123_;
v_b_2118_ = v_a_2121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg___boxed(lean_object* v___x_2134_, lean_object* v_as_2135_, lean_object* v_i_2136_, lean_object* v_stop_2137_, lean_object* v_b_2138_, lean_object* v___y_2139_){
_start:
{
size_t v_i_boxed_2140_; size_t v_stop_boxed_2141_; lean_object* v_res_2142_; 
v_i_boxed_2140_ = lean_unbox_usize(v_i_2136_);
lean_dec(v_i_2136_);
v_stop_boxed_2141_ = lean_unbox_usize(v_stop_2137_);
lean_dec(v_stop_2137_);
v_res_2142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(v___x_2134_, v_as_2135_, v_i_boxed_2140_, v_stop_boxed_2141_, v_b_2138_);
lean_dec_ref(v_as_2135_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated(lean_object* v_selector_2146_, lean_object* v_g_2147_, lean_object* v_c_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v___x_2154_; 
lean_inc(v_a_2152_);
lean_inc_ref(v_c_2148_);
v___x_2154_ = lean_apply_7(v_selector_2146_, v_g_2147_, v_c_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, lean_box(0));
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v_caller_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
v_caller_2156_ = lean_ctor_get(v_c_2148_, 1);
lean_inc(v_caller_2156_);
lean_dec_ref(v_c_2148_);
v___x_2157_ = ((lean_object*)(l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__1));
v___x_2158_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1(v_caller_2156_, v___x_2157_);
lean_dec(v_caller_2156_);
if (v___x_2158_ == 0)
{
lean_dec(v_a_2155_);
lean_dec(v_a_2152_);
return v___x_2154_;
}
else
{
lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2181_; 
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v___x_2154_, 0);
lean_dec(v_unused_2182_);
v___x_2160_ = v___x_2154_;
v_isShared_2161_ = v_isSharedCheck_2181_;
goto v_resetjp_2159_;
}
else
{
lean_dec(v___x_2154_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2181_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2162_ = lean_st_ref_get(v_a_2152_);
lean_dec(v_a_2152_);
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = lean_array_get_size(v_a_2155_);
v___x_2165_ = ((lean_object*)(l_Lean_LibrarySuggestions_Selector_postFilter___closed__1));
v___x_2166_ = lean_nat_dec_lt(v___x_2163_, v___x_2164_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2168_; 
lean_dec(v___x_2162_);
lean_dec(v_a_2155_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2165_);
v___x_2168_ = v___x_2160_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2165_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
else
{
lean_object* v_env_2170_; uint8_t v___x_2171_; 
v_env_2170_ = lean_ctor_get(v___x_2162_, 0);
lean_inc_ref(v_env_2170_);
lean_dec(v___x_2162_);
v___x_2171_ = lean_nat_dec_le(v___x_2164_, v___x_2164_);
if (v___x_2171_ == 0)
{
if (v___x_2166_ == 0)
{
lean_object* v___x_2173_; 
lean_dec_ref(v_env_2170_);
lean_dec(v_a_2155_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2165_);
v___x_2173_ = v___x_2160_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2165_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
else
{
size_t v___x_2175_; size_t v___x_2176_; lean_object* v___x_2177_; 
lean_del_object(v___x_2160_);
v___x_2175_ = ((size_t)0ULL);
v___x_2176_ = lean_usize_of_nat(v___x_2164_);
v___x_2177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(v_env_2170_, v_a_2155_, v___x_2175_, v___x_2176_, v___x_2165_);
lean_dec(v_a_2155_);
return v___x_2177_;
}
}
else
{
size_t v___x_2178_; size_t v___x_2179_; lean_object* v___x_2180_; 
lean_del_object(v___x_2160_);
v___x_2178_ = ((size_t)0ULL);
v___x_2179_ = lean_usize_of_nat(v___x_2164_);
v___x_2180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(v_env_2170_, v_a_2155_, v___x_2178_, v___x_2179_, v___x_2165_);
lean_dec(v_a_2155_);
return v___x_2180_;
}
}
}
}
}
else
{
lean_dec(v_a_2152_);
lean_dec_ref(v_c_2148_);
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___boxed(lean_object* v_selector_2183_, lean_object* v_g_2184_, lean_object* v_c_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated(v_selector_2183_, v_g_2184_, v_c_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0(lean_object* v___x_2192_, lean_object* v_as_2193_, size_t v_i_2194_, size_t v_stop_2195_, lean_object* v_b_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(v___x_2192_, v_as_2193_, v_i_2194_, v_stop_2195_, v_b_2196_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___boxed(lean_object* v___x_2203_, lean_object* v_as_2204_, lean_object* v_i_2205_, lean_object* v_stop_2206_, lean_object* v_b_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
size_t v_i_boxed_2213_; size_t v_stop_boxed_2214_; lean_object* v_res_2215_; 
v_i_boxed_2213_ = lean_unbox_usize(v_i_2205_);
lean_dec(v_i_2205_);
v_stop_boxed_2214_ = lean_unbox_usize(v_stop_2206_);
lean_dec(v_stop_2206_);
v_res_2215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0(v___x_2203_, v_as_2204_, v_i_boxed_2213_, v_stop_boxed_2214_, v_b_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec_ref(v_as_2204_);
return v_res_2215_;
}
}
static double _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2216_; double v___x_2217_; 
v___x_2216_ = lean_unsigned_to_nat(1u);
v___x_2217_ = lean_float_of_nat(v___x_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg(double v_ratio_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v___x_2221_, lean_object* v_b_2222_){
_start:
{
lean_object* v_snd_2224_; lean_object* v_snd_2225_; lean_object* v_snd_2226_; lean_object* v_fst_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2304_; 
v_snd_2224_ = lean_ctor_get(v_b_2222_, 1);
lean_inc(v_snd_2224_);
v_snd_2225_ = lean_ctor_get(v_snd_2224_, 1);
lean_inc(v_snd_2225_);
v_snd_2226_ = lean_ctor_get(v_snd_2225_, 1);
lean_inc(v_snd_2226_);
v_fst_2227_ = lean_ctor_get(v_b_2222_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v_b_2222_);
if (v_isSharedCheck_2304_ == 0)
{
lean_object* v_unused_2305_; 
v_unused_2305_ = lean_ctor_get(v_b_2222_, 1);
lean_dec(v_unused_2305_);
v___x_2229_ = v_b_2222_;
v_isShared_2230_ = v_isSharedCheck_2304_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_fst_2227_);
lean_dec(v_b_2222_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2304_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_fst_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2302_; 
v_fst_2231_ = lean_ctor_get(v_snd_2224_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_snd_2224_);
if (v_isSharedCheck_2302_ == 0)
{
lean_object* v_unused_2303_; 
v_unused_2303_ = lean_ctor_get(v_snd_2224_, 1);
lean_dec(v_unused_2303_);
v___x_2233_ = v_snd_2224_;
v_isShared_2234_ = v_isSharedCheck_2302_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_fst_2231_);
lean_dec(v_snd_2224_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2302_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v_fst_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2300_; 
v_fst_2235_ = lean_ctor_get(v_snd_2225_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_snd_2225_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; 
v_unused_2301_ = lean_ctor_get(v_snd_2225_, 1);
lean_dec(v_unused_2301_);
v___x_2237_ = v_snd_2225_;
v_isShared_2238_ = v_isSharedCheck_2300_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_fst_2235_);
lean_dec(v_snd_2225_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2300_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v_fst_2239_; lean_object* v_snd_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2299_; 
v_fst_2239_ = lean_ctor_get(v_snd_2226_, 0);
v_snd_2240_ = lean_ctor_get(v_snd_2226_, 1);
v_isSharedCheck_2299_ = !lean_is_exclusive(v_snd_2226_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2242_ = v_snd_2226_;
v_isShared_2243_ = v_isSharedCheck_2299_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_snd_2240_);
lean_inc(v_fst_2239_);
lean_dec(v_snd_2226_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2299_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2258_; uint8_t v___x_2259_; 
v___x_2258_ = lean_array_get_size(v_a_2220_);
v___x_2259_ = lean_nat_dec_lt(v_fst_2231_, v___x_2258_);
if (v___x_2259_ == 0)
{
goto v___jp_2244_;
}
else
{
lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2260_ = lean_array_get_size(v_a_2219_);
v___x_2261_ = lean_nat_dec_lt(v_fst_2235_, v___x_2260_);
if (v___x_2261_ == 0)
{
goto v___jp_2244_;
}
else
{
lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = lean_array_get_size(v_fst_2227_);
v___x_2263_ = lean_nat_dec_lt(v___x_2262_, v___x_2221_);
if (v___x_2263_ == 0)
{
goto v___jp_2244_;
}
else
{
lean_object* v___x_2264_; double v___x_2265_; double v___y_2267_; lean_object* v___x_2291_; double v___x_2292_; double v___x_2293_; double v___x_2294_; double v___x_2295_; uint8_t v___x_2296_; 
lean_del_object(v___x_2242_);
lean_del_object(v___x_2237_);
lean_del_object(v___x_2233_);
lean_del_object(v___x_2229_);
v___x_2264_ = lean_unsigned_to_nat(1u);
v___x_2265_ = lean_float_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0);
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = l_Float_ofScientific(v___x_2291_, v___x_2263_, v___x_2264_);
v___x_2293_ = lean_unbox_float(v_fst_2239_);
v___x_2294_ = lean_unbox_float(v_snd_2240_);
v___x_2295_ = lean_float_add(v___x_2293_, v___x_2294_);
v___x_2296_ = lean_float_decLe(v___x_2295_, v___x_2292_);
if (v___x_2296_ == 0)
{
double v___x_2297_; double v___x_2298_; 
v___x_2297_ = lean_unbox_float(v_fst_2239_);
v___x_2298_ = lean_float_div(v___x_2297_, v___x_2295_);
v___y_2267_ = v___x_2298_;
goto v___jp_2266_;
}
else
{
v___y_2267_ = v___x_2292_;
goto v___jp_2266_;
}
v___jp_2266_:
{
uint8_t v___x_2268_; 
v___x_2268_ = lean_float_decLt(v___y_2267_, v_ratio_2218_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; double v___x_2272_; double v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2269_ = lean_array_fget_borrowed(v_a_2219_, v_fst_2235_);
lean_inc(v___x_2269_);
v___x_2270_ = lean_array_push(v_fst_2227_, v___x_2269_);
v___x_2271_ = lean_nat_add(v_fst_2235_, v___x_2264_);
lean_dec(v_fst_2235_);
v___x_2272_ = lean_unbox_float(v_snd_2240_);
lean_dec(v_snd_2240_);
v___x_2273_ = lean_float_add(v___x_2272_, v___x_2265_);
v___x_2274_ = lean_box_float(v___x_2273_);
v___x_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2275_, 0, v_fst_2239_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2271_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2277_, 0, v_fst_2231_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2270_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v_b_2222_ = v___x_2278_;
goto _start;
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; double v___x_2283_; double v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2280_ = lean_array_fget_borrowed(v_a_2220_, v_fst_2231_);
lean_inc(v___x_2280_);
v___x_2281_ = lean_array_push(v_fst_2227_, v___x_2280_);
v___x_2282_ = lean_nat_add(v_fst_2231_, v___x_2264_);
lean_dec(v_fst_2231_);
v___x_2283_ = lean_unbox_float(v_fst_2239_);
lean_dec(v_fst_2239_);
v___x_2284_ = lean_float_add(v___x_2283_, v___x_2265_);
v___x_2285_ = lean_box_float(v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v_snd_2240_);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_fst_2235_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2282_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2281_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v_b_2222_ = v___x_2289_;
goto _start;
}
}
}
}
}
v___jp_2244_:
{
lean_object* v___x_2246_; 
if (v_isShared_2243_ == 0)
{
v___x_2246_ = v___x_2242_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_fst_2239_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_snd_2240_);
v___x_2246_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
lean_object* v___x_2248_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 1, v___x_2246_);
v___x_2248_ = v___x_2237_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_fst_2235_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2250_; 
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 1, v___x_2248_);
v___x_2250_ = v___x_2233_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_fst_2231_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2252_; 
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v___x_2250_);
v___x_2252_ = v___x_2229_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_fst_2227_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___boxed(lean_object* v_ratio_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v___x_2309_, lean_object* v_b_2310_, lean_object* v___y_2311_){
_start:
{
double v_ratio_boxed_2312_; lean_object* v_res_2313_; 
v_ratio_boxed_2312_ = lean_unbox_float(v_ratio_2306_);
lean_dec_ref(v_ratio_2306_);
v_res_2313_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg(v_ratio_boxed_2312_, v_a_2307_, v_a_2308_, v___x_2309_, v_b_2310_);
lean_dec(v___x_2309_);
lean_dec_ref(v_a_2308_);
lean_dec_ref(v_a_2307_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(lean_object* v_a_2314_, lean_object* v___x_2315_, lean_object* v_b_2316_){
_start:
{
lean_object* v_fst_2318_; lean_object* v_snd_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2338_; 
v_fst_2318_ = lean_ctor_get(v_b_2316_, 0);
v_snd_2319_ = lean_ctor_get(v_b_2316_, 1);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_b_2316_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2321_ = v_b_2316_;
v_isShared_2322_ = v_isSharedCheck_2338_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_snd_2319_);
lean_inc(v_fst_2318_);
lean_dec(v_b_2316_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2338_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = lean_array_get_size(v_a_2314_);
v___x_2329_ = lean_nat_dec_lt(v_snd_2319_, v___x_2328_);
if (v___x_2329_ == 0)
{
goto v___jp_2323_;
}
else
{
lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = lean_array_get_size(v_fst_2318_);
v___x_2331_ = lean_nat_dec_lt(v___x_2330_, v___x_2315_);
if (v___x_2331_ == 0)
{
goto v___jp_2323_;
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_del_object(v___x_2321_);
v___x_2332_ = lean_unsigned_to_nat(1u);
v___x_2333_ = lean_array_fget_borrowed(v_a_2314_, v_snd_2319_);
lean_inc(v___x_2333_);
v___x_2334_ = lean_array_push(v_fst_2318_, v___x_2333_);
v___x_2335_ = lean_nat_add(v_snd_2319_, v___x_2332_);
lean_dec(v_snd_2319_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v_b_2316_ = v___x_2336_;
goto _start;
}
}
v___jp_2323_:
{
lean_object* v___x_2325_; 
if (v_isShared_2322_ == 0)
{
v___x_2325_ = v___x_2321_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_fst_2318_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_snd_2319_);
v___x_2325_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg___boxed(lean_object* v_a_2339_, lean_object* v___x_2340_, lean_object* v_b_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(v_a_2339_, v___x_2340_, v_b_2341_);
lean_dec(v___x_2340_);
lean_dec_ref(v_a_2339_);
return v_res_2343_;
}
}
static double _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__0(void){
_start:
{
lean_object* v___x_2344_; uint8_t v___x_2345_; lean_object* v___x_2346_; double v___x_2347_; 
v___x_2344_ = lean_unsigned_to_nat(1u);
v___x_2345_ = 1;
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = l_Float_ofScientific(v___x_2346_, v___x_2345_, v___x_2344_);
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__1___boxed__const__1(void){
_start:
{
double v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_float_once(&l_Lean_LibrarySuggestions_Selector_intersperse___closed__0, &l_Lean_LibrarySuggestions_Selector_intersperse___closed__0_once, _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__0);
v___x_2349_ = lean_box_float(v___x_2348_);
return v___x_2349_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__1(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = l_Lean_LibrarySuggestions_Selector_intersperse___closed__1___boxed__const__1;
v___x_2351_ = l_Lean_LibrarySuggestions_Selector_intersperse___closed__1___boxed__const__1;
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
return v___x_2352_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__2(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = lean_obj_once(&l_Lean_LibrarySuggestions_Selector_intersperse___closed__1, &l_Lean_LibrarySuggestions_Selector_intersperse___closed__1_once, _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__1);
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
lean_ctor_set(v___x_2355_, 1, v___x_2353_);
return v___x_2355_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__3(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = lean_obj_once(&l_Lean_LibrarySuggestions_Selector_intersperse___closed__2, &l_Lean_LibrarySuggestions_Selector_intersperse___closed__2_once, _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__2);
v___x_2357_ = lean_unsigned_to_nat(0u);
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
lean_ctor_set(v___x_2358_, 1, v___x_2356_);
return v___x_2358_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__4(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = lean_obj_once(&l_Lean_LibrarySuggestions_Selector_intersperse___closed__3, &l_Lean_LibrarySuggestions_Selector_intersperse___closed__3_once, _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__3);
v___x_2360_ = ((lean_object*)(l_Lean_LibrarySuggestions_Selector_postFilter___closed__1));
v___x_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
lean_ctor_set(v___x_2361_, 1, v___x_2359_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_intersperse(lean_object* v_selector_u2081_2362_, lean_object* v_selector_u2082_2363_, double v_ratio_2364_, lean_object* v_g_2365_, lean_object* v_c_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v_maxSuggestions_2372_; lean_object* v_caller_2373_; lean_object* v_filter_2374_; lean_object* v_hint_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2456_; 
v_maxSuggestions_2372_ = lean_ctor_get(v_c_2366_, 0);
v_caller_2373_ = lean_ctor_get(v_c_2366_, 1);
v_filter_2374_ = lean_ctor_get(v_c_2366_, 2);
v_hint_2375_ = lean_ctor_get(v_c_2366_, 3);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_c_2366_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2377_ = v_c_2366_;
v_isShared_2378_ = v_isSharedCheck_2456_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_hint_2375_);
lean_inc(v_filter_2374_);
lean_inc(v_caller_2373_);
lean_inc(v_maxSuggestions_2372_);
lean_dec(v_c_2366_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2456_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
double v___x_2379_; double v___x_2380_; uint32_t v___x_2381_; lean_object* v_max_u2081_2382_; lean_object* v___x_2384_; 
lean_inc(v_maxSuggestions_2372_);
v___x_2379_ = lean_float_of_nat(v_maxSuggestions_2372_);
v___x_2380_ = lean_float_mul(v___x_2379_, v_ratio_2364_);
v___x_2381_ = lean_float_to_uint32(v___x_2380_);
v_max_u2081_2382_ = lean_uint32_to_nat(v___x_2381_);
lean_inc(v_hint_2375_);
lean_inc_ref(v_filter_2374_);
lean_inc(v_caller_2373_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v_max_u2081_2382_);
v___x_2384_ = v___x_2377_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_max_u2081_2382_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_caller_2373_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_filter_2374_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v_hint_2375_);
v___x_2384_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; 
lean_inc(v_a_2370_);
lean_inc_ref(v_a_2369_);
lean_inc(v_a_2368_);
lean_inc_ref(v_a_2367_);
lean_inc(v_g_2365_);
v___x_2385_ = lean_apply_7(v_selector_u2081_2362_, v_g_2365_, v___x_2384_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, lean_box(0));
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; double v___x_2387_; double v___x_2388_; double v___x_2389_; uint32_t v___x_2390_; lean_object* v_max_u2082_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref(v___x_2385_);
v___x_2387_ = lean_float_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0);
v___x_2388_ = lean_float_sub(v___x_2387_, v_ratio_2364_);
v___x_2389_ = lean_float_mul(v___x_2379_, v___x_2388_);
v___x_2390_ = lean_float_to_uint32(v___x_2389_);
v_max_u2082_2391_ = lean_uint32_to_nat(v___x_2390_);
v___x_2392_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2392_, 0, v_max_u2082_2391_);
lean_ctor_set(v___x_2392_, 1, v_caller_2373_);
lean_ctor_set(v___x_2392_, 2, v_filter_2374_);
lean_ctor_set(v___x_2392_, 3, v_hint_2375_);
v___x_2393_ = lean_apply_7(v_selector_u2082_2363_, v_g_2365_, v___x_2392_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, lean_box(0));
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref(v___x_2393_);
v___x_2395_ = lean_obj_once(&l_Lean_LibrarySuggestions_Selector_intersperse___closed__4, &l_Lean_LibrarySuggestions_Selector_intersperse___closed__4_once, _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__4);
v___x_2396_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg(v_ratio_2364_, v_a_2394_, v_a_2386_, v_maxSuggestions_2372_, v___x_2395_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v_snd_2398_; lean_object* v_fst_2399_; lean_object* v_fst_2400_; lean_object* v_snd_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2446_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref(v___x_2396_);
v_snd_2398_ = lean_ctor_get(v_a_2397_, 1);
lean_inc(v_snd_2398_);
v_fst_2399_ = lean_ctor_get(v_a_2397_, 0);
lean_inc(v_fst_2399_);
lean_dec(v_a_2397_);
v_fst_2400_ = lean_ctor_get(v_snd_2398_, 0);
v_snd_2401_ = lean_ctor_get(v_snd_2398_, 1);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_snd_2398_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2403_ = v_snd_2398_;
v_isShared_2404_ = v_isSharedCheck_2446_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_snd_2401_);
lean_inc(v_fst_2400_);
lean_dec(v_snd_2398_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2446_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 1, v_fst_2400_);
lean_ctor_set(v___x_2403_, 0, v_fst_2399_);
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_fst_2399_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v_fst_2400_);
v___x_2406_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2407_; 
v___x_2407_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(v_a_2386_, v_maxSuggestions_2372_, v___x_2406_);
lean_dec(v_a_2386_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v_fst_2409_; lean_object* v_fst_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2435_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref(v___x_2407_);
v_fst_2409_ = lean_ctor_get(v_snd_2401_, 0);
lean_inc(v_fst_2409_);
lean_dec(v_snd_2401_);
v_fst_2410_ = lean_ctor_get(v_a_2408_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_a_2408_);
if (v_isSharedCheck_2435_ == 0)
{
lean_object* v_unused_2436_; 
v_unused_2436_ = lean_ctor_get(v_a_2408_, 1);
lean_dec(v_unused_2436_);
v___x_2412_ = v_a_2408_;
v_isShared_2413_ = v_isSharedCheck_2435_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_fst_2410_);
lean_dec(v_a_2408_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2435_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v_fst_2409_);
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_fst_2410_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_fst_2409_);
v___x_2415_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2416_; 
v___x_2416_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(v_a_2394_, v_maxSuggestions_2372_, v___x_2415_);
lean_dec(v_maxSuggestions_2372_);
lean_dec(v_a_2394_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2425_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2425_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2425_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v_fst_2421_; lean_object* v___x_2423_; 
v_fst_2421_ = lean_ctor_get(v_a_2417_, 0);
lean_inc(v_fst_2421_);
lean_dec(v_a_2417_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v_fst_2421_);
v___x_2423_ = v___x_2419_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_fst_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2416_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2416_);
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
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec(v_snd_2401_);
lean_dec(v_a_2394_);
lean_dec(v_maxSuggestions_2372_);
v_a_2437_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2407_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2407_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec(v_a_2394_);
lean_dec(v_a_2386_);
lean_dec(v_maxSuggestions_2372_);
v_a_2447_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2396_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2396_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_dec(v_a_2386_);
lean_dec(v_maxSuggestions_2372_);
return v___x_2393_;
}
}
else
{
lean_dec(v_hint_2375_);
lean_dec_ref(v_filter_2374_);
lean_dec(v_caller_2373_);
lean_dec(v_maxSuggestions_2372_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
lean_dec(v_g_2365_);
lean_dec_ref(v_selector_u2082_2363_);
return v___x_2385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___boxed(lean_object* v_selector_u2081_2457_, lean_object* v_selector_u2082_2458_, lean_object* v_ratio_2459_, lean_object* v_g_2460_, lean_object* v_c_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
double v_ratio_boxed_2467_; lean_object* v_res_2468_; 
v_ratio_boxed_2467_ = lean_unbox_float(v_ratio_2459_);
lean_dec_ref(v_ratio_2459_);
v_res_2468_ = l_Lean_LibrarySuggestions_Selector_intersperse(v_selector_u2081_2457_, v_selector_u2082_2458_, v_ratio_boxed_2467_, v_g_2460_, v_c_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0(double v_ratio_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v___x_2472_, lean_object* v_b_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg(v_ratio_2469_, v_a_2470_, v_a_2471_, v___x_2472_, v_b_2473_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___boxed(lean_object* v_ratio_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v___x_2483_, lean_object* v_b_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
double v_ratio_boxed_2490_; lean_object* v_res_2491_; 
v_ratio_boxed_2490_ = lean_unbox_float(v_ratio_2480_);
lean_dec_ref(v_ratio_2480_);
v_res_2491_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0(v_ratio_boxed_2490_, v_a_2481_, v_a_2482_, v___x_2483_, v_b_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___x_2483_);
lean_dec_ref(v_a_2482_);
lean_dec_ref(v_a_2481_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1(lean_object* v_a_2492_, lean_object* v___x_2493_, lean_object* v_b_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(v_a_2492_, v___x_2493_, v_b_2494_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___boxed(lean_object* v_a_2501_, lean_object* v___x_2502_, lean_object* v_b_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1(v_a_2501_, v___x_2502_, v_b_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___x_2502_);
lean_dec_ref(v_a_2501_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_(lean_object* v_x_2510_, lean_object* v_head_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2512_, 0, v_head_2511_);
lean_ctor_set(v___x_2512_, 1, v_x_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_(lean_object* v_es_2513_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_array_mk(v_es_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_2515_, size_t v_i_2516_, size_t v_stop_2517_, lean_object* v_b_2518_){
_start:
{
uint8_t v___x_2519_; 
v___x_2519_ = lean_usize_dec_eq(v_i_2516_, v_stop_2517_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; size_t v___x_2522_; size_t v___x_2523_; 
v___x_2520_ = lean_array_uget_borrowed(v_as_2515_, v_i_2516_);
lean_inc(v___x_2520_);
v___x_2521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v_b_2518_);
v___x_2522_ = ((size_t)1ULL);
v___x_2523_ = lean_usize_add(v_i_2516_, v___x_2522_);
v_i_2516_ = v___x_2523_;
v_b_2518_ = v___x_2521_;
goto _start;
}
else
{
return v_b_2518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_2525_, lean_object* v_i_2526_, lean_object* v_stop_2527_, lean_object* v_b_2528_){
_start:
{
size_t v_i_boxed_2529_; size_t v_stop_boxed_2530_; lean_object* v_res_2531_; 
v_i_boxed_2529_ = lean_unbox_usize(v_i_2526_);
lean_dec(v_i_2526_);
v_stop_boxed_2530_ = lean_unbox_usize(v_stop_2527_);
lean_dec(v_stop_2527_);
v_res_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0(v_as_2525_, v_i_boxed_2529_, v_stop_boxed_2530_, v_b_2528_);
lean_dec_ref(v_as_2525_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_2532_, size_t v_i_2533_, size_t v_stop_2534_, lean_object* v_b_2535_){
_start:
{
lean_object* v___y_2537_; uint8_t v___x_2541_; 
v___x_2541_ = lean_usize_dec_eq(v_i_2533_, v_stop_2534_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2542_ = lean_array_uget_borrowed(v_as_2532_, v_i_2533_);
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = lean_array_get_size(v___x_2542_);
v___x_2545_ = lean_nat_dec_lt(v___x_2543_, v___x_2544_);
if (v___x_2545_ == 0)
{
v___y_2537_ = v_b_2535_;
goto v___jp_2536_;
}
else
{
uint8_t v___x_2546_; 
v___x_2546_ = lean_nat_dec_le(v___x_2544_, v___x_2544_);
if (v___x_2546_ == 0)
{
if (v___x_2545_ == 0)
{
v___y_2537_ = v_b_2535_;
goto v___jp_2536_;
}
else
{
size_t v___x_2547_; size_t v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = ((size_t)0ULL);
v___x_2548_ = lean_usize_of_nat(v___x_2544_);
v___x_2549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0(v___x_2542_, v___x_2547_, v___x_2548_, v_b_2535_);
v___y_2537_ = v___x_2549_;
goto v___jp_2536_;
}
}
else
{
size_t v___x_2550_; size_t v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = ((size_t)0ULL);
v___x_2551_ = lean_usize_of_nat(v___x_2544_);
v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0(v___x_2542_, v___x_2550_, v___x_2551_, v_b_2535_);
v___y_2537_ = v___x_2552_;
goto v___jp_2536_;
}
}
}
else
{
return v_b_2535_;
}
v___jp_2536_:
{
size_t v___x_2538_; size_t v___x_2539_; 
v___x_2538_ = ((size_t)1ULL);
v___x_2539_ = lean_usize_add(v_i_2533_, v___x_2538_);
v_i_2533_ = v___x_2539_;
v_b_2535_ = v___y_2537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_2553_, lean_object* v_i_2554_, lean_object* v_stop_2555_, lean_object* v_b_2556_){
_start:
{
size_t v_i_boxed_2557_; size_t v_stop_boxed_2558_; lean_object* v_res_2559_; 
v_i_boxed_2557_ = lean_unbox_usize(v_i_2554_);
lean_dec(v_i_2554_);
v_stop_boxed_2558_ = lean_unbox_usize(v_stop_2555_);
lean_dec(v_stop_2555_);
v_res_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1(v_as_2553_, v_i_boxed_2557_, v_stop_boxed_2558_, v_b_2556_);
lean_dec_ref(v_as_2553_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0(lean_object* v_initState_2560_, lean_object* v_as_2561_){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2562_ = lean_unsigned_to_nat(0u);
v___x_2563_ = lean_array_get_size(v_as_2561_);
v___x_2564_ = lean_nat_dec_lt(v___x_2562_, v___x_2563_);
if (v___x_2564_ == 0)
{
return v_initState_2560_;
}
else
{
uint8_t v___x_2565_; 
v___x_2565_ = lean_nat_dec_le(v___x_2563_, v___x_2563_);
if (v___x_2565_ == 0)
{
if (v___x_2564_ == 0)
{
return v_initState_2560_;
}
else
{
size_t v___x_2566_; size_t v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = ((size_t)0ULL);
v___x_2567_ = lean_usize_of_nat(v___x_2563_);
v___x_2568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1(v_as_2561_, v___x_2566_, v___x_2567_, v_initState_2560_);
return v___x_2568_;
}
}
else
{
size_t v___x_2569_; size_t v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = ((size_t)0ULL);
v___x_2570_ = lean_usize_of_nat(v___x_2563_);
v___x_2571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1(v_as_2561_, v___x_2569_, v___x_2570_, v_initState_2560_);
return v___x_2571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_2572_, lean_object* v_as_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0(v_initState_2572_, v_as_2573_);
lean_dec_ref(v_as_2573_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__14_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_));
v___x_2610_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2____boxed(lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_();
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_));
v___x_2627_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2626_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2____boxed(lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_();
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_(lean_object* v_x_2630_, lean_object* v_head_2631_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2632_, 0, v_head_2631_);
lean_ctor_set(v___x_2632_, 1, v_x_2630_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_(lean_object* v_es_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_array_mk(v_es_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_2635_, size_t v_i_2636_, size_t v_stop_2637_, lean_object* v_b_2638_){
_start:
{
uint8_t v___x_2639_; 
v___x_2639_ = lean_usize_dec_eq(v_i_2636_, v_stop_2637_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; size_t v___x_2642_; size_t v___x_2643_; 
v___x_2640_ = lean_array_uget_borrowed(v_as_2635_, v_i_2636_);
lean_inc(v___x_2640_);
v___x_2641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
lean_ctor_set(v___x_2641_, 1, v_b_2638_);
v___x_2642_ = ((size_t)1ULL);
v___x_2643_ = lean_usize_add(v_i_2636_, v___x_2642_);
v_i_2636_ = v___x_2643_;
v_b_2638_ = v___x_2641_;
goto _start;
}
else
{
return v_b_2638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_2645_, lean_object* v_i_2646_, lean_object* v_stop_2647_, lean_object* v_b_2648_){
_start:
{
size_t v_i_boxed_2649_; size_t v_stop_boxed_2650_; lean_object* v_res_2651_; 
v_i_boxed_2649_ = lean_unbox_usize(v_i_2646_);
lean_dec(v_i_2646_);
v_stop_boxed_2650_ = lean_unbox_usize(v_stop_2647_);
lean_dec(v_stop_2647_);
v_res_2651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0(v_as_2645_, v_i_boxed_2649_, v_stop_boxed_2650_, v_b_2648_);
lean_dec_ref(v_as_2645_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_2652_, size_t v_i_2653_, size_t v_stop_2654_, lean_object* v_b_2655_){
_start:
{
lean_object* v___y_2657_; uint8_t v___x_2661_; 
v___x_2661_ = lean_usize_dec_eq(v_i_2653_, v_stop_2654_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2662_ = lean_array_uget_borrowed(v_as_2652_, v_i_2653_);
v___x_2663_ = lean_unsigned_to_nat(0u);
v___x_2664_ = lean_array_get_size(v___x_2662_);
v___x_2665_ = lean_nat_dec_lt(v___x_2663_, v___x_2664_);
if (v___x_2665_ == 0)
{
v___y_2657_ = v_b_2655_;
goto v___jp_2656_;
}
else
{
uint8_t v___x_2666_; 
v___x_2666_ = lean_nat_dec_le(v___x_2664_, v___x_2664_);
if (v___x_2666_ == 0)
{
if (v___x_2665_ == 0)
{
v___y_2657_ = v_b_2655_;
goto v___jp_2656_;
}
else
{
size_t v___x_2667_; size_t v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = ((size_t)0ULL);
v___x_2668_ = lean_usize_of_nat(v___x_2664_);
v___x_2669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0(v___x_2662_, v___x_2667_, v___x_2668_, v_b_2655_);
v___y_2657_ = v___x_2669_;
goto v___jp_2656_;
}
}
else
{
size_t v___x_2670_; size_t v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = ((size_t)0ULL);
v___x_2671_ = lean_usize_of_nat(v___x_2664_);
v___x_2672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0(v___x_2662_, v___x_2670_, v___x_2671_, v_b_2655_);
v___y_2657_ = v___x_2672_;
goto v___jp_2656_;
}
}
}
else
{
return v_b_2655_;
}
v___jp_2656_:
{
size_t v___x_2658_; size_t v___x_2659_; 
v___x_2658_ = ((size_t)1ULL);
v___x_2659_ = lean_usize_add(v_i_2653_, v___x_2658_);
v_i_2653_ = v___x_2659_;
v_b_2655_ = v___y_2657_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_2673_, lean_object* v_i_2674_, lean_object* v_stop_2675_, lean_object* v_b_2676_){
_start:
{
size_t v_i_boxed_2677_; size_t v_stop_boxed_2678_; lean_object* v_res_2679_; 
v_i_boxed_2677_ = lean_unbox_usize(v_i_2674_);
lean_dec(v_i_2674_);
v_stop_boxed_2678_ = lean_unbox_usize(v_stop_2675_);
lean_dec(v_stop_2675_);
v_res_2679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1(v_as_2673_, v_i_boxed_2677_, v_stop_boxed_2678_, v_b_2676_);
lean_dec_ref(v_as_2673_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0(lean_object* v_initState_2680_, lean_object* v_as_2681_){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; 
v___x_2682_ = lean_unsigned_to_nat(0u);
v___x_2683_ = lean_array_get_size(v_as_2681_);
v___x_2684_ = lean_nat_dec_lt(v___x_2682_, v___x_2683_);
if (v___x_2684_ == 0)
{
return v_initState_2680_;
}
else
{
uint8_t v___x_2685_; 
v___x_2685_ = lean_nat_dec_le(v___x_2683_, v___x_2683_);
if (v___x_2685_ == 0)
{
if (v___x_2684_ == 0)
{
return v_initState_2680_;
}
else
{
size_t v___x_2686_; size_t v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = ((size_t)0ULL);
v___x_2687_ = lean_usize_of_nat(v___x_2683_);
v___x_2688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1(v_as_2681_, v___x_2686_, v___x_2687_, v_initState_2680_);
return v___x_2688_;
}
}
else
{
size_t v___x_2689_; size_t v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = ((size_t)0ULL);
v___x_2690_ = lean_usize_of_nat(v___x_2683_);
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1(v_as_2681_, v___x_2689_, v___x_2690_, v_initState_2680_);
return v___x_2691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_2692_, lean_object* v_as_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0(v_initState_2692_, v_as_2693_);
lean_dec_ref(v_as_2693_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_));
v___x_2723_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2____boxed(lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_();
return v_res_2725_;
}
}
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedModule___lam__0(lean_object* v_p_2726_, lean_object* v_x_2727_){
_start:
{
uint8_t v___x_2728_; 
v___x_2728_ = lean_string_dec_eq(v_x_2727_, v_p_2726_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedModule___lam__0___boxed(lean_object* v_p_2729_, lean_object* v_x_2730_){
_start:
{
uint8_t v_res_2731_; lean_object* v_r_2732_; 
v_res_2731_ = l_Lean_LibrarySuggestions_isDeniedModule___lam__0(v_p_2729_, v_x_2730_);
lean_dec_ref(v_x_2730_);
lean_dec_ref(v_p_2729_);
v_r_2732_ = lean_box(v_res_2731_);
return v_r_2732_;
}
}
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedModule___lam__1(lean_object* v_moduleName_2733_, lean_object* v_p_2734_){
_start:
{
lean_object* v___f_2735_; uint8_t v___x_2736_; 
v___f_2735_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_isDeniedModule___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2735_, 0, v_p_2734_);
v___x_2736_ = l_Lean_Name_anyS(v_moduleName_2733_, v___f_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedModule___lam__1___boxed(lean_object* v_moduleName_2737_, lean_object* v_p_2738_){
_start:
{
uint8_t v_res_2739_; lean_object* v_r_2740_; 
v_res_2739_ = l_Lean_LibrarySuggestions_isDeniedModule___lam__1(v_moduleName_2737_, v_p_2738_);
v_r_2740_ = lean_box(v_res_2739_);
return v_r_2740_;
}
}
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedModule(lean_object* v_env_2741_, lean_object* v_moduleName_2742_){
_start:
{
lean_object* v___x_2743_; lean_object* v_toEnvExtension_2744_; lean_object* v_asyncMode_2745_; lean_object* v___f_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2743_ = l_Lean_LibrarySuggestions_moduleDenyListExt;
v_toEnvExtension_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc_ref(v_toEnvExtension_2744_);
v_asyncMode_2745_ = lean_ctor_get(v_toEnvExtension_2744_, 2);
lean_inc(v_asyncMode_2745_);
lean_dec_ref(v_toEnvExtension_2744_);
v___f_2746_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_isDeniedModule___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2746_, 0, v_moduleName_2742_);
v___x_2747_ = lean_box(0);
v___x_2748_ = lean_box(0);
v___x_2749_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2747_, v___x_2743_, v_env_2741_, v_asyncMode_2745_, v___x_2748_);
lean_dec(v_asyncMode_2745_);
v___x_2750_ = l_List_any___redArg(v___x_2749_, v___f_2746_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedModule___boxed(lean_object* v_env_2751_, lean_object* v_moduleName_2752_){
_start:
{
uint8_t v_res_2753_; lean_object* v_r_2754_; 
v_res_2753_ = l_Lean_LibrarySuggestions_isDeniedModule(v_env_2751_, v_moduleName_2752_);
v_r_2754_ = lean_box(v_res_2753_);
return v_r_2754_;
}
}
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedPremise___lam__1(lean_object* v_name_2755_, lean_object* v_p_2756_){
_start:
{
lean_object* v___f_2757_; uint8_t v___x_2758_; 
v___f_2757_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_isDeniedModule___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2757_, 0, v_p_2756_);
v___x_2758_ = l_Lean_Name_anyS(v_name_2755_, v___f_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___lam__1___boxed(lean_object* v_name_2759_, lean_object* v_p_2760_){
_start:
{
uint8_t v_res_2761_; lean_object* v_r_2762_; 
v_res_2761_ = l_Lean_LibrarySuggestions_isDeniedPremise___lam__1(v_name_2759_, v_p_2760_);
v_r_2762_ = lean_box(v_res_2761_);
return v_r_2762_;
}
}
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedPremise___lam__0(lean_object* v_declName_2763_, lean_object* v_p_2764_){
_start:
{
uint8_t v___x_2765_; 
v___x_2765_ = l_Lean_Name_isPrefixOf(v_p_2764_, v_declName_2763_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___lam__0___boxed(lean_object* v_declName_2766_, lean_object* v_p_2767_){
_start:
{
uint8_t v_res_2768_; lean_object* v_r_2769_; 
v_res_2768_ = l_Lean_LibrarySuggestions_isDeniedPremise___lam__0(v_declName_2766_, v_p_2767_);
lean_dec(v_p_2767_);
lean_dec(v_declName_2766_);
v_r_2769_ = lean_box(v_res_2768_);
return v_r_2769_;
}
}
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedPremise(lean_object* v_env_2773_, lean_object* v_name_2774_, uint8_t v_allowPrivate_2775_){
_start:
{
lean_object* v___x_2776_; uint8_t v___x_2777_; uint8_t v___x_2778_; lean_object* v___y_2780_; uint8_t v___y_2781_; 
v___x_2776_ = ((lean_object*)(l_Lean_LibrarySuggestions_isDeniedPremise___closed__1));
v___x_2777_ = lean_name_eq(v_name_2774_, v___x_2776_);
v___x_2778_ = 1;
if (v___x_2777_ == 0)
{
lean_object* v___f_2795_; uint8_t v___y_2797_; uint8_t v___x_2813_; 
lean_inc(v_name_2774_);
v___f_2795_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_isDeniedPremise___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2795_, 0, v_name_2774_);
lean_inc(v_name_2774_);
v___x_2813_ = l_Lean_Name_isInternalDetail(v_name_2774_);
if (v___x_2813_ == 0)
{
v___y_2797_ = v___x_2813_;
goto v___jp_2796_;
}
else
{
if (v_allowPrivate_2775_ == 0)
{
v___y_2797_ = v___x_2813_;
goto v___jp_2796_;
}
else
{
uint8_t v___x_2814_; 
v___x_2814_ = l_Lean_isPrivateName(v_name_2774_);
if (v___x_2814_ == 0)
{
v___y_2797_ = v___x_2813_;
goto v___jp_2796_;
}
else
{
v___y_2797_ = v___x_2777_;
goto v___jp_2796_;
}
}
}
v___jp_2796_:
{
if (v___y_2797_ == 0)
{
uint8_t v___x_2798_; 
lean_inc(v_name_2774_);
lean_inc_ref(v_env_2773_);
v___x_2798_ = l_Lean_isImplicitReducibleCore(v_env_2773_, v_name_2774_);
if (v___x_2798_ == 0)
{
uint8_t v___x_2799_; 
lean_inc(v_name_2774_);
lean_inc_ref(v_env_2773_);
v___x_2799_ = l_Lean_Linter_isDeprecated(v_env_2773_, v_name_2774_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; lean_object* v_toEnvExtension_2801_; lean_object* v_asyncMode_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2800_ = l_Lean_LibrarySuggestions_nameDenyListExt;
v_toEnvExtension_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc_ref(v_toEnvExtension_2801_);
v_asyncMode_2802_ = lean_ctor_get(v_toEnvExtension_2801_, 2);
lean_inc(v_asyncMode_2802_);
lean_dec_ref(v_toEnvExtension_2801_);
v___x_2803_ = lean_box(0);
v___x_2804_ = lean_box(0);
lean_inc_ref(v_env_2773_);
v___x_2805_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2803_, v___x_2800_, v_env_2773_, v_asyncMode_2802_, v___x_2804_);
lean_dec(v_asyncMode_2802_);
v___x_2806_ = l_List_any___redArg(v___x_2805_, v___f_2795_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2773_, v_name_2774_);
if (lean_obj_tag(v___x_2807_) == 1)
{
lean_object* v_val_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v_moduleName_2811_; uint8_t v___x_2812_; 
v_val_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_val_2808_);
lean_dec_ref(v___x_2807_);
v___x_2809_ = l_Lean_Environment_header(v_env_2773_);
v___x_2810_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2809_);
v_moduleName_2811_ = lean_array_get(v___x_2804_, v___x_2810_, v_val_2808_);
lean_dec(v_val_2808_);
lean_dec_ref(v___x_2810_);
lean_inc_ref(v_env_2773_);
v___x_2812_ = l_Lean_LibrarySuggestions_isDeniedModule(v_env_2773_, v_moduleName_2811_);
if (v___x_2812_ == 0)
{
v___y_2780_ = v___x_2804_;
v___y_2781_ = v___x_2806_;
goto v___jp_2779_;
}
else
{
lean_dec(v_name_2774_);
lean_dec_ref(v_env_2773_);
return v___x_2778_;
}
}
else
{
lean_dec(v___x_2807_);
v___y_2780_ = v___x_2804_;
v___y_2781_ = v___x_2806_;
goto v___jp_2779_;
}
}
else
{
lean_dec(v_name_2774_);
lean_dec_ref(v_env_2773_);
return v___x_2778_;
}
}
else
{
lean_dec_ref(v___f_2795_);
lean_dec(v_name_2774_);
lean_dec_ref(v_env_2773_);
return v___x_2778_;
}
}
else
{
lean_dec_ref(v___f_2795_);
lean_dec(v_name_2774_);
lean_dec_ref(v_env_2773_);
return v___x_2778_;
}
}
else
{
lean_dec_ref(v___f_2795_);
lean_dec(v_name_2774_);
lean_dec_ref(v_env_2773_);
return v___x_2778_;
}
}
}
else
{
lean_dec(v_name_2774_);
lean_dec_ref(v_env_2773_);
return v___x_2778_;
}
v___jp_2779_:
{
lean_object* v___x_2782_; 
lean_inc_ref(v_env_2773_);
v___x_2782_ = l_Lean_Environment_find_x3f(v_env_2773_, v_name_2774_, v___y_2781_);
if (lean_obj_tag(v___x_2782_) == 1)
{
lean_object* v_val_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_val_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_val_2783_);
lean_dec_ref(v___x_2782_);
v___x_2784_ = l_Lean_ConstantInfo_type(v_val_2783_);
lean_dec(v_val_2783_);
v___x_2785_ = l_Lean_Expr_getForallBody(v___x_2784_);
lean_dec_ref(v___x_2784_);
v___x_2786_ = l_Lean_Expr_getAppFn(v___x_2785_);
lean_dec_ref(v___x_2785_);
if (lean_obj_tag(v___x_2786_) == 4)
{
lean_object* v_declName_2787_; lean_object* v___x_2788_; lean_object* v_toEnvExtension_2789_; lean_object* v_asyncMode_2790_; lean_object* v___f_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; 
v_declName_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_declName_2787_);
lean_dec_ref(v___x_2786_);
v___x_2788_ = l_Lean_LibrarySuggestions_typePrefixDenyListExt;
v_toEnvExtension_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc_ref(v_toEnvExtension_2789_);
v_asyncMode_2790_ = lean_ctor_get(v_toEnvExtension_2789_, 2);
lean_inc(v_asyncMode_2790_);
lean_dec_ref(v_toEnvExtension_2789_);
v___f_2791_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_isDeniedPremise___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2791_, 0, v_declName_2787_);
v___x_2792_ = lean_box(0);
v___x_2793_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2792_, v___x_2788_, v_env_2773_, v_asyncMode_2790_, v___y_2780_);
lean_dec(v_asyncMode_2790_);
v___x_2794_ = l_List_any___redArg(v___x_2793_, v___f_2791_);
if (v___x_2794_ == 0)
{
return v___x_2794_;
}
else
{
return v___x_2778_;
}
}
else
{
lean_dec_ref(v___x_2786_);
lean_dec(v___y_2780_);
lean_dec_ref(v_env_2773_);
return v___y_2781_;
}
}
else
{
lean_dec(v___x_2782_);
lean_dec(v___y_2780_);
lean_dec_ref(v_env_2773_);
return v___x_2778_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___boxed(lean_object* v_env_2815_, lean_object* v_name_2816_, lean_object* v_allowPrivate_2817_){
_start:
{
uint8_t v_allowPrivate_boxed_2818_; uint8_t v_res_2819_; lean_object* v_r_2820_; 
v_allowPrivate_boxed_2818_ = lean_unbox(v_allowPrivate_2817_);
v_res_2819_ = l_Lean_LibrarySuggestions_isDeniedPremise(v_env_2815_, v_name_2816_, v_allowPrivate_boxed_2818_);
v_r_2820_ = lean_box(v_res_2819_);
return v_r_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty___redArg(){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = ((lean_object*)(l_Lean_LibrarySuggestions_Selector_postFilter___closed__1));
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty___redArg___boxed(lean_object* v_a_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_LibrarySuggestions_empty___redArg();
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty(lean_object* v_x_2826_, lean_object* v_x_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_LibrarySuggestions_empty___redArg();
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty___boxed(lean_object* v_x_2834_, lean_object* v_x_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_LibrarySuggestions_empty(v_x_2834_, v_x_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec_ref(v_x_2835_);
lean_dec(v_x_2834_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg(lean_object* v___x_2842_, lean_object* v___y_2843_, lean_object* v___x_2844_, lean_object* v_b_2845_){
_start:
{
lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2847_ = lean_array_get_size(v_b_2845_);
v___x_2848_ = lean_nat_dec_lt(v___x_2847_, v___x_2842_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; 
lean_dec_ref(v___x_2844_);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v_b_2845_);
return v___x_2849_;
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; uint8_t v___x_2856_; 
v___x_2850_ = lean_unsigned_to_nat(0u);
v___x_2851_ = lean_array_get_size(v___y_2843_);
v___x_2852_ = l_IO_rand(v___x_2850_, v___x_2851_);
v___x_2853_ = lean_box(0);
v___x_2854_ = lean_array_get_borrowed(v___x_2853_, v___y_2843_, v___x_2852_);
lean_dec(v___x_2852_);
v___x_2855_ = 0;
lean_inc(v___x_2854_);
lean_inc_ref(v___x_2844_);
v___x_2856_ = l_Lean_LibrarySuggestions_isDeniedPremise(v___x_2844_, v___x_2854_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; lean_object* v___x_2858_; double v___x_2859_; double v___x_2860_; double v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2857_ = lean_unsigned_to_nat(10u);
v___x_2858_ = lean_unsigned_to_nat(1u);
v___x_2859_ = l_Float_ofScientific(v___x_2857_, v___x_2848_, v___x_2858_);
v___x_2860_ = lean_float_of_nat(v___x_2851_);
v___x_2861_ = lean_float_div(v___x_2859_, v___x_2860_);
v___x_2862_ = lean_box(0);
lean_inc(v___x_2854_);
v___x_2863_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_2863_, 0, v___x_2854_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
lean_ctor_set_float(v___x_2863_, sizeof(void*)*2, v___x_2861_);
v___x_2864_ = lean_array_push(v_b_2845_, v___x_2863_);
v_b_2845_ = v___x_2864_;
goto _start;
}
else
{
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg___boxed(lean_object* v___x_2867_, lean_object* v___y_2868_, lean_object* v___x_2869_, lean_object* v_b_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg(v___x_2867_, v___y_2868_, v___x_2869_, v_b_2870_);
lean_dec_ref(v___y_2868_);
lean_dec(v___x_2867_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_random_spec__1(lean_object* v_x_2873_, lean_object* v_x_2874_){
_start:
{
if (lean_obj_tag(v_x_2874_) == 0)
{
return v_x_2873_;
}
else
{
lean_object* v_key_2875_; lean_object* v_tail_2876_; lean_object* v___x_2877_; 
v_key_2875_ = lean_ctor_get(v_x_2874_, 0);
lean_inc(v_key_2875_);
v_tail_2876_ = lean_ctor_get(v_x_2874_, 2);
lean_inc(v_tail_2876_);
lean_dec_ref(v_x_2874_);
v___x_2877_ = lean_array_push(v_x_2873_, v_key_2875_);
v_x_2873_ = v___x_2877_;
v_x_2874_ = v_tail_2876_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2(lean_object* v_as_2879_, size_t v_i_2880_, size_t v_stop_2881_, lean_object* v_b_2882_){
_start:
{
uint8_t v___x_2883_; 
v___x_2883_ = lean_usize_dec_eq(v_i_2880_, v_stop_2881_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; lean_object* v___x_2885_; size_t v___x_2886_; size_t v___x_2887_; 
v___x_2884_ = lean_array_uget_borrowed(v_as_2879_, v_i_2880_);
lean_inc(v___x_2884_);
v___x_2885_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_random_spec__1(v_b_2882_, v___x_2884_);
v___x_2886_ = ((size_t)1ULL);
v___x_2887_ = lean_usize_add(v_i_2880_, v___x_2886_);
v_i_2880_ = v___x_2887_;
v_b_2882_ = v___x_2885_;
goto _start;
}
else
{
return v_b_2882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2___boxed(lean_object* v_as_2889_, lean_object* v_i_2890_, lean_object* v_stop_2891_, lean_object* v_b_2892_){
_start:
{
size_t v_i_boxed_2893_; size_t v_stop_boxed_2894_; lean_object* v_res_2895_; 
v_i_boxed_2893_ = lean_unbox_usize(v_i_2890_);
lean_dec(v_i_2890_);
v_stop_boxed_2894_ = lean_unbox_usize(v_stop_2891_);
lean_dec(v_stop_2891_);
v_res_2895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2(v_as_2889_, v_i_boxed_2893_, v_stop_boxed_2894_, v_b_2892_);
lean_dec_ref(v_as_2889_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random___redArg(lean_object* v_gen_2896_, lean_object* v_cfg_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v_env_2906_; lean_object* v_maxSuggestions_2907_; lean_object* v___y_2909_; lean_object* v___x_2912_; lean_object* v_size_2913_; lean_object* v_buckets_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
v___x_2903_ = l_IO_stdGenRef;
v___x_2904_ = lean_st_ref_set(v___x_2903_, v_gen_2896_);
v___x_2905_ = lean_st_ref_get(v_a_2901_);
v_env_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc_ref(v_env_2906_);
lean_dec(v___x_2905_);
v_maxSuggestions_2907_ = lean_ctor_get(v_cfg_2897_, 0);
lean_inc_ref(v_env_2906_);
v___x_2912_ = l_Lean_Environment_const2ModIdx(v_env_2906_);
v_size_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_size_2913_);
v_buckets_2914_ = lean_ctor_get(v___x_2912_, 1);
lean_inc_ref(v_buckets_2914_);
lean_dec_ref(v___x_2912_);
v___x_2915_ = lean_mk_empty_array_with_capacity(v_size_2913_);
lean_dec(v_size_2913_);
v___x_2916_ = lean_unsigned_to_nat(0u);
v___x_2917_ = lean_array_get_size(v_buckets_2914_);
v___x_2918_ = lean_nat_dec_lt(v___x_2916_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_dec_ref(v_buckets_2914_);
v___y_2909_ = v___x_2915_;
goto v___jp_2908_;
}
else
{
uint8_t v___x_2919_; 
v___x_2919_ = lean_nat_dec_le(v___x_2917_, v___x_2917_);
if (v___x_2919_ == 0)
{
if (v___x_2918_ == 0)
{
lean_dec_ref(v_buckets_2914_);
v___y_2909_ = v___x_2915_;
goto v___jp_2908_;
}
else
{
size_t v___x_2920_; size_t v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = ((size_t)0ULL);
v___x_2921_ = lean_usize_of_nat(v___x_2917_);
v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2(v_buckets_2914_, v___x_2920_, v___x_2921_, v___x_2915_);
lean_dec_ref(v_buckets_2914_);
v___y_2909_ = v___x_2922_;
goto v___jp_2908_;
}
}
else
{
size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = ((size_t)0ULL);
v___x_2924_ = lean_usize_of_nat(v___x_2917_);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2(v_buckets_2914_, v___x_2923_, v___x_2924_, v___x_2915_);
lean_dec_ref(v_buckets_2914_);
v___y_2909_ = v___x_2925_;
goto v___jp_2908_;
}
}
v___jp_2908_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = ((lean_object*)(l_Lean_LibrarySuggestions_Selector_postFilter___closed__1));
v___x_2911_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg(v_maxSuggestions_2907_, v___y_2909_, v_env_2906_, v___x_2910_);
lean_dec_ref(v___y_2909_);
return v___x_2911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random___redArg___boxed(lean_object* v_gen_2926_, lean_object* v_cfg_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_LibrarySuggestions_random___redArg(v_gen_2926_, v_cfg_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec_ref(v_cfg_2927_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random(lean_object* v_gen_2934_, lean_object* v_x_2935_, lean_object* v_cfg_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_LibrarySuggestions_random___redArg(v_gen_2934_, v_cfg_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random___boxed(lean_object* v_gen_2943_, lean_object* v_x_2944_, lean_object* v_cfg_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_LibrarySuggestions_random(v_gen_2943_, v_x_2944_, v_cfg_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_);
lean_dec(v_a_2949_);
lean_dec_ref(v_a_2948_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec_ref(v_cfg_2945_);
lean_dec(v_x_2944_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0(lean_object* v___x_2952_, lean_object* v___y_2953_, lean_object* v___x_2954_, lean_object* v_b_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg(v___x_2952_, v___y_2953_, v___x_2954_, v_b_2955_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___boxed(lean_object* v___x_2962_, lean_object* v___y_2963_, lean_object* v___x_2964_, lean_object* v_b_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0(v___x_2962_, v___y_2963_, v___x_2964_, v_b_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec_ref(v___y_2963_);
lean_dec(v___x_2962_);
return v_res_2971_;
}
}
static double _init_l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; double v___x_2975_; 
v___x_2972_ = lean_unsigned_to_nat(1u);
v___x_2973_ = 1;
v___x_2974_ = lean_unsigned_to_nat(10u);
v___x_2975_ = l_Float_ofScientific(v___x_2974_, v___x_2973_, v___x_2972_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg___lam__0(lean_object* v_maxSuggestions_2976_, lean_object* v_env_2977_, lean_object* v_x_2978_, lean_object* v_____s_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_fst_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v_fst_2985_ = lean_ctor_get(v_x_2978_, 0);
lean_inc(v_fst_2985_);
lean_dec_ref(v_x_2978_);
v___x_2986_ = lean_array_get_size(v_____s_2979_);
v___x_2987_ = lean_nat_dec_le(v_maxSuggestions_2976_, v___x_2986_);
if (v___x_2987_ == 0)
{
uint8_t v___x_2988_; uint8_t v___x_2989_; 
v___x_2988_ = 1;
lean_inc(v_fst_2985_);
lean_inc_ref(v_env_2977_);
v___x_2989_ = l_Lean_LibrarySuggestions_isDeniedPremise(v_env_2977_, v_fst_2985_, v___x_2988_);
if (v___x_2989_ == 0)
{
uint8_t v___x_2990_; 
lean_inc(v_fst_2985_);
v___x_2990_ = l_Lean_wasOriginallyTheorem(v_env_2977_, v_fst_2985_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_dec(v_fst_2985_);
v___x_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2991_, 0, v_____s_2979_);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
else
{
double v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2993_ = lean_float_once(&l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___closed__0, &l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___closed__0_once, _init_l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___closed__0);
v___x_2994_ = lean_box(0);
v___x_2995_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_2995_, 0, v_fst_2985_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
lean_ctor_set_float(v___x_2995_, sizeof(void*)*2, v___x_2993_);
v___x_2996_ = lean_array_push(v_____s_2979_, v___x_2995_);
v___x_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_dec(v_fst_2985_);
lean_dec_ref(v_env_2977_);
v___x_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2999_, 0, v_____s_2979_);
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
return v___x_3000_;
}
}
else
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
lean_dec(v_fst_2985_);
lean_dec_ref(v_env_2977_);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_____s_2979_);
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
return v___x_3002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___boxed(lean_object* v_maxSuggestions_3003_, lean_object* v_env_3004_, lean_object* v_x_3005_, lean_object* v_____s_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_LibrarySuggestions_currentFile___redArg___lam__0(v_maxSuggestions_3003_, v_env_3004_, v_x_3005_, v_____s_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v_maxSuggestions_3003_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___lam__0(lean_object* v_f_3013_, lean_object* v_s_3014_, lean_object* v_a_3015_, lean_object* v_b_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v_a_3015_);
lean_ctor_set(v___x_3022_, 1, v_b_3016_);
v___x_3023_ = lean_apply_7(v_f_3013_, v___x_3022_, v_s_3014_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, lean_box(0));
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3050_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3050_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3050_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
if (lean_obj_tag(v_a_3024_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3038_; 
v_a_3028_ = lean_ctor_get(v_a_3024_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_a_3024_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3030_ = v_a_3024_;
v_isShared_3031_ = v_isSharedCheck_3038_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v_a_3024_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3038_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3035_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3033_);
v___x_3035_ = v___x_3026_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3049_; 
v_a_3039_ = lean_ctor_get(v_a_3024_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v_a_3024_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3041_ = v_a_3024_;
v_isShared_3042_ = v_isSharedCheck_3049_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v_a_3024_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3049_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3046_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3044_);
v___x_3046_ = v___x_3026_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
v_a_3051_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3023_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3023_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___lam__0___boxed(lean_object* v_f_3059_, lean_object* v_s_3060_, lean_object* v_a_3061_, lean_object* v_b_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___lam__0(v_f_3059_, v_s_3060_, v_a_3061_, v_b_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3069_, lean_object* v_keys_3070_, lean_object* v_vals_3071_, lean_object* v_i_3072_, lean_object* v_acc_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = lean_array_get_size(v_keys_3070_);
v___x_3080_ = lean_nat_dec_lt(v_i_3072_, v___x_3079_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v_i_3072_);
lean_dec_ref(v_f_3069_);
v___x_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3081_, 0, v_acc_3073_);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
return v___x_3082_;
}
else
{
lean_object* v_k_3083_; lean_object* v_v_3084_; lean_object* v___x_3085_; 
v_k_3083_ = lean_array_fget_borrowed(v_keys_3070_, v_i_3072_);
v_v_3084_ = lean_array_fget_borrowed(v_vals_3071_, v_i_3072_);
lean_inc_ref(v_f_3069_);
lean_inc(v___y_3077_);
lean_inc_ref(v___y_3076_);
lean_inc(v___y_3075_);
lean_inc_ref(v___y_3074_);
lean_inc(v_v_3084_);
lean_inc(v_k_3083_);
v___x_3085_ = lean_apply_8(v_f_3069_, v_acc_3073_, v_k_3083_, v_v_3084_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, lean_box(0));
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
if (lean_obj_tag(v_a_3086_) == 0)
{
lean_dec_ref(v_a_3086_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v_i_3072_);
lean_dec_ref(v_f_3069_);
return v___x_3085_;
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_dec_ref(v___x_3085_);
v_a_3087_ = lean_ctor_get(v_a_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref(v_a_3086_);
v___x_3088_ = lean_unsigned_to_nat(1u);
v___x_3089_ = lean_nat_add(v_i_3072_, v___x_3088_);
lean_dec(v_i_3072_);
v_i_3072_ = v___x_3089_;
v_acc_3073_ = v_a_3087_;
goto _start;
}
}
else
{
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v_i_3072_);
lean_dec_ref(v_f_3069_);
return v___x_3085_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3091_, lean_object* v_keys_3092_, lean_object* v_vals_3093_, lean_object* v_i_3094_, lean_object* v_acc_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3091_, v_keys_3092_, v_vals_3093_, v_i_3094_, v_acc_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
lean_dec_ref(v_vals_3093_);
lean_dec_ref(v_keys_3092_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3102_, lean_object* v_x_3103_, lean_object* v_x_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
if (lean_obj_tag(v_x_3103_) == 0)
{
lean_object* v_es_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3132_; 
v_es_3110_ = lean_ctor_get(v_x_3103_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_x_3103_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3112_ = v_x_3103_;
v_isShared_3113_ = v_isSharedCheck_3132_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_es_3110_);
lean_dec(v_x_3103_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3132_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3114_ = lean_unsigned_to_nat(0u);
v___x_3115_ = lean_array_get_size(v_es_3110_);
v___x_3116_ = lean_nat_dec_lt(v___x_3114_, v___x_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3118_; 
lean_dec_ref(v_es_3110_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec_ref(v_f_3102_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set_tag(v___x_3112_, 1);
lean_ctor_set(v___x_3112_, 0, v_x_3104_);
v___x_3118_ = v___x_3112_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_x_3104_);
v___x_3118_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
return v___x_3119_;
}
}
else
{
uint8_t v___x_3121_; 
v___x_3121_ = lean_nat_dec_le(v___x_3115_, v___x_3115_);
if (v___x_3121_ == 0)
{
if (v___x_3116_ == 0)
{
lean_object* v___x_3123_; 
lean_dec_ref(v_es_3110_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec_ref(v_f_3102_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set_tag(v___x_3112_, 1);
lean_ctor_set(v___x_3112_, 0, v_x_3104_);
v___x_3123_ = v___x_3112_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_x_3104_);
v___x_3123_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
return v___x_3124_;
}
}
else
{
size_t v___x_3126_; size_t v___x_3127_; lean_object* v___x_3128_; 
lean_del_object(v___x_3112_);
v___x_3126_ = ((size_t)0ULL);
v___x_3127_ = lean_usize_of_nat(v___x_3115_);
v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3102_, v_es_3110_, v___x_3126_, v___x_3127_, v_x_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec_ref(v_es_3110_);
return v___x_3128_;
}
}
else
{
size_t v___x_3129_; size_t v___x_3130_; lean_object* v___x_3131_; 
lean_del_object(v___x_3112_);
v___x_3129_ = ((size_t)0ULL);
v___x_3130_ = lean_usize_of_nat(v___x_3115_);
v___x_3131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3102_, v_es_3110_, v___x_3129_, v___x_3130_, v_x_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec_ref(v_es_3110_);
return v___x_3131_;
}
}
}
}
else
{
lean_object* v_ks_3133_; lean_object* v_vs_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v_ks_3133_ = lean_ctor_get(v_x_3103_, 0);
lean_inc_ref(v_ks_3133_);
v_vs_3134_ = lean_ctor_get(v_x_3103_, 1);
lean_inc_ref(v_vs_3134_);
lean_dec_ref(v_x_3103_);
v___x_3135_ = lean_unsigned_to_nat(0u);
v___x_3136_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3102_, v_ks_3133_, v_vs_3134_, v___x_3135_, v_x_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec_ref(v_vs_3134_);
lean_dec_ref(v_ks_3133_);
return v___x_3136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3137_, lean_object* v_as_3138_, size_t v_i_3139_, size_t v_stop_3140_, lean_object* v_b_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_a_3148_; lean_object* v___y_3153_; uint8_t v___x_3156_; 
v___x_3156_ = lean_usize_dec_eq(v_i_3139_, v_stop_3140_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; 
v___x_3157_ = lean_array_uget_borrowed(v_as_3138_, v_i_3139_);
switch(lean_obj_tag(v___x_3157_))
{
case 0:
{
lean_object* v_key_3158_; lean_object* v_val_3159_; lean_object* v___x_3160_; 
v_key_3158_ = lean_ctor_get(v___x_3157_, 0);
v_val_3159_ = lean_ctor_get(v___x_3157_, 1);
lean_inc_ref(v_f_3137_);
lean_inc(v___y_3145_);
lean_inc_ref(v___y_3144_);
lean_inc(v___y_3143_);
lean_inc_ref(v___y_3142_);
lean_inc(v_val_3159_);
lean_inc(v_key_3158_);
v___x_3160_ = lean_apply_8(v_f_3137_, v_b_3141_, v_key_3158_, v_val_3159_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, lean_box(0));
v___y_3153_ = v___x_3160_;
goto v___jp_3152_;
}
case 1:
{
lean_object* v_node_3161_; lean_object* v___x_3162_; 
v_node_3161_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v___y_3145_);
lean_inc_ref(v___y_3144_);
lean_inc(v___y_3143_);
lean_inc_ref(v___y_3142_);
lean_inc(v_node_3161_);
lean_inc_ref(v_f_3137_);
v___x_3162_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(v_f_3137_, v_node_3161_, v_b_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
v___y_3153_ = v___x_3162_;
goto v___jp_3152_;
}
default: 
{
v_a_3148_ = v_b_3141_;
goto v___jp_3147_;
}
}
}
else
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec_ref(v_f_3137_);
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v_b_3141_);
v___x_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
return v___x_3164_;
}
v___jp_3147_:
{
size_t v___x_3149_; size_t v___x_3150_; 
v___x_3149_ = ((size_t)1ULL);
v___x_3150_ = lean_usize_add(v_i_3139_, v___x_3149_);
v_i_3139_ = v___x_3150_;
v_b_3141_ = v_a_3148_;
goto _start;
}
v___jp_3152_:
{
if (lean_obj_tag(v___y_3153_) == 0)
{
lean_object* v_a_3154_; 
v_a_3154_ = lean_ctor_get(v___y_3153_, 0);
if (lean_obj_tag(v_a_3154_) == 0)
{
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec_ref(v_f_3137_);
return v___y_3153_;
}
else
{
lean_object* v_a_3155_; 
lean_inc_ref(v_a_3154_);
lean_dec_ref(v___y_3153_);
v_a_3155_ = lean_ctor_get(v_a_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref(v_a_3154_);
v_a_3148_ = v_a_3155_;
goto v___jp_3147_;
}
}
else
{
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec_ref(v_f_3137_);
return v___y_3153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3165_, lean_object* v_as_3166_, lean_object* v_i_3167_, lean_object* v_stop_3168_, lean_object* v_b_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
size_t v_i_boxed_3175_; size_t v_stop_boxed_3176_; lean_object* v_res_3177_; 
v_i_boxed_3175_ = lean_unbox_usize(v_i_3167_);
lean_dec(v_i_3167_);
v_stop_boxed_3176_ = lean_unbox_usize(v_stop_3168_);
lean_dec(v_stop_3168_);
v_res_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3165_, v_as_3166_, v_i_boxed_3175_, v_stop_boxed_3176_, v_b_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec_ref(v_as_3166_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3178_, lean_object* v_x_3179_, lean_object* v_x_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(v_f_3178_, v_x_3179_, v_x_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg(lean_object* v_map_3187_, lean_object* v_init_3188_, lean_object* v_f_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v___f_3195_; lean_object* v___x_3196_; 
v___f_3195_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3195_, 0, v_f_3189_);
v___x_3196_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(v___f_3195_, v_map_3187_, v_init_3188_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3205_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3205_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3205_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v_a_3201_; lean_object* v___x_3203_; 
v_a_3201_ = lean_ctor_get(v_a_3197_, 0);
lean_inc(v_a_3201_);
lean_dec(v_a_3197_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v_a_3201_);
v___x_3203_ = v___x_3199_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
v_a_3206_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3196_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3196_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___boxed(lean_object* v_map_3214_, lean_object* v_init_3215_, lean_object* v_f_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg(v_map_3214_, v_init_3215_, v_f_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg(lean_object* v_cfg_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
lean_object* v___x_3229_; lean_object* v_env_3230_; lean_object* v_maxSuggestions_3231_; lean_object* v___x_3232_; lean_object* v_map_u2082_3233_; lean_object* v___f_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3229_ = lean_st_ref_get(v_a_3227_);
v_env_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc_ref(v_env_3230_);
lean_dec(v___x_3229_);
v_maxSuggestions_3231_ = lean_ctor_get(v_cfg_3223_, 0);
lean_inc(v_maxSuggestions_3231_);
lean_dec_ref(v_cfg_3223_);
lean_inc_ref(v_env_3230_);
v___x_3232_ = l_Lean_Environment_constants(v_env_3230_);
v_map_u2082_3233_ = lean_ctor_get(v___x_3232_, 1);
lean_inc_ref(v_map_u2082_3233_);
lean_dec_ref(v___x_3232_);
v___f_3234_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3234_, 0, v_maxSuggestions_3231_);
lean_closure_set(v___f_3234_, 1, v_env_3230_);
v___x_3235_ = ((lean_object*)(l_Lean_LibrarySuggestions_Selector_postFilter___closed__1));
v___x_3236_ = l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg(v_map_u2082_3233_, v___x_3235_, v___f_3234_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg___boxed(lean_object* v_cfg_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_LibrarySuggestions_currentFile___redArg(v_cfg_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile(lean_object* v_x_3244_, lean_object* v_cfg_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Lean_LibrarySuggestions_currentFile___redArg(v_cfg_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___boxed(lean_object* v_x_3252_, lean_object* v_cfg_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Lean_LibrarySuggestions_currentFile(v_x_3252_, v_cfg_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_);
lean_dec(v_x_3252_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0(lean_object* v_00_u03c3_3260_, lean_object* v_00_u03b2_3261_, lean_object* v_map_3262_, lean_object* v_init_3263_, lean_object* v_f_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg(v_map_3262_, v_init_3263_, v_f_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___boxed(lean_object* v_00_u03c3_3271_, lean_object* v_00_u03b2_3272_, lean_object* v_map_3273_, lean_object* v_init_3274_, lean_object* v_f_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0(v_00_u03c3_3271_, v_00_u03b2_3272_, v_map_3273_, v_init_3274_, v_f_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___redArg(lean_object* v_map_3282_, lean_object* v_f_3283_, lean_object* v_init_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(v_f_3283_, v_map_3282_, v_init_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___redArg___boxed(lean_object* v_map_3291_, lean_object* v_f_3292_, lean_object* v_init_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___redArg(v_map_3291_, v_f_3292_, v_init_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0(lean_object* v_00_u03c3_3300_, lean_object* v_00_u03c3_3301_, lean_object* v_00_u03b2_3302_, lean_object* v_map_3303_, lean_object* v_f_3304_, lean_object* v_init_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(v_f_3304_, v_map_3303_, v_init_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3312_, lean_object* v_00_u03c3_3313_, lean_object* v_00_u03b2_3314_, lean_object* v_map_3315_, lean_object* v_f_3316_, lean_object* v_init_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0(v_00_u03c3_3312_, v_00_u03c3_3313_, v_00_u03b2_3314_, v_map_3315_, v_f_3316_, v_init_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3324_, lean_object* v_00_u03c3_3325_, lean_object* v_00_u03b1_3326_, lean_object* v_00_u03b2_3327_, lean_object* v_f_3328_, lean_object* v_x_3329_, lean_object* v_x_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(v_f_3328_, v_x_3329_, v_x_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3337_, lean_object* v_00_u03c3_3338_, lean_object* v_00_u03b1_3339_, lean_object* v_00_u03b2_3340_, lean_object* v_f_3341_, lean_object* v_x_3342_, lean_object* v_x_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1(v_00_u03c3_3337_, v_00_u03c3_3338_, v_00_u03b1_3339_, v_00_u03b2_3340_, v_f_3341_, v_x_3342_, v_x_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3350_, lean_object* v_00_u03b2_3351_, lean_object* v_00_u03c3_3352_, lean_object* v_00_u03c3_3353_, lean_object* v_f_3354_, lean_object* v_as_3355_, size_t v_i_3356_, size_t v_stop_3357_, lean_object* v_b_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3354_, v_as_3355_, v_i_3356_, v_stop_3357_, v_b_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3365_, lean_object* v_00_u03b2_3366_, lean_object* v_00_u03c3_3367_, lean_object* v_00_u03c3_3368_, lean_object* v_f_3369_, lean_object* v_as_3370_, lean_object* v_i_3371_, lean_object* v_stop_3372_, lean_object* v_b_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
size_t v_i_boxed_3379_; size_t v_stop_boxed_3380_; lean_object* v_res_3381_; 
v_i_boxed_3379_ = lean_unbox_usize(v_i_3371_);
lean_dec(v_i_3371_);
v_stop_boxed_3380_ = lean_unbox_usize(v_stop_3372_);
lean_dec(v_stop_3372_);
v_res_3381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3365_, v_00_u03b2_3366_, v_00_u03c3_3367_, v_00_u03c3_3368_, v_f_3369_, v_as_3370_, v_i_boxed_3379_, v_stop_boxed_3380_, v_b_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
lean_dec_ref(v_as_3370_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3382_, lean_object* v_00_u03c3_3383_, lean_object* v_00_u03b1_3384_, lean_object* v_00_u03b2_3385_, lean_object* v_f_3386_, lean_object* v_keys_3387_, lean_object* v_vals_3388_, lean_object* v_heq_3389_, lean_object* v_i_3390_, lean_object* v_acc_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v___x_3397_; 
v___x_3397_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3386_, v_keys_3387_, v_vals_3388_, v_i_3390_, v_acc_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3398_, lean_object* v_00_u03c3_3399_, lean_object* v_00_u03b1_3400_, lean_object* v_00_u03b2_3401_, lean_object* v_f_3402_, lean_object* v_keys_3403_, lean_object* v_vals_3404_, lean_object* v_heq_3405_, lean_object* v_i_3406_, lean_object* v_acc_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3398_, v_00_u03c3_3399_, v_00_u03b1_3400_, v_00_u03b2_3401_, v_f_3402_, v_keys_3403_, v_vals_3404_, v_heq_3405_, v_i_3406_, v_acc_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec_ref(v_vals_3404_);
lean_dec_ref(v_keys_3403_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(lean_object* v_x_3414_, lean_object* v_name_3415_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3416_, 0, v_name_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed(lean_object* v_x_3417_, lean_object* v_name_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(v_x_3417_, v_name_3418_);
lean_dec(v_x_3417_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0(lean_object* v_as_3420_, size_t v_i_3421_, size_t v_stop_3422_, lean_object* v_b_3423_){
_start:
{
uint8_t v___x_3424_; 
v___x_3424_ = lean_usize_dec_eq(v_i_3421_, v_stop_3422_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; size_t v___x_3427_; size_t v___x_3428_; 
lean_dec(v_b_3423_);
v___x_3425_ = lean_array_uget_borrowed(v_as_3420_, v_i_3421_);
lean_inc(v___x_3425_);
v___x_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
v___x_3427_ = ((size_t)1ULL);
v___x_3428_ = lean_usize_add(v_i_3421_, v___x_3427_);
v_i_3421_ = v___x_3428_;
v_b_3423_ = v___x_3426_;
goto _start;
}
else
{
return v_b_3423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_3430_, lean_object* v_i_3431_, lean_object* v_stop_3432_, lean_object* v_b_3433_){
_start:
{
size_t v_i_boxed_3434_; size_t v_stop_boxed_3435_; lean_object* v_res_3436_; 
v_i_boxed_3434_ = lean_unbox_usize(v_i_3431_);
lean_dec(v_i_3431_);
v_stop_boxed_3435_ = lean_unbox_usize(v_stop_3432_);
lean_dec(v_stop_3432_);
v_res_3436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0(v_as_3430_, v_i_boxed_3434_, v_stop_boxed_3435_, v_b_3433_);
lean_dec_ref(v_as_3430_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1(lean_object* v_as_3437_, size_t v_i_3438_, size_t v_stop_3439_, lean_object* v_b_3440_){
_start:
{
lean_object* v___y_3442_; uint8_t v___x_3446_; 
v___x_3446_ = lean_usize_dec_eq(v_i_3438_, v_stop_3439_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; uint8_t v___x_3450_; 
v___x_3447_ = lean_array_uget_borrowed(v_as_3437_, v_i_3438_);
v___x_3448_ = lean_unsigned_to_nat(0u);
v___x_3449_ = lean_array_get_size(v___x_3447_);
v___x_3450_ = lean_nat_dec_lt(v___x_3448_, v___x_3449_);
if (v___x_3450_ == 0)
{
v___y_3442_ = v_b_3440_;
goto v___jp_3441_;
}
else
{
uint8_t v___x_3451_; 
v___x_3451_ = lean_nat_dec_le(v___x_3449_, v___x_3449_);
if (v___x_3451_ == 0)
{
if (v___x_3450_ == 0)
{
v___y_3442_ = v_b_3440_;
goto v___jp_3441_;
}
else
{
size_t v___x_3452_; size_t v___x_3453_; lean_object* v___x_3454_; 
v___x_3452_ = ((size_t)0ULL);
v___x_3453_ = lean_usize_of_nat(v___x_3449_);
v___x_3454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0(v___x_3447_, v___x_3452_, v___x_3453_, v_b_3440_);
v___y_3442_ = v___x_3454_;
goto v___jp_3441_;
}
}
else
{
size_t v___x_3455_; size_t v___x_3456_; lean_object* v___x_3457_; 
v___x_3455_ = ((size_t)0ULL);
v___x_3456_ = lean_usize_of_nat(v___x_3449_);
v___x_3457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0(v___x_3447_, v___x_3455_, v___x_3456_, v_b_3440_);
v___y_3442_ = v___x_3457_;
goto v___jp_3441_;
}
}
}
else
{
return v_b_3440_;
}
v___jp_3441_:
{
size_t v___x_3443_; size_t v___x_3444_; 
v___x_3443_ = ((size_t)1ULL);
v___x_3444_ = lean_usize_add(v_i_3438_, v___x_3443_);
v_i_3438_ = v___x_3444_;
v_b_3440_ = v___y_3442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_3458_, lean_object* v_i_3459_, lean_object* v_stop_3460_, lean_object* v_b_3461_){
_start:
{
size_t v_i_boxed_3462_; size_t v_stop_boxed_3463_; lean_object* v_res_3464_; 
v_i_boxed_3462_ = lean_unbox_usize(v_i_3459_);
lean_dec(v_i_3459_);
v_stop_boxed_3463_ = lean_unbox_usize(v_stop_3460_);
lean_dec(v_stop_3460_);
v_res_3464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1(v_as_3458_, v_i_boxed_3462_, v_stop_boxed_3463_, v_b_3461_);
lean_dec_ref(v_as_3458_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(lean_object* v_entries_3465_){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
v___x_3466_ = lean_box(0);
v___x_3467_ = lean_unsigned_to_nat(0u);
v___x_3468_ = lean_array_get_size(v_entries_3465_);
v___x_3469_ = lean_nat_dec_lt(v___x_3467_, v___x_3468_);
if (v___x_3469_ == 0)
{
return v___x_3466_;
}
else
{
uint8_t v___x_3470_; 
v___x_3470_ = lean_nat_dec_le(v___x_3468_, v___x_3468_);
if (v___x_3470_ == 0)
{
if (v___x_3469_ == 0)
{
return v___x_3466_;
}
else
{
size_t v___x_3471_; size_t v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = ((size_t)0ULL);
v___x_3472_ = lean_usize_of_nat(v___x_3468_);
v___x_3473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1(v_entries_3465_, v___x_3471_, v___x_3472_, v___x_3466_);
return v___x_3473_;
}
}
else
{
size_t v___x_3474_; size_t v___x_3475_; lean_object* v___x_3476_; 
v___x_3474_ = ((size_t)0ULL);
v___x_3475_ = lean_usize_of_nat(v___x_3468_);
v___x_3476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1(v_entries_3465_, v___x_3474_, v___x_3475_, v___x_3466_);
return v___x_3476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed(lean_object* v_entries_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(v_entries_3477_);
lean_dec_ref(v_entries_3477_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_));
v___x_3495_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed(lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_();
return v_res_3497_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3498_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__0);
v___x_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
return v___x_3500_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1);
v___x_3502_ = lean_unsigned_to_nat(0u);
v___x_3503_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
lean_ctor_set(v___x_3503_, 2, v___x_3502_);
lean_ctor_set(v___x_3503_, 3, v___x_3501_);
lean_ctor_set(v___x_3503_, 4, v___x_3501_);
lean_ctor_set(v___x_3503_, 5, v___x_3501_);
lean_ctor_set(v___x_3503_, 6, v___x_3501_);
lean_ctor_set(v___x_3503_, 7, v___x_3501_);
lean_ctor_set(v___x_3503_, 8, v___x_3501_);
return v___x_3503_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = lean_unsigned_to_nat(32u);
v___x_3505_ = lean_mk_empty_array_with_capacity(v___x_3504_);
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
return v___x_3506_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__4(void){
_start:
{
size_t v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3507_ = ((size_t)5ULL);
v___x_3508_ = lean_unsigned_to_nat(0u);
v___x_3509_ = lean_unsigned_to_nat(32u);
v___x_3510_ = lean_mk_empty_array_with_capacity(v___x_3509_);
v___x_3511_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3);
v___x_3512_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
lean_ctor_set(v___x_3512_, 1, v___x_3510_);
lean_ctor_set(v___x_3512_, 2, v___x_3508_);
lean_ctor_set(v___x_3512_, 3, v___x_3508_);
lean_ctor_set_usize(v___x_3512_, 4, v___x_3507_);
return v___x_3512_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3513_ = lean_box(1);
v___x_3514_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__4);
v___x_3515_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1);
v___x_3516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
lean_ctor_set(v___x_3516_, 1, v___x_3514_);
lean_ctor_set(v___x_3516_, 2, v___x_3513_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_msgData_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v___x_3521_; lean_object* v_env_3522_; lean_object* v_options_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3521_ = lean_st_ref_get(v___y_3519_);
v_env_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc_ref(v_env_3522_);
lean_dec(v___x_3521_);
v_options_3523_ = lean_ctor_get(v___y_3518_, 2);
v___x_3524_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2);
v___x_3525_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5);
lean_inc_ref(v_options_3523_);
v___x_3526_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3526_, 0, v_env_3522_);
lean_ctor_set(v___x_3526_, 1, v___x_3524_);
lean_ctor_set(v___x_3526_, 2, v___x_3525_);
lean_ctor_set(v___x_3526_, 3, v_options_3523_);
v___x_3527_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
lean_ctor_set(v___x_3527_, 1, v_msgData_3517_);
v___x_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_msgData_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2(v_msgData_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(lean_object* v_msg_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_ref_3538_; lean_object* v___x_3539_; lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3548_; 
v_ref_3538_ = lean_ctor_get(v___y_3535_, 5);
v___x_3539_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2(v_msg_3534_, v___y_3535_, v___y_3536_);
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
lean_inc(v_ref_3538_);
v___x_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3544_, 0, v_ref_3538_);
lean_ctor_set(v___x_3544_, 1, v_a_3540_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set_tag(v___x_3542_, 1);
lean_ctor_set(v___x_3542_, 0, v___x_3544_);
v___x_3546_ = v___x_3542_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_msg_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(v_msg_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_3554_, lean_object* v_msg_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v_fileName_3559_; lean_object* v_fileMap_3560_; lean_object* v_options_3561_; lean_object* v_currRecDepth_3562_; lean_object* v_maxRecDepth_3563_; lean_object* v_ref_3564_; lean_object* v_currNamespace_3565_; lean_object* v_openDecls_3566_; lean_object* v_initHeartbeats_3567_; lean_object* v_maxHeartbeats_3568_; lean_object* v_quotContext_3569_; lean_object* v_currMacroScope_3570_; uint8_t v_diag_3571_; lean_object* v_cancelTk_x3f_3572_; uint8_t v_suppressElabErrors_3573_; lean_object* v_inheritedTraceOptions_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3583_; 
v_fileName_3559_ = lean_ctor_get(v___y_3556_, 0);
v_fileMap_3560_ = lean_ctor_get(v___y_3556_, 1);
v_options_3561_ = lean_ctor_get(v___y_3556_, 2);
v_currRecDepth_3562_ = lean_ctor_get(v___y_3556_, 3);
v_maxRecDepth_3563_ = lean_ctor_get(v___y_3556_, 4);
v_ref_3564_ = lean_ctor_get(v___y_3556_, 5);
v_currNamespace_3565_ = lean_ctor_get(v___y_3556_, 6);
v_openDecls_3566_ = lean_ctor_get(v___y_3556_, 7);
v_initHeartbeats_3567_ = lean_ctor_get(v___y_3556_, 8);
v_maxHeartbeats_3568_ = lean_ctor_get(v___y_3556_, 9);
v_quotContext_3569_ = lean_ctor_get(v___y_3556_, 10);
v_currMacroScope_3570_ = lean_ctor_get(v___y_3556_, 11);
v_diag_3571_ = lean_ctor_get_uint8(v___y_3556_, sizeof(void*)*14);
v_cancelTk_x3f_3572_ = lean_ctor_get(v___y_3556_, 12);
v_suppressElabErrors_3573_ = lean_ctor_get_uint8(v___y_3556_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3574_ = lean_ctor_get(v___y_3556_, 13);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___y_3556_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3576_ = v___y_3556_;
v_isShared_3577_ = v_isSharedCheck_3583_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_inheritedTraceOptions_3574_);
lean_inc(v_cancelTk_x3f_3572_);
lean_inc(v_currMacroScope_3570_);
lean_inc(v_quotContext_3569_);
lean_inc(v_maxHeartbeats_3568_);
lean_inc(v_initHeartbeats_3567_);
lean_inc(v_openDecls_3566_);
lean_inc(v_currNamespace_3565_);
lean_inc(v_ref_3564_);
lean_inc(v_maxRecDepth_3563_);
lean_inc(v_currRecDepth_3562_);
lean_inc(v_options_3561_);
lean_inc(v_fileMap_3560_);
lean_inc(v_fileName_3559_);
lean_dec(v___y_3556_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3583_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v_ref_3578_; lean_object* v___x_3580_; 
v_ref_3578_ = l_Lean_replaceRef(v_ref_3554_, v_ref_3564_);
lean_dec(v_ref_3564_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 5, v_ref_3578_);
v___x_3580_ = v___x_3576_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_fileName_3559_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_fileMap_3560_);
lean_ctor_set(v_reuseFailAlloc_3582_, 2, v_options_3561_);
lean_ctor_set(v_reuseFailAlloc_3582_, 3, v_currRecDepth_3562_);
lean_ctor_set(v_reuseFailAlloc_3582_, 4, v_maxRecDepth_3563_);
lean_ctor_set(v_reuseFailAlloc_3582_, 5, v_ref_3578_);
lean_ctor_set(v_reuseFailAlloc_3582_, 6, v_currNamespace_3565_);
lean_ctor_set(v_reuseFailAlloc_3582_, 7, v_openDecls_3566_);
lean_ctor_set(v_reuseFailAlloc_3582_, 8, v_initHeartbeats_3567_);
lean_ctor_set(v_reuseFailAlloc_3582_, 9, v_maxHeartbeats_3568_);
lean_ctor_set(v_reuseFailAlloc_3582_, 10, v_quotContext_3569_);
lean_ctor_set(v_reuseFailAlloc_3582_, 11, v_currMacroScope_3570_);
lean_ctor_set(v_reuseFailAlloc_3582_, 12, v_cancelTk_x3f_3572_);
lean_ctor_set(v_reuseFailAlloc_3582_, 13, v_inheritedTraceOptions_3574_);
lean_ctor_set_uint8(v_reuseFailAlloc_3582_, sizeof(void*)*14, v_diag_3571_);
lean_ctor_set_uint8(v_reuseFailAlloc_3582_, sizeof(void*)*14 + 1, v_suppressElabErrors_3573_);
v___x_3580_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(v_msg_3555_, v___x_3580_, v___y_3557_);
lean_dec_ref(v___x_3580_);
return v___x_3581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_3584_, lean_object* v_msg_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_3584_, v_msg_3585_, v___y_3586_, v___y_3587_);
lean_dec(v___y_3587_);
lean_dec(v_ref_3584_);
return v_res_3589_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_3592_ = l_Lean_stringToMessageData(v___x_3591_);
return v___x_3592_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_3595_ = l_Lean_stringToMessageData(v___x_3594_);
return v___x_3595_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3597_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_3598_ = l_Lean_stringToMessageData(v___x_3597_);
return v___x_3598_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_3601_ = l_Lean_stringToMessageData(v___x_3600_);
return v___x_3601_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_3604_ = l_Lean_stringToMessageData(v___x_3603_);
return v___x_3604_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_3607_ = l_Lean_stringToMessageData(v___x_3606_);
return v___x_3607_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_3610_ = l_Lean_stringToMessageData(v___x_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_3611_, lean_object* v_declHint_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v___x_3615_; lean_object* v_env_3616_; uint8_t v___x_3617_; 
v___x_3615_ = lean_st_ref_get(v___y_3613_);
v_env_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc_ref(v_env_3616_);
lean_dec(v___x_3615_);
v___x_3617_ = l_Lean_Name_isAnonymous(v_declHint_3612_);
if (v___x_3617_ == 0)
{
uint8_t v_isExporting_3618_; 
v_isExporting_3618_ = lean_ctor_get_uint8(v_env_3616_, sizeof(void*)*8);
if (v_isExporting_3618_ == 0)
{
lean_object* v___x_3619_; 
lean_dec_ref(v_env_3616_);
lean_dec(v_declHint_3612_);
v___x_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3619_, 0, v_msg_3611_);
return v___x_3619_;
}
else
{
lean_object* v___x_3620_; uint8_t v___x_3621_; 
lean_inc_ref(v_env_3616_);
v___x_3620_ = l_Lean_Environment_setExporting(v_env_3616_, v___x_3617_);
lean_inc(v_declHint_3612_);
lean_inc_ref(v___x_3620_);
v___x_3621_ = l_Lean_Environment_contains(v___x_3620_, v_declHint_3612_, v_isExporting_3618_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; 
lean_dec_ref(v___x_3620_);
lean_dec_ref(v_env_3616_);
lean_dec(v_declHint_3612_);
v___x_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3622_, 0, v_msg_3611_);
return v___x_3622_;
}
else
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v_c_3628_; lean_object* v___x_3629_; 
v___x_3623_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2);
v___x_3624_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5);
v___x_3625_ = l_Lean_Options_empty;
v___x_3626_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3620_);
lean_ctor_set(v___x_3626_, 1, v___x_3623_);
lean_ctor_set(v___x_3626_, 2, v___x_3624_);
lean_ctor_set(v___x_3626_, 3, v___x_3625_);
lean_inc(v_declHint_3612_);
v___x_3627_ = l_Lean_MessageData_ofConstName(v_declHint_3612_, v___x_3617_);
v_c_3628_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3628_, 0, v___x_3626_);
lean_ctor_set(v_c_3628_, 1, v___x_3627_);
v___x_3629_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3616_, v_declHint_3612_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_dec_ref(v_env_3616_);
lean_dec(v_declHint_3612_);
v___x_3630_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_3631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
lean_ctor_set(v___x_3631_, 1, v_c_3628_);
v___x_3632_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_3633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3631_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
v___x_3634_ = l_Lean_MessageData_note(v___x_3633_);
v___x_3635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3635_, 0, v_msg_3611_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
return v___x_3636_;
}
else
{
lean_object* v_val_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3672_; 
v_val_3637_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3639_ = v___x_3629_;
v_isShared_3640_ = v_isSharedCheck_3672_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_val_3637_);
lean_dec(v___x_3629_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3672_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v_mod_3644_; uint8_t v___x_3645_; 
v___x_3641_ = lean_box(0);
v___x_3642_ = l_Lean_Environment_header(v_env_3616_);
lean_dec_ref(v_env_3616_);
v___x_3643_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3642_);
v_mod_3644_ = lean_array_get(v___x_3641_, v___x_3643_, v_val_3637_);
lean_dec(v_val_3637_);
lean_dec_ref(v___x_3643_);
v___x_3645_ = l_Lean_isPrivateName(v_declHint_3612_);
lean_dec(v_declHint_3612_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3657_; 
v___x_3646_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_3647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
lean_ctor_set(v___x_3647_, 1, v_c_3628_);
v___x_3648_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = l_Lean_MessageData_ofName(v_mod_3644_);
v___x_3651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3649_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___x_3652_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3651_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = l_Lean_MessageData_note(v___x_3653_);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v_msg_3611_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set_tag(v___x_3639_, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3655_);
v___x_3657_ = v___x_3639_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
else
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; 
v___x_3659_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_3660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
lean_ctor_set(v___x_3660_, 1, v_c_3628_);
v___x_3661_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_3662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = l_Lean_MessageData_ofName(v_mod_3644_);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3664_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = l_Lean_MessageData_note(v___x_3666_);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v_msg_3611_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set_tag(v___x_3639_, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3668_);
v___x_3670_ = v___x_3639_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3673_; 
lean_dec_ref(v_env_3616_);
lean_dec(v_declHint_3612_);
v___x_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3673_, 0, v_msg_3611_);
return v___x_3673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_3674_, lean_object* v_declHint_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_3674_, v_declHint_3675_, v___y_3676_);
lean_dec(v___y_3676_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_3679_, lean_object* v_declHint_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v___x_3684_; lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3694_; 
v___x_3684_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_3679_, v_declHint_3680_, v___y_3682_);
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3687_ = v___x_3684_;
v_isShared_3688_ = v_isSharedCheck_3694_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3684_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3694_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3689_ = l_Lean_unknownIdentifierMessageTag;
v___x_3690_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
lean_ctor_set(v___x_3690_, 1, v_a_3685_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v___x_3690_);
v___x_3692_ = v___x_3687_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_3695_, lean_object* v_declHint_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_3695_, v_declHint_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_3701_, lean_object* v_msg_3702_, lean_object* v_declHint_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v___x_3707_; lean_object* v_a_3708_; lean_object* v___x_3709_; 
v___x_3707_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_3702_, v_declHint_3703_, v___y_3704_, v___y_3705_);
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref(v___x_3707_);
v___x_3709_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_3701_, v_a_3708_, v___y_3704_, v___y_3705_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_3710_, lean_object* v_msg_3711_, lean_object* v_declHint_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_ref_3710_, v_msg_3711_, v_declHint_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec(v_ref_3710_);
return v_res_3716_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3718_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0));
v___x_3719_ = l_Lean_stringToMessageData(v___x_3718_);
return v___x_3719_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2));
v___x_3722_ = l_Lean_stringToMessageData(v___x_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3723_, lean_object* v_constName_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v___x_3728_; uint8_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3728_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3729_ = 0;
lean_inc(v_constName_3724_);
v___x_3730_ = l_Lean_MessageData_ofConstName(v_constName_3724_, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3728_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
v___x_3733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_ref_3723_, v___x_3733_, v_constName_3724_, v___y_3725_, v___y_3726_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3735_, lean_object* v_constName_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_3735_, v_constName_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___y_3738_);
lean_dec(v_ref_3735_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_constName_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v_ref_3745_; lean_object* v___x_3746_; 
v_ref_3745_ = lean_ctor_get(v___y_3742_, 5);
lean_inc(v_ref_3745_);
v___x_3746_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_3745_, v_constName_3741_, v___y_3742_, v___y_3743_);
lean_dec(v_ref_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_constName_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_3747_, v___y_3748_, v___y_3749_);
lean_dec(v___y_3749_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0(lean_object* v_constName_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v___x_3756_; lean_object* v_env_3757_; uint8_t v___x_3758_; lean_object* v___x_3759_; 
v___x_3756_ = lean_st_ref_get(v___y_3754_);
v_env_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc_ref(v_env_3757_);
lean_dec(v___x_3756_);
v___x_3758_ = 0;
lean_inc(v_constName_3752_);
v___x_3759_ = l_Lean_Environment_find_x3f(v_env_3757_, v_constName_3752_, v___x_3758_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v___x_3760_; 
v___x_3760_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_3752_, v___y_3753_, v___y_3754_);
return v___x_3760_;
}
else
{
lean_object* v_val_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec_ref(v___y_3753_);
lean_dec(v_constName_3752_);
v_val_3761_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3759_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_val_3761_);
lean_dec(v___x_3759_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set_tag(v___x_3763_, 0);
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_val_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0___boxed(lean_object* v_constName_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0(v_constName_3769_, v___y_3770_, v___y_3771_);
lean_dec(v___y_3771_);
return v_res_3773_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3774_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = lean_obj_once(&l_Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_, &l_Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__once, _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_);
v___x_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
return v___x_3776_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3777_ = lean_obj_once(&l_Lean_LibrarySuggestions_initFn___lam__0___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_, &l_Lean_LibrarySuggestions_initFn___lam__0___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__once, _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_);
v___x_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
return v___x_3778_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3784_ = lean_box(0);
v___x_3785_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
v___x_3786_ = l_Lean_mkConst(v___x_3785_, v___x_3784_);
return v___x_3786_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__0___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
v___x_3789_ = l_Lean_stringToMessageData(v___x_3788_);
return v___x_3789_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__0___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
v___x_3792_ = l_Lean_stringToMessageData(v___x_3791_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(lean_object* v_declName_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v___y_3798_; lean_object* v___x_3825_; 
lean_inc_ref(v___y_3794_);
lean_inc(v_declName_3793_);
v___x_3825_ = l_Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0(v_declName_3793_, v___y_3794_, v___y_3795_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref(v___x_3825_);
v___x_3827_ = l_Lean_ConstantInfo_type(v_a_3826_);
lean_dec(v_a_3826_);
v___x_3828_ = lean_obj_once(&l_Lean_LibrarySuggestions_initFn___lam__0___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_, &l_Lean_LibrarySuggestions_initFn___lam__0___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__once, _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_);
v___x_3829_ = lean_expr_eqv(v___x_3827_, v___x_3828_);
lean_dec_ref(v___x_3827_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3830_ = lean_obj_once(&l_Lean_LibrarySuggestions_initFn___lam__0___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_, &l_Lean_LibrarySuggestions_initFn___lam__0___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__once, _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_);
v___x_3831_ = l_Lean_MessageData_ofName(v_declName_3793_);
v___x_3832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3830_);
lean_ctor_set(v___x_3832_, 1, v___x_3831_);
v___x_3833_ = lean_obj_once(&l_Lean_LibrarySuggestions_initFn___lam__0___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_, &l_Lean_LibrarySuggestions_initFn___lam__0___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__once, _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_);
v___x_3834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3832_);
lean_ctor_set(v___x_3834_, 1, v___x_3833_);
v___x_3835_ = l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(v___x_3834_, v___y_3794_, v___y_3795_);
lean_dec_ref(v___y_3794_);
return v___x_3835_;
}
else
{
lean_dec_ref(v___y_3794_);
v___y_3798_ = v___y_3795_;
goto v___jp_3797_;
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_dec_ref(v___y_3794_);
lean_dec(v_declName_3793_);
v_a_3836_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3825_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3825_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
v___jp_3797_:
{
lean_object* v___x_3799_; lean_object* v_env_3800_; lean_object* v_nextMacroScope_3801_; lean_object* v_ngen_3802_; lean_object* v_auxDeclNGen_3803_; lean_object* v_traceState_3804_; lean_object* v_messages_3805_; lean_object* v_infoState_3806_; lean_object* v_snapshotTasks_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3823_; 
v___x_3799_ = lean_st_ref_take(v___y_3798_);
v_env_3800_ = lean_ctor_get(v___x_3799_, 0);
v_nextMacroScope_3801_ = lean_ctor_get(v___x_3799_, 1);
v_ngen_3802_ = lean_ctor_get(v___x_3799_, 2);
v_auxDeclNGen_3803_ = lean_ctor_get(v___x_3799_, 3);
v_traceState_3804_ = lean_ctor_get(v___x_3799_, 4);
v_messages_3805_ = lean_ctor_get(v___x_3799_, 6);
v_infoState_3806_ = lean_ctor_get(v___x_3799_, 7);
v_snapshotTasks_3807_ = lean_ctor_get(v___x_3799_, 8);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3823_ == 0)
{
lean_object* v_unused_3824_; 
v_unused_3824_ = lean_ctor_get(v___x_3799_, 5);
lean_dec(v_unused_3824_);
v___x_3809_ = v___x_3799_;
v_isShared_3810_ = v_isSharedCheck_3823_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_snapshotTasks_3807_);
lean_inc(v_infoState_3806_);
lean_inc(v_messages_3805_);
lean_inc(v_traceState_3804_);
lean_inc(v_auxDeclNGen_3803_);
lean_inc(v_ngen_3802_);
lean_inc(v_nextMacroScope_3801_);
lean_inc(v_env_3800_);
lean_dec(v___x_3799_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3823_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v_toEnvExtension_3812_; lean_object* v_asyncMode_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3818_; 
v___x_3811_ = l_Lean_LibrarySuggestions_librarySuggestionsExt;
v_toEnvExtension_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc_ref(v_toEnvExtension_3812_);
v_asyncMode_3813_ = lean_ctor_get(v_toEnvExtension_3812_, 2);
lean_inc(v_asyncMode_3813_);
lean_dec_ref(v_toEnvExtension_3812_);
v___x_3814_ = lean_box(0);
v___x_3815_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3811_, v_env_3800_, v_declName_3793_, v_asyncMode_3813_, v___x_3814_);
lean_dec(v_asyncMode_3813_);
v___x_3816_ = lean_obj_once(&l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_, &l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__once, _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 5, v___x_3816_);
lean_ctor_set(v___x_3809_, 0, v___x_3815_);
v___x_3818_ = v___x_3809_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_nextMacroScope_3801_);
lean_ctor_set(v_reuseFailAlloc_3822_, 2, v_ngen_3802_);
lean_ctor_set(v_reuseFailAlloc_3822_, 3, v_auxDeclNGen_3803_);
lean_ctor_set(v_reuseFailAlloc_3822_, 4, v_traceState_3804_);
lean_ctor_set(v_reuseFailAlloc_3822_, 5, v___x_3816_);
lean_ctor_set(v_reuseFailAlloc_3822_, 6, v_messages_3805_);
lean_ctor_set(v_reuseFailAlloc_3822_, 7, v_infoState_3806_);
lean_ctor_set(v_reuseFailAlloc_3822_, 8, v_snapshotTasks_3807_);
v___x_3818_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3819_ = lean_st_ref_set(v___y_3798_, v___x_3818_);
v___x_3820_ = lean_box(0);
v___x_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
return v___x_3821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2____boxed(lean_object* v_declName_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(v_declName_3844_, v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___f_3860_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
v___x_3861_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
v___x_3862_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
v___x_3863_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
v___x_3864_ = 0;
v___x_3865_ = lean_box(2);
v___x_3866_ = l_Lean_registerTagAttribute(v___x_3861_, v___x_3862_, v___f_3860_, v___x_3863_, v___x_3864_, v___x_3865_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2____boxed(lean_object* v_a_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_();
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_3869_, lean_object* v_msg_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(v_msg_3870_, v___y_3871_, v___y_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_3875_, lean_object* v_msg_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1(v_00_u03b1_3875_, v_msg_3876_, v___y_3877_, v___y_3878_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b1_3881_, lean_object* v_constName_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_3882_, v___y_3883_, v___y_3884_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b1_3887_, lean_object* v_constName_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_3887_, v_constName_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3893_, lean_object* v_ref_3894_, lean_object* v_constName_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_3894_, v_constName_3895_, v___y_3896_, v___y_3897_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3900_, lean_object* v_ref_3901_, lean_object* v_constName_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b1_3900_, v_ref_3901_, v_constName_3902_, v___y_3903_, v___y_3904_);
lean_dec(v___y_3904_);
lean_dec(v_ref_3901_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_3907_, lean_object* v_ref_3908_, lean_object* v_msg_3909_, lean_object* v_declHint_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_ref_3908_, v_msg_3909_, v_declHint_3910_, v___y_3911_, v___y_3912_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_3915_, lean_object* v_ref_3916_, lean_object* v_msg_3917_, lean_object* v_declHint_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b1_3915_, v_ref_3916_, v_msg_3917_, v_declHint_3918_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec(v_ref_3916_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_3923_, lean_object* v_declHint_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v___x_3928_; 
v___x_3928_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_3923_, v_declHint_3924_, v___y_3926_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_3929_, lean_object* v_declHint_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_3929_, v_declHint_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_3935_, lean_object* v_ref_3936_, lean_object* v_msg_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v___x_3941_; 
v___x_3941_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_3936_, v_msg_3937_, v___y_3938_, v___y_3939_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3942_, lean_object* v_ref_3943_, lean_object* v_msg_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_3942_, v_ref_3943_, v_msg_3944_, v___y_3945_, v___y_3946_);
lean_dec(v___y_3946_);
lean_dec(v_ref_3943_);
return v_res_3948_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3949_ = lean_box(0);
v___x_3950_ = l_Lean_Elab_abortCommandExceptionId;
v___x_3951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
lean_ctor_set(v___x_3951_, 1, v___x_3949_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3953_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___closed__0);
v___x_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___boxed(lean_object* v___y_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg();
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v___x_3963_; lean_object* v_env_3964_; lean_object* v___x_3965_; lean_object* v_mctx_3966_; lean_object* v_lctx_3967_; lean_object* v_options_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3963_ = lean_st_ref_get(v___y_3961_);
v_env_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc_ref(v_env_3964_);
lean_dec(v___x_3963_);
v___x_3965_ = lean_st_ref_get(v___y_3959_);
v_mctx_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc_ref(v_mctx_3966_);
lean_dec(v___x_3965_);
v_lctx_3967_ = lean_ctor_get(v___y_3958_, 2);
v_options_3968_ = lean_ctor_get(v___y_3960_, 2);
lean_inc_ref(v_options_3968_);
lean_inc_ref(v_lctx_3967_);
v___x_3969_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3969_, 0, v_env_3964_);
lean_ctor_set(v___x_3969_, 1, v_mctx_3966_);
lean_ctor_set(v___x_3969_, 2, v_lctx_3967_);
lean_ctor_set(v___x_3969_, 3, v_options_3968_);
v___x_3970_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
lean_ctor_set(v___x_3970_, 1, v_msgData_3957_);
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3(v_msgData_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v_ref_3985_; lean_object* v___x_3986_; lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3995_; 
v_ref_3985_ = lean_ctor_get(v___y_3982_, 5);
v___x_3986_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3(v_msg_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3989_ = v___x_3986_;
v_isShared_3990_ = v_isSharedCheck_3995_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3986_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3995_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3991_; lean_object* v___x_3993_; 
lean_inc(v_ref_3985_);
v___x_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3991_, 0, v_ref_3985_);
lean_ctor_set(v___x_3991_, 1, v_a_3987_);
if (v_isShared_3990_ == 0)
{
lean_ctor_set_tag(v___x_3989_, 1);
lean_ctor_set(v___x_3989_, 0, v___x_3991_);
v___x_3993_ = v___x_3989_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3991_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg(v_msg_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg(lean_object* v_x_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
if (lean_obj_tag(v_x_4003_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v_a_4009_ = lean_ctor_get(v_x_4003_, 0);
lean_inc(v_a_4009_);
lean_dec_ref(v_x_4003_);
v___x_4010_ = l_Lean_stringToMessageData(v_a_4009_);
v___x_4011_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg(v___x_4010_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
return v___x_4011_;
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
v_a_4012_ = lean_ctor_get(v_x_4003_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v_x_4003_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v_x_4003_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v_x_4003_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
lean_ctor_set_tag(v___x_4014_, 0);
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg(v_x_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg(lean_object* v_typeName_4027_, lean_object* v_constName_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v___x_4034_; lean_object* v_env_4035_; uint8_t v___x_4036_; 
v___x_4034_ = lean_st_ref_get(v___y_4032_);
v_env_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc_ref(v_env_4035_);
lean_dec(v___x_4034_);
lean_inc(v_constName_4028_);
v___x_4036_ = lean_has_compile_error(v_env_4035_, v_constName_4028_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; lean_object* v_env_4038_; lean_object* v_options_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4037_ = lean_st_ref_get(v___y_4032_);
v_env_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc_ref(v_env_4038_);
lean_dec(v___x_4037_);
v_options_4039_ = lean_ctor_get(v___y_4031_, 2);
v___x_4040_ = l_Lean_Environment_evalConstCheck___redArg(v_env_4038_, v_options_4039_, v_typeName_4027_, v_constName_4028_);
v___x_4041_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg(v___x_4040_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
return v___x_4041_;
}
else
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v___x_4043_; lean_object* v_env_4044_; lean_object* v_options_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
lean_dec_ref(v___x_4042_);
v___x_4043_ = lean_st_ref_get(v___y_4032_);
v_env_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc_ref(v_env_4044_);
lean_dec(v___x_4043_);
v_options_4045_ = lean_ctor_get(v___y_4031_, 2);
v___x_4046_ = l_Lean_Environment_evalConstCheck___redArg(v_env_4044_, v_options_4045_, v_typeName_4027_, v_constName_4028_);
v___x_4047_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg(v___x_4046_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
return v___x_4047_;
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec(v_constName_4028_);
lean_dec(v_typeName_4027_);
v_a_4048_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4042_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4042_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg___boxed(lean_object* v_typeName_4056_, lean_object* v_constName_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg(v_typeName_4056_, v_constName_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_getSelectorImpl(lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_){
_start:
{
lean_object* v___x_4069_; lean_object* v_env_4070_; lean_object* v___x_4071_; lean_object* v_toEnvExtension_4072_; lean_object* v_asyncMode_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4069_ = lean_st_ref_get(v_a_4067_);
v_env_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc_ref(v_env_4070_);
lean_dec(v___x_4069_);
v___x_4071_ = l_Lean_LibrarySuggestions_librarySuggestionsExt;
v_toEnvExtension_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc_ref(v_toEnvExtension_4072_);
v_asyncMode_4073_ = lean_ctor_get(v_toEnvExtension_4072_, 2);
lean_inc(v_asyncMode_4073_);
lean_dec_ref(v_toEnvExtension_4072_);
v___x_4074_ = lean_box(0);
v___x_4075_ = lean_box(0);
v___x_4076_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4074_, v___x_4071_, v_env_4070_, v_asyncMode_4073_, v___x_4075_);
lean_dec(v_asyncMode_4073_);
if (lean_obj_tag(v___x_4076_) == 1)
{
lean_object* v_val_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4109_; 
v_val_4077_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4079_ = v___x_4076_;
v_isShared_4080_ = v_isSharedCheck_4109_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_val_4077_);
lean_dec(v___x_4076_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4109_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
v___x_4082_ = l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg(v___x_4081_, v_val_4077_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4093_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4085_ = v___x_4082_;
v_isShared_4086_ = v_isSharedCheck_4093_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4082_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4093_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 0, v_a_4083_);
v___x_4088_ = v___x_4079_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4090_; 
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 0, v___x_4088_);
v___x_4090_ = v___x_4085_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4108_; 
lean_del_object(v___x_4079_);
v_a_4094_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4096_ = v___x_4082_;
v_isShared_4097_ = v_isSharedCheck_4108_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4082_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4108_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
uint8_t v___y_4099_; uint8_t v___x_4106_; 
v___x_4106_ = l_Lean_Exception_isInterrupt(v_a_4094_);
if (v___x_4106_ == 0)
{
uint8_t v___x_4107_; 
lean_inc(v_a_4094_);
v___x_4107_ = l_Lean_Exception_isRuntime(v_a_4094_);
v___y_4099_ = v___x_4107_;
goto v___jp_4098_;
}
else
{
v___y_4099_ = v___x_4106_;
goto v___jp_4098_;
}
v___jp_4098_:
{
if (v___y_4099_ == 0)
{
lean_object* v___x_4101_; 
lean_dec(v_a_4094_);
if (v_isShared_4097_ == 0)
{
lean_ctor_set_tag(v___x_4096_, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4074_);
v___x_4101_ = v___x_4096_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4074_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
else
{
lean_object* v___x_4104_; 
if (v_isShared_4097_ == 0)
{
v___x_4104_ = v___x_4096_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4094_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4110_; 
lean_dec(v___x_4076_);
v___x_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4074_);
return v___x_4110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_getSelectorImpl___boxed(lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_LibrarySuggestions_getSelectorImpl(v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_);
lean_dec(v_a_4114_);
lean_dec_ref(v_a_4113_);
lean_dec(v_a_4112_);
lean_dec_ref(v_a_4111_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1(lean_object* v_00_u03b1_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg();
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1(v_00_u03b1_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0(lean_object* v_00_u03b1_4131_, lean_object* v_typeName_4132_, lean_object* v_constName_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg(v_typeName_4132_, v_constName_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___boxed(lean_object* v_00_u03b1_4140_, lean_object* v_typeName_4141_, lean_object* v_constName_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0(v_00_u03b1_4140_, v_typeName_4141_, v_constName_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0(lean_object* v_00_u03b1_4149_, lean_object* v_x_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v___x_4156_; 
v___x_4156_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg(v_x_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b1_4157_, lean_object* v_x_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0(v_00_u03b1_4157_, v_x_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4165_, lean_object* v_msg_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v___x_4172_; 
v___x_4172_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg(v_msg_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4173_, lean_object* v_msg_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1(v_00_u03b1_4173_, v_msg_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
return v_res_4180_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_select___closed__1(void){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4182_ = ((lean_object*)(l_Lean_LibrarySuggestions_select___closed__0));
v___x_4183_ = l_Lean_stringToMessageData(v___x_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_select(lean_object* v_m_4184_, lean_object* v_c_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_LibrarySuggestions_getSelectorImpl(v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4192_);
lean_dec_ref(v___x_4191_);
if (lean_obj_tag(v_a_4192_) == 1)
{
lean_object* v_val_4193_; lean_object* v___x_4194_; 
v_val_4193_ = lean_ctor_get(v_a_4192_, 0);
lean_inc(v_val_4193_);
lean_dec_ref(v_a_4192_);
v___x_4194_ = lean_apply_7(v_val_4193_, v_m_4184_, v_c_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, lean_box(0));
return v___x_4194_;
}
else
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
lean_dec(v_a_4192_);
lean_dec_ref(v_c_4185_);
lean_dec(v_m_4184_);
v___x_4195_ = lean_obj_once(&l_Lean_LibrarySuggestions_select___closed__1, &l_Lean_LibrarySuggestions_select___closed__1_once, _init_l_Lean_LibrarySuggestions_select___closed__1);
v___x_4196_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg(v___x_4195_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_);
lean_dec(v_a_4189_);
lean_dec_ref(v_a_4188_);
lean_dec(v_a_4187_);
lean_dec_ref(v_a_4186_);
return v___x_4196_;
}
}
else
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
lean_dec(v_a_4189_);
lean_dec_ref(v_a_4188_);
lean_dec(v_a_4187_);
lean_dec_ref(v_a_4186_);
lean_dec_ref(v_c_4185_);
lean_dec(v_m_4184_);
v_a_4197_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4199_ = v___x_4191_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4191_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_select___boxed(lean_object* v_m_4205_, lean_object* v_c_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l_Lean_LibrarySuggestions_select(v_m_4205_, v_c_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_);
return v_res_4212_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4213_ = lean_box(0);
v___x_4214_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_4215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
lean_ctor_set(v___x_4215_, 1, v___x_4213_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg(){
_start:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4217_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___closed__0);
v___x_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4217_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___boxed(lean_object* v___y_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg();
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0(lean_object* v_00_u03b1_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg();
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___boxed(lean_object* v_00_u03b1_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0(v_00_u03b1_4226_, v___y_4227_, v___y_4228_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg(lean_object* v___y_4231_){
_start:
{
lean_object* v___x_4233_; lean_object* v_env_4234_; lean_object* v___x_4235_; lean_object* v_mainModule_4236_; lean_object* v___x_4237_; 
v___x_4233_ = lean_st_ref_get(v___y_4231_);
v_env_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc_ref(v_env_4234_);
lean_dec(v___x_4233_);
v___x_4235_ = l_Lean_Environment_header(v_env_4234_);
lean_dec_ref(v_env_4234_);
v_mainModule_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_mainModule_4236_);
lean_dec_ref(v___x_4235_);
v___x_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4237_, 0, v_mainModule_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg___boxed(lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg(v___y_4238_);
lean_dec(v___y_4238_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2(lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg(v___y_4242_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___boxed(lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2(v___y_4245_, v___y_4246_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v___x_4252_; lean_object* v_env_4253_; lean_object* v___x_4254_; lean_object* v_scopes_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v_opts_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4252_ = lean_st_ref_get(v___y_4250_);
v_env_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc_ref(v_env_4253_);
lean_dec(v___x_4252_);
v___x_4254_ = lean_st_ref_get(v___y_4250_);
v_scopes_4255_ = lean_ctor_get(v___x_4254_, 2);
lean_inc(v_scopes_4255_);
lean_dec(v___x_4254_);
v___x_4256_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4257_ = l_List_head_x21___redArg(v___x_4256_, v_scopes_4255_);
lean_dec(v_scopes_4255_);
v_opts_4258_ = lean_ctor_get(v___x_4257_, 1);
lean_inc_ref(v_opts_4258_);
lean_dec(v___x_4257_);
v___x_4259_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2);
v___x_4260_ = lean_unsigned_to_nat(32u);
v___x_4261_ = lean_mk_empty_array_with_capacity(v___x_4260_);
lean_dec_ref(v___x_4261_);
v___x_4262_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5);
v___x_4263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4263_, 0, v_env_4253_);
lean_ctor_set(v___x_4263_, 1, v___x_4259_);
lean_ctor_set(v___x_4263_, 2, v___x_4262_);
lean_ctor_set(v___x_4263_, 3, v_opts_4258_);
v___x_4264_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4263_);
lean_ctor_set(v___x_4264_, 1, v_msgData_4249_);
v___x_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4264_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(v_msgData_4266_, v___y_4267_);
lean_dec(v___y_4267_);
return v_res_4269_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0(uint8_t v___y_4271_, uint8_t v_suppressElabErrors_4272_, lean_object* v_x_4273_){
_start:
{
if (lean_obj_tag(v_x_4273_) == 1)
{
lean_object* v_pre_4274_; 
v_pre_4274_ = lean_ctor_get(v_x_4273_, 0);
if (lean_obj_tag(v_pre_4274_) == 0)
{
lean_object* v_str_4275_; lean_object* v___x_4276_; uint8_t v___x_4277_; 
v_str_4275_ = lean_ctor_get(v_x_4273_, 1);
v___x_4276_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___closed__0));
v___x_4277_ = lean_string_dec_eq(v_str_4275_, v___x_4276_);
if (v___x_4277_ == 0)
{
return v___y_4271_;
}
else
{
return v_suppressElabErrors_4272_;
}
}
else
{
return v___y_4271_;
}
}
else
{
return v___y_4271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___boxed(lean_object* v___y_4278_, lean_object* v_suppressElabErrors_4279_, lean_object* v_x_4280_){
_start:
{
uint8_t v___y_14819__boxed_4281_; uint8_t v_suppressElabErrors_boxed_4282_; uint8_t v_res_4283_; lean_object* v_r_4284_; 
v___y_14819__boxed_4281_ = lean_unbox(v___y_4278_);
v_suppressElabErrors_boxed_4282_ = lean_unbox(v_suppressElabErrors_4279_);
v_res_4283_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0(v___y_14819__boxed_4281_, v_suppressElabErrors_boxed_4282_, v_x_4280_);
lean_dec(v_x_4280_);
v_r_4284_ = lean_box(v_res_4283_);
return v_r_4284_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21(lean_object* v_opts_4285_, lean_object* v_opt_4286_){
_start:
{
lean_object* v_name_4287_; lean_object* v_defValue_4288_; lean_object* v_map_4289_; lean_object* v___x_4290_; 
v_name_4287_ = lean_ctor_get(v_opt_4286_, 0);
v_defValue_4288_ = lean_ctor_get(v_opt_4286_, 1);
v_map_4289_ = lean_ctor_get(v_opts_4285_, 0);
v___x_4290_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4289_, v_name_4287_);
if (lean_obj_tag(v___x_4290_) == 0)
{
uint8_t v___x_4291_; 
v___x_4291_ = lean_unbox(v_defValue_4288_);
return v___x_4291_;
}
else
{
lean_object* v_val_4292_; 
v_val_4292_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_val_4292_);
lean_dec_ref(v___x_4290_);
if (lean_obj_tag(v_val_4292_) == 1)
{
uint8_t v_v_4293_; 
v_v_4293_ = lean_ctor_get_uint8(v_val_4292_, 0);
lean_dec_ref(v_val_4292_);
return v_v_4293_;
}
else
{
uint8_t v___x_4294_; 
lean_dec(v_val_4292_);
v___x_4294_ = lean_unbox(v_defValue_4288_);
return v___x_4294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21___boxed(lean_object* v_opts_4295_, lean_object* v_opt_4296_){
_start:
{
uint8_t v_res_4297_; lean_object* v_r_4298_; 
v_res_4297_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21(v_opts_4295_, v_opt_4296_);
lean_dec_ref(v_opt_4296_);
lean_dec_ref(v_opts_4295_);
v_r_4298_ = lean_box(v_res_4297_);
return v_r_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17(lean_object* v_ref_4300_, lean_object* v_msgData_4301_, uint8_t v_severity_4302_, uint8_t v_isSilent_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v___y_4308_; lean_object* v___y_4309_; uint8_t v___y_4310_; uint8_t v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; uint8_t v___y_4371_; lean_object* v___y_4372_; uint8_t v___y_4373_; uint8_t v___y_4374_; lean_object* v___y_4375_; uint8_t v___y_4399_; uint8_t v___y_4400_; uint8_t v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; uint8_t v___y_4407_; uint8_t v___y_4408_; uint8_t v___y_4409_; uint8_t v___x_4424_; uint8_t v___y_4426_; uint8_t v___y_4427_; uint8_t v___y_4428_; uint8_t v___y_4430_; uint8_t v___x_4442_; 
v___x_4424_ = 2;
v___x_4442_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4302_, v___x_4424_);
if (v___x_4442_ == 0)
{
v___y_4430_ = v___x_4442_;
goto v___jp_4429_;
}
else
{
uint8_t v___x_4443_; 
lean_inc_ref(v_msgData_4301_);
v___x_4443_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4301_);
v___y_4430_ = v___x_4443_;
goto v___jp_4429_;
}
v___jp_4307_:
{
lean_object* v___x_4316_; 
v___x_4316_ = l_Lean_Elab_Command_getScope___redArg(v___y_4315_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; lean_object* v___x_4318_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref(v___x_4316_);
v___x_4318_ = l_Lean_Elab_Command_getScope___redArg(v___y_4315_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4353_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4321_ = v___x_4318_;
v_isShared_4322_ = v_isSharedCheck_4353_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4318_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4353_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4323_; lean_object* v_currNamespace_4324_; lean_object* v_openDecls_4325_; lean_object* v_env_4326_; lean_object* v_messages_4327_; lean_object* v_scopes_4328_; lean_object* v_usedQuotCtxts_4329_; lean_object* v_nextMacroScope_4330_; lean_object* v_maxRecDepth_4331_; lean_object* v_ngen_4332_; lean_object* v_auxDeclNGen_4333_; lean_object* v_infoState_4334_; lean_object* v_traceState_4335_; lean_object* v_snapshotTasks_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4352_; 
v___x_4323_ = lean_st_ref_take(v___y_4315_);
v_currNamespace_4324_ = lean_ctor_get(v_a_4317_, 2);
lean_inc(v_currNamespace_4324_);
lean_dec(v_a_4317_);
v_openDecls_4325_ = lean_ctor_get(v_a_4319_, 3);
lean_inc(v_openDecls_4325_);
lean_dec(v_a_4319_);
v_env_4326_ = lean_ctor_get(v___x_4323_, 0);
v_messages_4327_ = lean_ctor_get(v___x_4323_, 1);
v_scopes_4328_ = lean_ctor_get(v___x_4323_, 2);
v_usedQuotCtxts_4329_ = lean_ctor_get(v___x_4323_, 3);
v_nextMacroScope_4330_ = lean_ctor_get(v___x_4323_, 4);
v_maxRecDepth_4331_ = lean_ctor_get(v___x_4323_, 5);
v_ngen_4332_ = lean_ctor_get(v___x_4323_, 6);
v_auxDeclNGen_4333_ = lean_ctor_get(v___x_4323_, 7);
v_infoState_4334_ = lean_ctor_get(v___x_4323_, 8);
v_traceState_4335_ = lean_ctor_get(v___x_4323_, 9);
v_snapshotTasks_4336_ = lean_ctor_get(v___x_4323_, 10);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4338_ = v___x_4323_;
v_isShared_4339_ = v_isSharedCheck_4352_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_snapshotTasks_4336_);
lean_inc(v_traceState_4335_);
lean_inc(v_infoState_4334_);
lean_inc(v_auxDeclNGen_4333_);
lean_inc(v_ngen_4332_);
lean_inc(v_maxRecDepth_4331_);
lean_inc(v_nextMacroScope_4330_);
lean_inc(v_usedQuotCtxts_4329_);
lean_inc(v_scopes_4328_);
lean_inc(v_messages_4327_);
lean_inc(v_env_4326_);
lean_dec(v___x_4323_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4352_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4345_; 
v___x_4340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4340_, 0, v_currNamespace_4324_);
lean_ctor_set(v___x_4340_, 1, v_openDecls_4325_);
v___x_4341_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4340_);
lean_ctor_set(v___x_4341_, 1, v___y_4309_);
v___x_4342_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4342_, 0, v___y_4313_);
lean_ctor_set(v___x_4342_, 1, v___y_4312_);
lean_ctor_set(v___x_4342_, 2, v___y_4308_);
lean_ctor_set(v___x_4342_, 3, v___y_4314_);
lean_ctor_set(v___x_4342_, 4, v___x_4341_);
lean_ctor_set_uint8(v___x_4342_, sizeof(void*)*5, v___y_4310_);
lean_ctor_set_uint8(v___x_4342_, sizeof(void*)*5 + 1, v___y_4311_);
lean_ctor_set_uint8(v___x_4342_, sizeof(void*)*5 + 2, v_isSilent_4303_);
v___x_4343_ = l_Lean_MessageLog_add(v___x_4342_, v_messages_4327_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 1, v___x_4343_);
v___x_4345_ = v___x_4338_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v_env_4326_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v___x_4343_);
lean_ctor_set(v_reuseFailAlloc_4351_, 2, v_scopes_4328_);
lean_ctor_set(v_reuseFailAlloc_4351_, 3, v_usedQuotCtxts_4329_);
lean_ctor_set(v_reuseFailAlloc_4351_, 4, v_nextMacroScope_4330_);
lean_ctor_set(v_reuseFailAlloc_4351_, 5, v_maxRecDepth_4331_);
lean_ctor_set(v_reuseFailAlloc_4351_, 6, v_ngen_4332_);
lean_ctor_set(v_reuseFailAlloc_4351_, 7, v_auxDeclNGen_4333_);
lean_ctor_set(v_reuseFailAlloc_4351_, 8, v_infoState_4334_);
lean_ctor_set(v_reuseFailAlloc_4351_, 9, v_traceState_4335_);
lean_ctor_set(v_reuseFailAlloc_4351_, 10, v_snapshotTasks_4336_);
v___x_4345_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4349_; 
v___x_4346_ = lean_st_ref_set(v___y_4315_, v___x_4345_);
v___x_4347_ = lean_box(0);
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 0, v___x_4347_);
v___x_4349_ = v___x_4321_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
}
else
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4361_; 
lean_dec(v_a_4317_);
lean_dec_ref(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec_ref(v___y_4309_);
lean_dec(v___y_4308_);
v_a_4354_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4356_ = v___x_4318_;
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4318_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4359_; 
if (v_isShared_4357_ == 0)
{
v___x_4359_ = v___x_4356_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_a_4354_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
else
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4369_; 
lean_dec_ref(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec_ref(v___y_4309_);
lean_dec(v___y_4308_);
v_a_4362_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4364_ = v___x_4316_;
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4316_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4367_; 
if (v_isShared_4365_ == 0)
{
v___x_4367_ = v___x_4364_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
v___jp_4370_:
{
lean_object* v_fileName_4376_; lean_object* v_fileMap_4377_; uint8_t v_suppressElabErrors_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4397_; 
v_fileName_4376_ = lean_ctor_get(v___y_4304_, 0);
lean_inc_ref(v_fileName_4376_);
v_fileMap_4377_ = lean_ctor_get(v___y_4304_, 1);
lean_inc_ref(v_fileMap_4377_);
v_suppressElabErrors_4378_ = lean_ctor_get_uint8(v___y_4304_, sizeof(void*)*10);
lean_dec_ref(v___y_4304_);
v___x_4379_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4301_);
v___x_4380_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(v___x_4379_, v___y_4305_);
v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4383_ = v___x_4380_;
v_isShared_4384_ = v_isSharedCheck_4397_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4380_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4397_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
lean_inc_ref(v_fileMap_4377_);
v___x_4385_ = l_Lean_FileMap_toPosition(v_fileMap_4377_, v___y_4372_);
lean_dec(v___y_4372_);
v___x_4386_ = l_Lean_FileMap_toPosition(v_fileMap_4377_, v___y_4375_);
lean_dec(v___y_4375_);
v___x_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4386_);
v___x_4388_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
if (v_suppressElabErrors_4378_ == 0)
{
lean_del_object(v___x_4383_);
v___y_4308_ = v___x_4387_;
v___y_4309_ = v_a_4381_;
v___y_4310_ = v___y_4373_;
v___y_4311_ = v___y_4374_;
v___y_4312_ = v___x_4385_;
v___y_4313_ = v_fileName_4376_;
v___y_4314_ = v___x_4388_;
v___y_4315_ = v___y_4305_;
goto v___jp_4307_;
}
else
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___f_4391_; uint8_t v___x_4392_; 
v___x_4389_ = lean_box(v___y_4371_);
v___x_4390_ = lean_box(v_suppressElabErrors_4378_);
v___f_4391_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4391_, 0, v___x_4389_);
lean_closure_set(v___f_4391_, 1, v___x_4390_);
lean_inc(v_a_4381_);
v___x_4392_ = l_Lean_MessageData_hasTag(v___f_4391_, v_a_4381_);
if (v___x_4392_ == 0)
{
lean_object* v___x_4393_; lean_object* v___x_4395_; 
lean_dec_ref(v___x_4387_);
lean_dec_ref(v___x_4385_);
lean_dec(v_a_4381_);
lean_dec_ref(v_fileName_4376_);
v___x_4393_ = lean_box(0);
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 0, v___x_4393_);
v___x_4395_ = v___x_4383_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
else
{
lean_del_object(v___x_4383_);
v___y_4308_ = v___x_4387_;
v___y_4309_ = v_a_4381_;
v___y_4310_ = v___y_4373_;
v___y_4311_ = v___y_4374_;
v___y_4312_ = v___x_4385_;
v___y_4313_ = v_fileName_4376_;
v___y_4314_ = v___x_4388_;
v___y_4315_ = v___y_4305_;
goto v___jp_4307_;
}
}
}
}
v___jp_4398_:
{
lean_object* v___x_4404_; 
v___x_4404_ = l_Lean_Syntax_getTailPos_x3f(v___y_4402_, v___y_4400_);
lean_dec(v___y_4402_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_inc(v___y_4403_);
v___y_4371_ = v___y_4399_;
v___y_4372_ = v___y_4403_;
v___y_4373_ = v___y_4400_;
v___y_4374_ = v___y_4401_;
v___y_4375_ = v___y_4403_;
goto v___jp_4370_;
}
else
{
lean_object* v_val_4405_; 
v_val_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_val_4405_);
lean_dec_ref(v___x_4404_);
v___y_4371_ = v___y_4399_;
v___y_4372_ = v___y_4403_;
v___y_4373_ = v___y_4400_;
v___y_4374_ = v___y_4401_;
v___y_4375_ = v_val_4405_;
goto v___jp_4370_;
}
}
v___jp_4406_:
{
lean_object* v___x_4410_; 
v___x_4410_ = l_Lean_Elab_Command_getRef___redArg(v___y_4304_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v_ref_4412_; lean_object* v___x_4413_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref(v___x_4410_);
v_ref_4412_ = l_Lean_replaceRef(v_ref_4300_, v_a_4411_);
lean_dec(v_a_4411_);
v___x_4413_ = l_Lean_Syntax_getPos_x3f(v_ref_4412_, v___y_4408_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v___x_4414_; 
v___x_4414_ = lean_unsigned_to_nat(0u);
v___y_4399_ = v___y_4407_;
v___y_4400_ = v___y_4408_;
v___y_4401_ = v___y_4409_;
v___y_4402_ = v_ref_4412_;
v___y_4403_ = v___x_4414_;
goto v___jp_4398_;
}
else
{
lean_object* v_val_4415_; 
v_val_4415_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_val_4415_);
lean_dec_ref(v___x_4413_);
v___y_4399_ = v___y_4407_;
v___y_4400_ = v___y_4408_;
v___y_4401_ = v___y_4409_;
v___y_4402_ = v_ref_4412_;
v___y_4403_ = v_val_4415_;
goto v___jp_4398_;
}
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_dec_ref(v___y_4304_);
lean_dec_ref(v_msgData_4301_);
v_a_4416_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4410_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4410_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
v___jp_4425_:
{
if (v___y_4428_ == 0)
{
v___y_4407_ = v___y_4426_;
v___y_4408_ = v___y_4427_;
v___y_4409_ = v_severity_4302_;
goto v___jp_4406_;
}
else
{
v___y_4407_ = v___y_4426_;
v___y_4408_ = v___y_4427_;
v___y_4409_ = v___x_4424_;
goto v___jp_4406_;
}
}
v___jp_4429_:
{
if (v___y_4430_ == 0)
{
lean_object* v___x_4431_; lean_object* v_scopes_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v_opts_4435_; uint8_t v___x_4436_; uint8_t v___x_4437_; 
v___x_4431_ = lean_st_ref_get(v___y_4305_);
v_scopes_4432_ = lean_ctor_get(v___x_4431_, 2);
lean_inc(v_scopes_4432_);
lean_dec(v___x_4431_);
v___x_4433_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4434_ = l_List_head_x21___redArg(v___x_4433_, v_scopes_4432_);
lean_dec(v_scopes_4432_);
v_opts_4435_ = lean_ctor_get(v___x_4434_, 1);
lean_inc_ref(v_opts_4435_);
lean_dec(v___x_4434_);
v___x_4436_ = 1;
v___x_4437_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4302_, v___x_4436_);
if (v___x_4437_ == 0)
{
lean_dec_ref(v_opts_4435_);
v___y_4426_ = v___y_4430_;
v___y_4427_ = v___y_4430_;
v___y_4428_ = v___x_4437_;
goto v___jp_4425_;
}
else
{
lean_object* v___x_4438_; uint8_t v___x_4439_; 
v___x_4438_ = l_Lean_warningAsError;
v___x_4439_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21(v_opts_4435_, v___x_4438_);
lean_dec_ref(v_opts_4435_);
v___y_4426_ = v___y_4430_;
v___y_4427_ = v___y_4430_;
v___y_4428_ = v___x_4439_;
goto v___jp_4425_;
}
}
else
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
lean_dec_ref(v___y_4304_);
lean_dec_ref(v_msgData_4301_);
v___x_4440_ = lean_box(0);
v___x_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
return v___x_4441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___boxed(lean_object* v_ref_4444_, lean_object* v_msgData_4445_, lean_object* v_severity_4446_, lean_object* v_isSilent_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
uint8_t v_severity_boxed_4451_; uint8_t v_isSilent_boxed_4452_; lean_object* v_res_4453_; 
v_severity_boxed_4451_ = lean_unbox(v_severity_4446_);
v_isSilent_boxed_4452_ = lean_unbox(v_isSilent_4447_);
v_res_4453_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17(v_ref_4444_, v_msgData_4445_, v_severity_boxed_4451_, v_isSilent_boxed_4452_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec(v_ref_4444_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11(lean_object* v_msgData_4454_, uint8_t v_severity_4455_, uint8_t v_isSilent_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v___x_4460_; 
v___x_4460_ = l_Lean_Elab_Command_getRef___redArg(v___y_4457_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4462_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4461_);
lean_dec_ref(v___x_4460_);
v___x_4462_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17(v_a_4461_, v_msgData_4454_, v_severity_4455_, v_isSilent_4456_, v___y_4457_, v___y_4458_);
lean_dec(v_a_4461_);
return v___x_4462_;
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_dec_ref(v___y_4457_);
lean_dec_ref(v_msgData_4454_);
v_a_4463_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4460_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4460_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11___boxed(lean_object* v_msgData_4471_, lean_object* v_severity_4472_, lean_object* v_isSilent_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
uint8_t v_severity_boxed_4477_; uint8_t v_isSilent_boxed_4478_; lean_object* v_res_4479_; 
v_severity_boxed_4477_ = lean_unbox(v_severity_4472_);
v_isSilent_boxed_4478_ = lean_unbox(v_isSilent_4473_);
v_res_4479_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11(v_msgData_4471_, v_severity_boxed_4477_, v_isSilent_boxed_4478_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3(lean_object* v_msgData_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
uint8_t v___x_4484_; uint8_t v___x_4485_; lean_object* v___x_4486_; 
v___x_4484_ = 1;
v___x_4485_ = 0;
v___x_4486_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11(v_msgData_4480_, v___x_4484_, v___x_4485_, v___y_4481_, v___y_4482_);
return v___x_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3___boxed(lean_object* v_msgData_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l_Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3(v_msgData_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(lean_object* v_x_4492_, lean_object* v___y_4493_){
_start:
{
if (lean_obj_tag(v_x_4492_) == 0)
{
lean_object* v_a_4494_; lean_object* v___x_4495_; 
v_a_4494_ = lean_ctor_get(v_x_4492_, 0);
lean_inc(v_a_4494_);
v___x_4495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4495_, 0, v_a_4494_);
lean_ctor_set(v___x_4495_, 1, v___y_4493_);
return v___x_4495_;
}
else
{
lean_object* v_a_4496_; lean_object* v___x_4497_; 
v_a_4496_ = lean_ctor_get(v_x_4492_, 0);
lean_inc(v_a_4496_);
v___x_4497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4497_, 0, v_a_4496_);
lean_ctor_set(v___x_4497_, 1, v___y_4493_);
return v___x_4497_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg___boxed(lean_object* v_x_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(v_x_4498_, v___y_4499_);
lean_dec_ref(v_x_4498_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__1(lean_object* v_env_4501_, lean_object* v_stx_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v___x_4505_; 
v___x_4505_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_4501_, v_stx_4502_, v___y_4503_, v___y_4504_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4506_; 
v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
lean_inc(v_a_4506_);
if (lean_obj_tag(v_a_4506_) == 0)
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4515_; 
v_a_4507_ = lean_ctor_get(v___x_4505_, 1);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; 
v_unused_4516_ = lean_ctor_get(v___x_4505_, 0);
lean_dec(v_unused_4516_);
v___x_4509_ = v___x_4505_;
v_isShared_4510_ = v_isSharedCheck_4515_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4505_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4515_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4511_; lean_object* v___x_4513_; 
v___x_4511_ = lean_box(0);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 0, v___x_4511_);
v___x_4513_ = v___x_4509_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4511_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_a_4507_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
else
{
lean_object* v_val_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4545_; 
v_val_4517_ = lean_ctor_get(v_a_4506_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v_a_4506_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4519_ = v_a_4506_;
v_isShared_4520_ = v_isSharedCheck_4545_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_val_4517_);
lean_dec(v_a_4506_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4545_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v_snd_4521_; 
v_snd_4521_ = lean_ctor_get(v_val_4517_, 1);
lean_inc(v_snd_4521_);
lean_dec(v_val_4517_);
if (lean_obj_tag(v_snd_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4531_; 
lean_del_object(v___x_4519_);
v_a_4522_ = lean_ctor_get(v___x_4505_, 1);
lean_inc(v_a_4522_);
lean_dec_ref(v___x_4505_);
v_a_4523_ = lean_ctor_get(v_snd_4521_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v_snd_4521_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4525_ = v_snd_4521_;
v_isShared_4526_ = v_isSharedCheck_4531_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v_snd_4521_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4531_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
lean_object* v___x_4529_; 
v___x_4529_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(v___x_4528_, v_a_4522_);
lean_dec_ref(v___x_4528_);
return v___x_4529_;
}
}
}
else
{
lean_object* v_a_4532_; lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4544_; 
v_a_4532_ = lean_ctor_get(v___x_4505_, 1);
lean_inc(v_a_4532_);
lean_dec_ref(v___x_4505_);
v_a_4533_ = lean_ctor_get(v_snd_4521_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v_snd_4521_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4535_ = v_snd_4521_;
v_isShared_4536_ = v_isSharedCheck_4544_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v_snd_4521_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4544_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4520_ == 0)
{
lean_ctor_set(v___x_4519_, 0, v_a_4533_);
v___x_4538_ = v___x_4519_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4533_);
v___x_4538_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
lean_object* v___x_4540_; 
if (v_isShared_4536_ == 0)
{
lean_ctor_set(v___x_4535_, 0, v___x_4538_);
v___x_4540_ = v___x_4535_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4538_);
v___x_4540_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
lean_object* v___x_4541_; 
v___x_4541_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(v___x_4540_, v_a_4532_);
lean_dec_ref(v___x_4540_);
return v___x_4541_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4546_; lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4554_; 
v_a_4546_ = lean_ctor_get(v___x_4505_, 0);
v_a_4547_ = lean_ctor_get(v___x_4505_, 1);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4549_ = v___x_4505_;
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_inc(v_a_4546_);
lean_dec(v___x_4505_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4552_; 
if (v_isShared_4550_ == 0)
{
v___x_4552_ = v___x_4549_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4546_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_a_4547_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__1___boxed(lean_object* v_env_4555_, lean_object* v_stx_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__1(v_env_4555_, v_stx_4556_, v___y_4557_, v___y_4558_);
lean_dec_ref(v___y_4557_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__3(lean_object* v_env_4560_, lean_object* v_currNamespace_4561_, lean_object* v_openDecls_4562_, lean_object* v_n_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4566_ = l_Lean_ResolveName_resolveNamespace(v_env_4560_, v_currNamespace_4561_, v_openDecls_4562_, v_n_4563_);
v___x_4567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4566_);
lean_ctor_set(v___x_4567_, 1, v___y_4565_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__3___boxed(lean_object* v_env_4568_, lean_object* v_currNamespace_4569_, lean_object* v_openDecls_4570_, lean_object* v_n_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__3(v_env_4568_, v_currNamespace_4569_, v_openDecls_4570_, v_n_4571_, v___y_4572_, v___y_4573_);
lean_dec_ref(v___y_4572_);
return v_res_4574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__0(lean_object* v_env_4575_, lean_object* v_declName_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
uint8_t v___x_4579_; lean_object* v_env_4580_; lean_object* v___x_4581_; uint8_t v___x_4582_; uint8_t v___x_4583_; 
v___x_4579_ = 0;
v_env_4580_ = l_Lean_Environment_setExporting(v_env_4575_, v___x_4579_);
lean_inc(v_declName_4576_);
v___x_4581_ = l_Lean_mkPrivateName(v_env_4580_, v_declName_4576_);
v___x_4582_ = 1;
lean_inc_ref(v_env_4580_);
v___x_4583_ = l_Lean_Environment_contains(v_env_4580_, v___x_4581_, v___x_4582_);
if (v___x_4583_ == 0)
{
lean_object* v___x_4584_; uint8_t v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4584_ = l_Lean_privateToUserName(v_declName_4576_);
v___x_4585_ = l_Lean_Environment_contains(v_env_4580_, v___x_4584_, v___x_4582_);
v___x_4586_ = lean_box(v___x_4585_);
v___x_4587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4586_);
lean_ctor_set(v___x_4587_, 1, v___y_4578_);
return v___x_4587_;
}
else
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
lean_dec_ref(v_env_4580_);
lean_dec(v_declName_4576_);
v___x_4588_ = lean_box(v___x_4583_);
v___x_4589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
lean_ctor_set(v___x_4589_, 1, v___y_4578_);
return v___x_4589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__0___boxed(lean_object* v_env_4590_, lean_object* v_declName_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__0(v_env_4590_, v_declName_4591_, v___y_4592_, v___y_4593_);
lean_dec_ref(v___y_4592_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* v_a_4595_, lean_object* v_x_4596_){
_start:
{
if (lean_obj_tag(v_x_4596_) == 0)
{
lean_object* v___x_4597_; 
v___x_4597_ = lean_box(0);
return v___x_4597_;
}
else
{
lean_object* v_key_4598_; lean_object* v_value_4599_; lean_object* v_tail_4600_; uint8_t v___x_4601_; 
v_key_4598_ = lean_ctor_get(v_x_4596_, 0);
v_value_4599_ = lean_ctor_get(v_x_4596_, 1);
v_tail_4600_ = lean_ctor_get(v_x_4596_, 2);
v___x_4601_ = lean_name_eq(v_key_4598_, v_a_4595_);
if (v___x_4601_ == 0)
{
v_x_4596_ = v_tail_4600_;
goto _start;
}
else
{
lean_object* v___x_4603_; 
lean_inc(v_value_4599_);
v___x_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4603_, 0, v_value_4599_);
return v___x_4603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg___boxed(lean_object* v_a_4604_, lean_object* v_x_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg(v_a_4604_, v_x_4605_);
lean_dec(v_x_4605_);
lean_dec(v_a_4604_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg(lean_object* v_m_4607_, lean_object* v_a_4608_){
_start:
{
lean_object* v_buckets_4609_; lean_object* v___x_4610_; uint64_t v___y_4612_; 
v_buckets_4609_ = lean_ctor_get(v_m_4607_, 1);
v___x_4610_ = lean_array_get_size(v_buckets_4609_);
if (lean_obj_tag(v_a_4608_) == 0)
{
uint64_t v___x_4626_; 
v___x_4626_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg___closed__0);
v___y_4612_ = v___x_4626_;
goto v___jp_4611_;
}
else
{
uint64_t v_hash_4627_; 
v_hash_4627_ = lean_ctor_get_uint64(v_a_4608_, sizeof(void*)*2);
v___y_4612_ = v_hash_4627_;
goto v___jp_4611_;
}
v___jp_4611_:
{
uint64_t v___x_4613_; uint64_t v___x_4614_; uint64_t v_fold_4615_; uint64_t v___x_4616_; uint64_t v___x_4617_; uint64_t v___x_4618_; size_t v___x_4619_; size_t v___x_4620_; size_t v___x_4621_; size_t v___x_4622_; size_t v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4613_ = 32ULL;
v___x_4614_ = lean_uint64_shift_right(v___y_4612_, v___x_4613_);
v_fold_4615_ = lean_uint64_xor(v___y_4612_, v___x_4614_);
v___x_4616_ = 16ULL;
v___x_4617_ = lean_uint64_shift_right(v_fold_4615_, v___x_4616_);
v___x_4618_ = lean_uint64_xor(v_fold_4615_, v___x_4617_);
v___x_4619_ = lean_uint64_to_usize(v___x_4618_);
v___x_4620_ = lean_usize_of_nat(v___x_4610_);
v___x_4621_ = ((size_t)1ULL);
v___x_4622_ = lean_usize_sub(v___x_4620_, v___x_4621_);
v___x_4623_ = lean_usize_land(v___x_4619_, v___x_4622_);
v___x_4624_ = lean_array_uget_borrowed(v_buckets_4609_, v___x_4623_);
v___x_4625_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg(v_a_4608_, v___x_4624_);
return v___x_4625_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg___boxed(lean_object* v_m_4628_, lean_object* v_a_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg(v_m_4628_, v_a_4629_);
lean_dec(v_a_4629_);
lean_dec_ref(v_m_4628_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg(lean_object* v_cls_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v_scopes_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v_opts_4642_; uint8_t v_hasTrace_4643_; 
v___x_4636_ = l_Lean_inheritedTraceOptions;
v___x_4637_ = lean_st_ref_get(v___x_4636_);
v___x_4638_ = lean_st_ref_get(v___y_4634_);
v_scopes_4639_ = lean_ctor_get(v___x_4638_, 2);
lean_inc(v_scopes_4639_);
lean_dec(v___x_4638_);
v___x_4640_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4641_ = l_List_head_x21___redArg(v___x_4640_, v_scopes_4639_);
lean_dec(v_scopes_4639_);
v_opts_4642_ = lean_ctor_get(v___x_4641_, 1);
lean_inc_ref(v_opts_4642_);
lean_dec(v___x_4641_);
v_hasTrace_4643_ = lean_ctor_get_uint8(v_opts_4642_, sizeof(void*)*1);
if (v_hasTrace_4643_ == 0)
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
lean_dec_ref(v_opts_4642_);
lean_dec(v___x_4637_);
lean_dec(v_cls_4633_);
v___x_4644_ = lean_box(v_hasTrace_4643_);
v___x_4645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4644_);
return v___x_4645_;
}
else
{
lean_object* v___x_4646_; lean_object* v___x_4647_; uint8_t v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4646_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg___closed__0));
v___x_4647_ = l_Lean_Name_append(v___x_4646_, v_cls_4633_);
v___x_4648_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_4637_, v_opts_4642_, v___x_4647_);
lean_dec(v___x_4647_);
lean_dec_ref(v_opts_4642_);
lean_dec(v___x_4637_);
v___x_4649_ = lean_box(v___x_4648_);
v___x_4650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4649_);
return v___x_4650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg___boxed(lean_object* v_cls_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg(v_cls_4651_, v___y_4652_);
lean_dec(v___y_4652_);
return v_res_4654_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg(lean_object* v_keys_4655_, lean_object* v_i_4656_, lean_object* v_k_4657_){
_start:
{
lean_object* v___x_4658_; uint8_t v___x_4659_; 
v___x_4658_ = lean_array_get_size(v_keys_4655_);
v___x_4659_ = lean_nat_dec_lt(v_i_4656_, v___x_4658_);
if (v___x_4659_ == 0)
{
lean_dec(v_i_4656_);
return v___x_4659_;
}
else
{
lean_object* v_k_x27_4660_; uint8_t v___x_4661_; 
v_k_x27_4660_ = lean_array_fget_borrowed(v_keys_4655_, v_i_4656_);
v___x_4661_ = l_Lean_instBEqExtraModUse_beq(v_k_4657_, v_k_x27_4660_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4662_ = lean_unsigned_to_nat(1u);
v___x_4663_ = lean_nat_add(v_i_4656_, v___x_4662_);
lean_dec(v_i_4656_);
v_i_4656_ = v___x_4663_;
goto _start;
}
else
{
lean_dec(v_i_4656_);
return v___x_4661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg___boxed(lean_object* v_keys_4665_, lean_object* v_i_4666_, lean_object* v_k_4667_){
_start:
{
uint8_t v_res_4668_; lean_object* v_r_4669_; 
v_res_4668_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg(v_keys_4665_, v_i_4666_, v_k_4667_);
lean_dec_ref(v_k_4667_);
lean_dec_ref(v_keys_4665_);
v_r_4669_ = lean_box(v_res_4668_);
return v_r_4669_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__0(void){
_start:
{
size_t v___x_4670_; size_t v___x_4671_; size_t v___x_4672_; 
v___x_4670_ = ((size_t)5ULL);
v___x_4671_ = ((size_t)1ULL);
v___x_4672_ = lean_usize_shift_left(v___x_4671_, v___x_4670_);
return v___x_4672_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__1(void){
_start:
{
size_t v___x_4673_; size_t v___x_4674_; size_t v___x_4675_; 
v___x_4673_ = ((size_t)1ULL);
v___x_4674_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__0);
v___x_4675_ = lean_usize_sub(v___x_4674_, v___x_4673_);
return v___x_4675_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg(lean_object* v_x_4676_, size_t v_x_4677_, lean_object* v_x_4678_){
_start:
{
if (lean_obj_tag(v_x_4676_) == 0)
{
lean_object* v_es_4679_; lean_object* v___x_4680_; size_t v___x_4681_; size_t v___x_4682_; size_t v___x_4683_; lean_object* v_j_4684_; lean_object* v___x_4685_; 
v_es_4679_ = lean_ctor_get(v_x_4676_, 0);
lean_inc_ref(v_es_4679_);
lean_dec_ref(v_x_4676_);
v___x_4680_ = lean_box(2);
v___x_4681_ = ((size_t)5ULL);
v___x_4682_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__1);
v___x_4683_ = lean_usize_land(v_x_4677_, v___x_4682_);
v_j_4684_ = lean_usize_to_nat(v___x_4683_);
v___x_4685_ = lean_array_get(v___x_4680_, v_es_4679_, v_j_4684_);
lean_dec(v_j_4684_);
lean_dec_ref(v_es_4679_);
switch(lean_obj_tag(v___x_4685_))
{
case 0:
{
lean_object* v_key_4686_; uint8_t v___x_4687_; 
v_key_4686_ = lean_ctor_get(v___x_4685_, 0);
lean_inc(v_key_4686_);
lean_dec_ref(v___x_4685_);
v___x_4687_ = l_Lean_instBEqExtraModUse_beq(v_x_4678_, v_key_4686_);
lean_dec(v_key_4686_);
return v___x_4687_;
}
case 1:
{
lean_object* v_node_4688_; size_t v___x_4689_; 
v_node_4688_ = lean_ctor_get(v___x_4685_, 0);
lean_inc(v_node_4688_);
lean_dec_ref(v___x_4685_);
v___x_4689_ = lean_usize_shift_right(v_x_4677_, v___x_4681_);
v_x_4676_ = v_node_4688_;
v_x_4677_ = v___x_4689_;
goto _start;
}
default: 
{
uint8_t v___x_4691_; 
v___x_4691_ = 0;
return v___x_4691_;
}
}
}
else
{
lean_object* v_ks_4692_; lean_object* v___x_4693_; uint8_t v___x_4694_; 
v_ks_4692_ = lean_ctor_get(v_x_4676_, 0);
lean_inc_ref(v_ks_4692_);
lean_dec_ref(v_x_4676_);
v___x_4693_ = lean_unsigned_to_nat(0u);
v___x_4694_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg(v_ks_4692_, v___x_4693_, v_x_4678_);
lean_dec_ref(v_ks_4692_);
return v___x_4694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object* v_x_4695_, lean_object* v_x_4696_, lean_object* v_x_4697_){
_start:
{
size_t v_x_15416__boxed_4698_; uint8_t v_res_4699_; lean_object* v_r_4700_; 
v_x_15416__boxed_4698_ = lean_unbox_usize(v_x_4696_);
lean_dec(v_x_4696_);
v_res_4699_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg(v_x_4695_, v_x_15416__boxed_4698_, v_x_4697_);
lean_dec_ref(v_x_4697_);
v_r_4700_ = lean_box(v_res_4699_);
return v_r_4700_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg(lean_object* v_x_4701_, lean_object* v_x_4702_){
_start:
{
uint64_t v___x_4703_; size_t v___x_4704_; uint8_t v___x_4705_; 
v___x_4703_ = l_Lean_instHashableExtraModUse_hash(v_x_4702_);
v___x_4704_ = lean_uint64_to_usize(v___x_4703_);
v___x_4705_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg(v_x_4701_, v___x_4704_, v_x_4702_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_x_4706_, lean_object* v_x_4707_){
_start:
{
uint8_t v_res_4708_; lean_object* v_r_4709_; 
v_res_4708_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg(v_x_4706_, v_x_4707_);
lean_dec_ref(v_x_4707_);
v_r_4709_ = lean_box(v_res_4708_);
return v_r_4709_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4710_; double v___x_4711_; 
v___x_4710_ = lean_unsigned_to_nat(0u);
v___x_4711_ = lean_float_of_nat(v___x_4710_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2(lean_object* v_cls_4714_, lean_object* v_msg_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l_Lean_Elab_Command_getRef___redArg(v___y_4716_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v_a_4720_; lean_object* v___x_4721_; lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4768_; 
v_a_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_a_4720_);
lean_dec_ref(v___x_4719_);
v___x_4721_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(v_msg_4715_, v___y_4717_);
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4724_ = v___x_4721_;
v_isShared_4725_ = v_isSharedCheck_4768_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4721_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4768_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4726_; lean_object* v_traceState_4727_; lean_object* v_env_4728_; lean_object* v_messages_4729_; lean_object* v_scopes_4730_; lean_object* v_usedQuotCtxts_4731_; lean_object* v_nextMacroScope_4732_; lean_object* v_maxRecDepth_4733_; lean_object* v_ngen_4734_; lean_object* v_auxDeclNGen_4735_; lean_object* v_infoState_4736_; lean_object* v_snapshotTasks_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4767_; 
v___x_4726_ = lean_st_ref_take(v___y_4717_);
v_traceState_4727_ = lean_ctor_get(v___x_4726_, 9);
v_env_4728_ = lean_ctor_get(v___x_4726_, 0);
v_messages_4729_ = lean_ctor_get(v___x_4726_, 1);
v_scopes_4730_ = lean_ctor_get(v___x_4726_, 2);
v_usedQuotCtxts_4731_ = lean_ctor_get(v___x_4726_, 3);
v_nextMacroScope_4732_ = lean_ctor_get(v___x_4726_, 4);
v_maxRecDepth_4733_ = lean_ctor_get(v___x_4726_, 5);
v_ngen_4734_ = lean_ctor_get(v___x_4726_, 6);
v_auxDeclNGen_4735_ = lean_ctor_get(v___x_4726_, 7);
v_infoState_4736_ = lean_ctor_get(v___x_4726_, 8);
v_snapshotTasks_4737_ = lean_ctor_get(v___x_4726_, 10);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4739_ = v___x_4726_;
v_isShared_4740_ = v_isSharedCheck_4767_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_snapshotTasks_4737_);
lean_inc(v_traceState_4727_);
lean_inc(v_infoState_4736_);
lean_inc(v_auxDeclNGen_4735_);
lean_inc(v_ngen_4734_);
lean_inc(v_maxRecDepth_4733_);
lean_inc(v_nextMacroScope_4732_);
lean_inc(v_usedQuotCtxts_4731_);
lean_inc(v_scopes_4730_);
lean_inc(v_messages_4729_);
lean_inc(v_env_4728_);
lean_dec(v___x_4726_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4767_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
uint64_t v_tid_4741_; lean_object* v_traces_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4766_; 
v_tid_4741_ = lean_ctor_get_uint64(v_traceState_4727_, sizeof(void*)*1);
v_traces_4742_ = lean_ctor_get(v_traceState_4727_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v_traceState_4727_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4744_ = v_traceState_4727_;
v_isShared_4745_ = v_isSharedCheck_4766_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_traces_4742_);
lean_dec(v_traceState_4727_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4766_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4746_; double v___x_4747_; uint8_t v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4756_; 
v___x_4746_ = lean_box(0);
v___x_4747_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0);
v___x_4748_ = 0;
v___x_4749_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
v___x_4750_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4750_, 0, v_cls_4714_);
lean_ctor_set(v___x_4750_, 1, v___x_4746_);
lean_ctor_set(v___x_4750_, 2, v___x_4749_);
lean_ctor_set_float(v___x_4750_, sizeof(void*)*3, v___x_4747_);
lean_ctor_set_float(v___x_4750_, sizeof(void*)*3 + 8, v___x_4747_);
lean_ctor_set_uint8(v___x_4750_, sizeof(void*)*3 + 16, v___x_4748_);
v___x_4751_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1));
v___x_4752_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4750_);
lean_ctor_set(v___x_4752_, 1, v_a_4722_);
lean_ctor_set(v___x_4752_, 2, v___x_4751_);
v___x_4753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4753_, 0, v_a_4720_);
lean_ctor_set(v___x_4753_, 1, v___x_4752_);
v___x_4754_ = l_Lean_PersistentArray_push___redArg(v_traces_4742_, v___x_4753_);
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 0, v___x_4754_);
v___x_4756_ = v___x_4744_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4754_);
lean_ctor_set_uint64(v_reuseFailAlloc_4765_, sizeof(void*)*1, v_tid_4741_);
v___x_4756_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
lean_object* v___x_4758_; 
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 9, v___x_4756_);
v___x_4758_ = v___x_4739_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_env_4728_);
lean_ctor_set(v_reuseFailAlloc_4764_, 1, v_messages_4729_);
lean_ctor_set(v_reuseFailAlloc_4764_, 2, v_scopes_4730_);
lean_ctor_set(v_reuseFailAlloc_4764_, 3, v_usedQuotCtxts_4731_);
lean_ctor_set(v_reuseFailAlloc_4764_, 4, v_nextMacroScope_4732_);
lean_ctor_set(v_reuseFailAlloc_4764_, 5, v_maxRecDepth_4733_);
lean_ctor_set(v_reuseFailAlloc_4764_, 6, v_ngen_4734_);
lean_ctor_set(v_reuseFailAlloc_4764_, 7, v_auxDeclNGen_4735_);
lean_ctor_set(v_reuseFailAlloc_4764_, 8, v_infoState_4736_);
lean_ctor_set(v_reuseFailAlloc_4764_, 9, v___x_4756_);
lean_ctor_set(v_reuseFailAlloc_4764_, 10, v_snapshotTasks_4737_);
v___x_4758_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4762_; 
v___x_4759_ = lean_st_ref_set(v___y_4717_, v___x_4758_);
v___x_4760_ = lean_box(0);
if (v_isShared_4725_ == 0)
{
lean_ctor_set(v___x_4724_, 0, v___x_4760_);
v___x_4762_ = v___x_4724_;
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
}
}
}
}
else
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4776_; 
lean_dec_ref(v_msg_4715_);
lean_dec(v_cls_4714_);
v_a_4769_ = lean_ctor_get(v___x_4719_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4771_ = v___x_4719_;
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4719_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4774_; 
if (v_isShared_4772_ == 0)
{
v___x_4774_ = v___x_4771_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4769_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___boxed(lean_object* v_cls_4777_, lean_object* v_msg_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2(v_cls_4777_, v_msg_4778_, v___y_4779_, v___y_4780_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
return v_res_4782_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__2(void){
_start:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4785_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__1));
v___x_4786_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__0));
v___x_4787_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_4786_, v___x_4785_);
return v___x_4787_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__6(void){
_start:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__5));
v___x_4793_ = l_Lean_stringToMessageData(v___x_4792_);
return v___x_4793_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__8(void){
_start:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; 
v___x_4795_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__7));
v___x_4796_ = l_Lean_stringToMessageData(v___x_4795_);
return v___x_4796_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__9(void){
_start:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___x_4797_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
v___x_4798_ = l_Lean_stringToMessageData(v___x_4797_);
return v___x_4798_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__11(void){
_start:
{
lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4800_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__10));
v___x_4801_ = l_Lean_stringToMessageData(v___x_4800_);
return v___x_4801_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__13(void){
_start:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4803_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__12));
v___x_4804_ = l_Lean_stringToMessageData(v___x_4803_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7(lean_object* v_mod_4809_, uint8_t v_isMeta_4810_, lean_object* v_hint_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v___x_4815_; lean_object* v_env_4816_; uint8_t v_isExporting_4817_; lean_object* v___x_4818_; lean_object* v_env_4819_; lean_object* v___x_4820_; lean_object* v_entry_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___y_4826_; lean_object* v___x_4852_; uint8_t v___x_4853_; 
v___x_4815_ = lean_st_ref_get(v___y_4813_);
v_env_4816_ = lean_ctor_get(v___x_4815_, 0);
lean_inc_ref(v_env_4816_);
lean_dec(v___x_4815_);
v_isExporting_4817_ = lean_ctor_get_uint8(v_env_4816_, sizeof(void*)*8);
lean_dec_ref(v_env_4816_);
v___x_4818_ = lean_st_ref_get(v___y_4813_);
v_env_4819_ = lean_ctor_get(v___x_4818_, 0);
lean_inc_ref(v_env_4819_);
lean_dec(v___x_4818_);
v___x_4820_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__2);
lean_inc(v_mod_4809_);
v_entry_4821_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_4821_, 0, v_mod_4809_);
lean_ctor_set_uint8(v_entry_4821_, sizeof(void*)*1, v_isExporting_4817_);
lean_ctor_set_uint8(v_entry_4821_, sizeof(void*)*1 + 1, v_isMeta_4810_);
v___x_4822_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_4823_ = lean_box(1);
v___x_4824_ = lean_box(0);
v___x_4852_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4820_, v___x_4822_, v_env_4819_, v___x_4823_, v___x_4824_);
v___x_4853_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg(v___x_4852_, v_entry_4821_);
if (v___x_4853_ == 0)
{
lean_object* v_cls_4854_; lean_object* v___x_4855_; lean_object* v_a_4856_; lean_object* v___y_4858_; lean_object* v___y_4859_; lean_object* v___y_4863_; lean_object* v___y_4864_; uint8_t v___x_4876_; 
v_cls_4854_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__4));
v___x_4855_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg(v_cls_4854_, v___y_4813_);
v_a_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc(v_a_4856_);
lean_dec_ref(v___x_4855_);
v___x_4876_ = lean_unbox(v_a_4856_);
lean_dec(v_a_4856_);
if (v___x_4876_ == 0)
{
lean_dec(v_hint_4811_);
lean_dec(v_mod_4809_);
v___y_4826_ = v___y_4813_;
goto v___jp_4825_;
}
else
{
lean_object* v___x_4877_; lean_object* v___y_4879_; 
v___x_4877_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__11);
if (v_isExporting_4817_ == 0)
{
lean_object* v___x_4886_; 
v___x_4886_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__16));
v___y_4879_ = v___x_4886_;
goto v___jp_4878_;
}
else
{
lean_object* v___x_4887_; 
v___x_4887_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__17));
v___y_4879_ = v___x_4887_;
goto v___jp_4878_;
}
v___jp_4878_:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4880_ = l_Lean_stringToMessageData(v___y_4879_);
v___x_4881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4877_);
lean_ctor_set(v___x_4881_, 1, v___x_4880_);
v___x_4882_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__13);
v___x_4883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4881_);
lean_ctor_set(v___x_4883_, 1, v___x_4882_);
if (v_isMeta_4810_ == 0)
{
lean_object* v___x_4884_; 
v___x_4884_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__14));
v___y_4863_ = v___x_4883_;
v___y_4864_ = v___x_4884_;
goto v___jp_4862_;
}
else
{
lean_object* v___x_4885_; 
v___x_4885_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__15));
v___y_4863_ = v___x_4883_;
v___y_4864_ = v___x_4885_;
goto v___jp_4862_;
}
}
}
v___jp_4857_:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4860_, 0, v___y_4858_);
lean_ctor_set(v___x_4860_, 1, v___y_4859_);
v___x_4861_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2(v_cls_4854_, v___x_4860_, v___y_4812_, v___y_4813_);
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_dec_ref(v___x_4861_);
v___y_4826_ = v___y_4813_;
goto v___jp_4825_;
}
else
{
lean_dec_ref(v_entry_4821_);
return v___x_4861_;
}
}
v___jp_4862_:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; uint8_t v___x_4871_; 
v___x_4865_ = l_Lean_stringToMessageData(v___y_4864_);
v___x_4866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4866_, 0, v___y_4863_);
lean_ctor_set(v___x_4866_, 1, v___x_4865_);
v___x_4867_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__6);
v___x_4868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4868_, 0, v___x_4866_);
lean_ctor_set(v___x_4868_, 1, v___x_4867_);
v___x_4869_ = l_Lean_MessageData_ofName(v_mod_4809_);
v___x_4870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4868_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
v___x_4871_ = l_Lean_Name_isAnonymous(v_hint_4811_);
if (v___x_4871_ == 0)
{
lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4872_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__8);
v___x_4873_ = l_Lean_MessageData_ofName(v_hint_4811_);
v___x_4874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4872_);
lean_ctor_set(v___x_4874_, 1, v___x_4873_);
v___y_4858_ = v___x_4870_;
v___y_4859_ = v___x_4874_;
goto v___jp_4857_;
}
else
{
lean_object* v___x_4875_; 
lean_dec(v_hint_4811_);
v___x_4875_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__9);
v___y_4858_ = v___x_4870_;
v___y_4859_ = v___x_4875_;
goto v___jp_4857_;
}
}
}
else
{
lean_object* v___x_4888_; lean_object* v___x_4889_; 
lean_dec_ref(v_entry_4821_);
lean_dec(v_hint_4811_);
lean_dec(v_mod_4809_);
v___x_4888_ = lean_box(0);
v___x_4889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4888_);
return v___x_4889_;
}
v___jp_4825_:
{
lean_object* v___x_4827_; lean_object* v_toEnvExtension_4828_; lean_object* v_env_4829_; lean_object* v_messages_4830_; lean_object* v_scopes_4831_; lean_object* v_usedQuotCtxts_4832_; lean_object* v_nextMacroScope_4833_; lean_object* v_maxRecDepth_4834_; lean_object* v_ngen_4835_; lean_object* v_auxDeclNGen_4836_; lean_object* v_infoState_4837_; lean_object* v_traceState_4838_; lean_object* v_snapshotTasks_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4851_; 
v___x_4827_ = lean_st_ref_take(v___y_4826_);
v_toEnvExtension_4828_ = lean_ctor_get(v___x_4822_, 0);
lean_inc_ref(v_toEnvExtension_4828_);
v_env_4829_ = lean_ctor_get(v___x_4827_, 0);
v_messages_4830_ = lean_ctor_get(v___x_4827_, 1);
v_scopes_4831_ = lean_ctor_get(v___x_4827_, 2);
v_usedQuotCtxts_4832_ = lean_ctor_get(v___x_4827_, 3);
v_nextMacroScope_4833_ = lean_ctor_get(v___x_4827_, 4);
v_maxRecDepth_4834_ = lean_ctor_get(v___x_4827_, 5);
v_ngen_4835_ = lean_ctor_get(v___x_4827_, 6);
v_auxDeclNGen_4836_ = lean_ctor_get(v___x_4827_, 7);
v_infoState_4837_ = lean_ctor_get(v___x_4827_, 8);
v_traceState_4838_ = lean_ctor_get(v___x_4827_, 9);
v_snapshotTasks_4839_ = lean_ctor_get(v___x_4827_, 10);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4841_ = v___x_4827_;
v_isShared_4842_ = v_isSharedCheck_4851_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_snapshotTasks_4839_);
lean_inc(v_traceState_4838_);
lean_inc(v_infoState_4837_);
lean_inc(v_auxDeclNGen_4836_);
lean_inc(v_ngen_4835_);
lean_inc(v_maxRecDepth_4834_);
lean_inc(v_nextMacroScope_4833_);
lean_inc(v_usedQuotCtxts_4832_);
lean_inc(v_scopes_4831_);
lean_inc(v_messages_4830_);
lean_inc(v_env_4829_);
lean_dec(v___x_4827_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4851_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v_asyncMode_4843_; lean_object* v___x_4844_; lean_object* v___x_4846_; 
v_asyncMode_4843_ = lean_ctor_get(v_toEnvExtension_4828_, 2);
lean_inc(v_asyncMode_4843_);
lean_dec_ref(v_toEnvExtension_4828_);
v___x_4844_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4822_, v_env_4829_, v_entry_4821_, v_asyncMode_4843_, v___x_4824_);
lean_dec(v_asyncMode_4843_);
if (v_isShared_4842_ == 0)
{
lean_ctor_set(v___x_4841_, 0, v___x_4844_);
v___x_4846_ = v___x_4841_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4844_);
lean_ctor_set(v_reuseFailAlloc_4850_, 1, v_messages_4830_);
lean_ctor_set(v_reuseFailAlloc_4850_, 2, v_scopes_4831_);
lean_ctor_set(v_reuseFailAlloc_4850_, 3, v_usedQuotCtxts_4832_);
lean_ctor_set(v_reuseFailAlloc_4850_, 4, v_nextMacroScope_4833_);
lean_ctor_set(v_reuseFailAlloc_4850_, 5, v_maxRecDepth_4834_);
lean_ctor_set(v_reuseFailAlloc_4850_, 6, v_ngen_4835_);
lean_ctor_set(v_reuseFailAlloc_4850_, 7, v_auxDeclNGen_4836_);
lean_ctor_set(v_reuseFailAlloc_4850_, 8, v_infoState_4837_);
lean_ctor_set(v_reuseFailAlloc_4850_, 9, v_traceState_4838_);
lean_ctor_set(v_reuseFailAlloc_4850_, 10, v_snapshotTasks_4839_);
v___x_4846_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4847_ = lean_st_ref_set(v___y_4826_, v___x_4846_);
v___x_4848_ = lean_box(0);
v___x_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
return v___x_4849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___boxed(lean_object* v_mod_4890_, lean_object* v_isMeta_4891_, lean_object* v_hint_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_){
_start:
{
uint8_t v_isMeta_boxed_4896_; lean_object* v_res_4897_; 
v_isMeta_boxed_4896_ = lean_unbox(v_isMeta_4891_);
v_res_4897_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7(v_mod_4890_, v_isMeta_boxed_4896_, v_hint_4892_, v___y_4893_, v___y_4894_);
lean_dec(v___y_4894_);
lean_dec_ref(v___y_4893_);
return v_res_4897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__8(lean_object* v___x_4898_, lean_object* v_declName_4899_, lean_object* v_as_4900_, size_t v_sz_4901_, size_t v_i_4902_, lean_object* v_b_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
uint8_t v___x_4907_; 
v___x_4907_ = lean_usize_dec_lt(v_i_4902_, v_sz_4901_);
if (v___x_4907_ == 0)
{
lean_object* v___x_4908_; 
lean_dec(v_declName_4899_);
v___x_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4908_, 0, v_b_4903_);
return v___x_4908_;
}
else
{
lean_object* v___x_4909_; lean_object* v_modules_4910_; lean_object* v___x_4911_; lean_object* v_a_4912_; lean_object* v___x_4913_; lean_object* v_toImport_4914_; lean_object* v_module_4915_; uint8_t v___x_4916_; lean_object* v___x_4917_; 
v___x_4909_ = l_Lean_Environment_header(v___x_4898_);
v_modules_4910_ = lean_ctor_get(v___x_4909_, 3);
lean_inc_ref(v_modules_4910_);
lean_dec_ref(v___x_4909_);
v___x_4911_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_4912_ = lean_array_uget_borrowed(v_as_4900_, v_i_4902_);
v___x_4913_ = lean_array_get(v___x_4911_, v_modules_4910_, v_a_4912_);
lean_dec_ref(v_modules_4910_);
v_toImport_4914_ = lean_ctor_get(v___x_4913_, 0);
lean_inc_ref(v_toImport_4914_);
lean_dec(v___x_4913_);
v_module_4915_ = lean_ctor_get(v_toImport_4914_, 0);
lean_inc(v_module_4915_);
lean_dec_ref(v_toImport_4914_);
v___x_4916_ = 0;
lean_inc(v_declName_4899_);
v___x_4917_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7(v_module_4915_, v___x_4916_, v_declName_4899_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v___x_4918_; size_t v___x_4919_; size_t v___x_4920_; 
lean_dec_ref(v___x_4917_);
v___x_4918_ = lean_box(0);
v___x_4919_ = ((size_t)1ULL);
v___x_4920_ = lean_usize_add(v_i_4902_, v___x_4919_);
v_i_4902_ = v___x_4920_;
v_b_4903_ = v___x_4918_;
goto _start;
}
else
{
lean_dec(v_declName_4899_);
return v___x_4917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__8___boxed(lean_object* v___x_4922_, lean_object* v_declName_4923_, lean_object* v_as_4924_, lean_object* v_sz_4925_, lean_object* v_i_4926_, lean_object* v_b_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_){
_start:
{
size_t v_sz_boxed_4931_; size_t v_i_boxed_4932_; lean_object* v_res_4933_; 
v_sz_boxed_4931_ = lean_unbox_usize(v_sz_4925_);
lean_dec(v_sz_4925_);
v_i_boxed_4932_ = lean_unbox_usize(v_i_4926_);
lean_dec(v_i_4926_);
v_res_4933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__8(v___x_4922_, v_declName_4923_, v_as_4924_, v_sz_boxed_4931_, v_i_boxed_4932_, v_b_4927_, v___y_4928_, v___y_4929_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
lean_dec_ref(v_as_4924_);
lean_dec_ref(v___x_4922_);
return v_res_4933_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__2(void){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4936_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__1));
v___x_4937_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__0));
v___x_4938_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_4937_, v___x_4936_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4(lean_object* v_declName_4941_, uint8_t v_isMeta_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v___x_4946_; lean_object* v_env_4950_; lean_object* v___y_4952_; lean_object* v___x_4965_; 
v___x_4946_ = lean_st_ref_get(v___y_4944_);
v_env_4950_ = lean_ctor_get(v___x_4946_, 0);
lean_inc_ref(v_env_4950_);
lean_dec(v___x_4946_);
v___x_4965_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4950_, v_declName_4941_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_dec_ref(v_env_4950_);
lean_dec(v_declName_4941_);
goto v___jp_4947_;
}
else
{
lean_object* v_val_4966_; lean_object* v___x_4967_; lean_object* v_modules_4968_; lean_object* v___x_4969_; uint8_t v___x_4970_; 
v_val_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc(v_val_4966_);
lean_dec_ref(v___x_4965_);
v___x_4967_ = l_Lean_Environment_header(v_env_4950_);
v_modules_4968_ = lean_ctor_get(v___x_4967_, 3);
lean_inc_ref(v_modules_4968_);
lean_dec_ref(v___x_4967_);
v___x_4969_ = lean_array_get_size(v_modules_4968_);
v___x_4970_ = lean_nat_dec_lt(v_val_4966_, v___x_4969_);
if (v___x_4970_ == 0)
{
lean_dec_ref(v_modules_4968_);
lean_dec(v_val_4966_);
lean_dec_ref(v_env_4950_);
lean_dec(v_declName_4941_);
goto v___jp_4947_;
}
else
{
lean_object* v___x_4971_; lean_object* v_env_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; uint8_t v___y_4976_; 
v___x_4971_ = lean_st_ref_get(v___y_4944_);
v_env_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc_ref(v_env_4972_);
lean_dec(v___x_4971_);
v___x_4973_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__2);
v___x_4974_ = lean_array_fget(v_modules_4968_, v_val_4966_);
lean_dec(v_val_4966_);
lean_dec_ref(v_modules_4968_);
if (v_isMeta_4942_ == 0)
{
lean_dec_ref(v_env_4972_);
v___y_4976_ = v_isMeta_4942_;
goto v___jp_4975_;
}
else
{
uint8_t v___x_4987_; 
lean_inc(v_declName_4941_);
v___x_4987_ = l_Lean_isMarkedMeta(v_env_4972_, v_declName_4941_);
if (v___x_4987_ == 0)
{
v___y_4976_ = v_isMeta_4942_;
goto v___jp_4975_;
}
else
{
uint8_t v___x_4988_; 
v___x_4988_ = 0;
v___y_4976_ = v___x_4988_;
goto v___jp_4975_;
}
}
v___jp_4975_:
{
lean_object* v_toImport_4977_; lean_object* v_module_4978_; lean_object* v___x_4979_; 
v_toImport_4977_ = lean_ctor_get(v___x_4974_, 0);
lean_inc_ref(v_toImport_4977_);
lean_dec(v___x_4974_);
v_module_4978_ = lean_ctor_get(v_toImport_4977_, 0);
lean_inc(v_module_4978_);
lean_dec_ref(v_toImport_4977_);
lean_inc(v_declName_4941_);
v___x_4979_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7(v_module_4978_, v___y_4976_, v_declName_4941_, v___y_4943_, v___y_4944_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
lean_dec_ref(v___x_4979_);
v___x_4980_ = l_Lean_indirectModUseExt;
v___x_4981_ = lean_box(1);
v___x_4982_ = lean_box(0);
lean_inc_ref(v_env_4950_);
v___x_4983_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4973_, v___x_4980_, v_env_4950_, v___x_4981_, v___x_4982_);
v___x_4984_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg(v___x_4983_, v_declName_4941_);
lean_dec(v___x_4983_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v___x_4985_; 
v___x_4985_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__3));
v___y_4952_ = v___x_4985_;
goto v___jp_4951_;
}
else
{
lean_object* v_val_4986_; 
v_val_4986_ = lean_ctor_get(v___x_4984_, 0);
lean_inc(v_val_4986_);
lean_dec_ref(v___x_4984_);
v___y_4952_ = v_val_4986_;
goto v___jp_4951_;
}
}
else
{
lean_dec_ref(v_env_4950_);
lean_dec(v_declName_4941_);
return v___x_4979_;
}
}
}
}
v___jp_4947_:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; 
v___x_4948_ = lean_box(0);
v___x_4949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4948_);
return v___x_4949_;
}
v___jp_4951_:
{
lean_object* v___x_4953_; size_t v_sz_4954_; size_t v___x_4955_; lean_object* v___x_4956_; 
v___x_4953_ = lean_box(0);
v_sz_4954_ = lean_array_size(v___y_4952_);
v___x_4955_ = ((size_t)0ULL);
v___x_4956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__8(v_env_4950_, v_declName_4941_, v___y_4952_, v_sz_4954_, v___x_4955_, v___x_4953_, v___y_4943_, v___y_4944_);
lean_dec_ref(v___y_4952_);
lean_dec_ref(v_env_4950_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4963_; 
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4963_ == 0)
{
lean_object* v_unused_4964_; 
v_unused_4964_ = lean_ctor_get(v___x_4956_, 0);
lean_dec(v_unused_4964_);
v___x_4958_ = v___x_4956_;
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
else
{
lean_dec(v___x_4956_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4961_; 
if (v_isShared_4959_ == 0)
{
lean_ctor_set(v___x_4958_, 0, v___x_4953_);
v___x_4961_ = v___x_4958_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v___x_4953_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
else
{
return v___x_4956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___boxed(lean_object* v_declName_4989_, lean_object* v_isMeta_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_){
_start:
{
uint8_t v_isMeta_boxed_4994_; lean_object* v_res_4995_; 
v_isMeta_boxed_4994_ = lean_unbox(v_isMeta_4990_);
v_res_4995_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4(v_declName_4989_, v_isMeta_boxed_4994_, v___y_4991_, v___y_4992_);
lean_dec(v___y_4992_);
lean_dec_ref(v___y_4991_);
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg(lean_object* v_as_x27_4996_, lean_object* v_b_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
if (lean_obj_tag(v_as_x27_4996_) == 0)
{
lean_object* v___x_5001_; 
v___x_5001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5001_, 0, v_b_4997_);
return v___x_5001_;
}
else
{
lean_object* v_head_5002_; lean_object* v_tail_5003_; uint8_t v___x_5004_; lean_object* v___x_5005_; 
v_head_5002_ = lean_ctor_get(v_as_x27_4996_, 0);
lean_inc(v_head_5002_);
v_tail_5003_ = lean_ctor_get(v_as_x27_4996_, 1);
lean_inc(v_tail_5003_);
lean_dec_ref(v_as_x27_4996_);
v___x_5004_ = 1;
v___x_5005_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4(v_head_5002_, v___x_5004_, v___y_4998_, v___y_4999_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v___x_5006_; 
lean_dec_ref(v___x_5005_);
v___x_5006_ = lean_box(0);
v_as_x27_4996_ = v_tail_5003_;
v_b_4997_ = v___x_5006_;
goto _start;
}
else
{
lean_dec(v_tail_5003_);
return v___x_5005_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg___boxed(lean_object* v_as_x27_5008_, lean_object* v_b_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg(v_as_x27_5008_, v_b_5009_, v___y_5010_, v___y_5011_);
lean_dec(v___y_5011_);
lean_dec_ref(v___y_5010_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6(lean_object* v_as_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_){
_start:
{
if (lean_obj_tag(v_as_5014_) == 0)
{
lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5018_ = lean_box(0);
v___x_5019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
return v___x_5019_;
}
else
{
lean_object* v_head_5020_; lean_object* v_tail_5021_; lean_object* v_fst_5022_; lean_object* v_snd_5023_; lean_object* v___x_5024_; lean_object* v_a_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5037_; 
v_head_5020_ = lean_ctor_get(v_as_5014_, 0);
lean_inc(v_head_5020_);
v_tail_5021_ = lean_ctor_get(v_as_5014_, 1);
lean_inc(v_tail_5021_);
lean_dec_ref(v_as_5014_);
v_fst_5022_ = lean_ctor_get(v_head_5020_, 0);
lean_inc(v_fst_5022_);
v_snd_5023_ = lean_ctor_get(v_head_5020_, 1);
lean_inc(v_snd_5023_);
lean_dec(v_head_5020_);
lean_inc(v_fst_5022_);
v___x_5024_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg(v_fst_5022_, v___y_5016_);
v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5027_ = v___x_5024_;
v_isShared_5028_ = v_isSharedCheck_5037_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_a_5025_);
lean_dec(v___x_5024_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5037_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
uint8_t v___x_5029_; 
v___x_5029_ = lean_unbox(v_a_5025_);
lean_dec(v_a_5025_);
if (v___x_5029_ == 0)
{
lean_del_object(v___x_5027_);
lean_dec(v_snd_5023_);
lean_dec(v_fst_5022_);
v_as_5014_ = v_tail_5021_;
goto _start;
}
else
{
lean_object* v___x_5032_; 
if (v_isShared_5028_ == 0)
{
lean_ctor_set_tag(v___x_5027_, 3);
lean_ctor_set(v___x_5027_, 0, v_snd_5023_);
v___x_5032_ = v___x_5027_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_snd_5023_);
v___x_5032_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5033_ = l_Lean_MessageData_ofFormat(v___x_5032_);
v___x_5034_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2(v_fst_5022_, v___x_5033_, v___y_5015_, v___y_5016_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_dec_ref(v___x_5034_);
v_as_5014_ = v_tail_5021_;
goto _start;
}
else
{
lean_dec(v_tail_5021_);
return v___x_5034_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6___boxed(lean_object* v_as_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6(v_as_5038_, v___y_5039_, v___y_5040_);
lean_dec(v___y_5040_);
lean_dec_ref(v___y_5039_);
return v_res_5042_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5048_ = l_Lean_maxRecDepthErrorMessage;
v___x_5049_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5049_, 0, v___x_5048_);
return v___x_5049_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5050_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__3);
v___x_5051_ = l_Lean_MessageData_ofFormat(v___x_5050_);
return v___x_5051_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5052_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__4);
v___x_5053_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__2));
v___x_5054_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5053_);
lean_ctor_set(v___x_5054_, 1, v___x_5052_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg(lean_object* v_ref_5055_){
_start:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5057_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__5);
v___x_5058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5058_, 0, v_ref_5055_);
lean_ctor_set(v___x_5058_, 1, v___x_5057_);
v___x_5059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5058_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___boxed(lean_object* v_ref_5060_, lean_object* v___y_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg(v_ref_5060_);
return v_res_5062_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0(void){
_start:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = lean_box(1);
v___x_5064_ = l_Lean_MessageData_ofFormat(v___x_5063_);
return v___x_5064_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3(void){
_start:
{
lean_object* v___x_5068_; lean_object* v___x_5069_; 
v___x_5068_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__2));
v___x_5069_ = l_Lean_MessageData_ofFormat(v___x_5068_);
return v___x_5069_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21(lean_object* v_x_5070_, lean_object* v_x_5071_){
_start:
{
if (lean_obj_tag(v_x_5071_) == 0)
{
return v_x_5070_;
}
else
{
lean_object* v_head_5072_; lean_object* v_tail_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5095_; 
v_head_5072_ = lean_ctor_get(v_x_5071_, 0);
v_tail_5073_ = lean_ctor_get(v_x_5071_, 1);
v_isSharedCheck_5095_ = !lean_is_exclusive(v_x_5071_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5075_ = v_x_5071_;
v_isShared_5076_ = v_isSharedCheck_5095_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_tail_5073_);
lean_inc(v_head_5072_);
lean_dec(v_x_5071_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5095_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v_before_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5093_; 
v_before_5077_ = lean_ctor_get(v_head_5072_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v_head_5072_);
if (v_isSharedCheck_5093_ == 0)
{
lean_object* v_unused_5094_; 
v_unused_5094_ = lean_ctor_get(v_head_5072_, 1);
lean_dec(v_unused_5094_);
v___x_5079_ = v_head_5072_;
v_isShared_5080_ = v_isSharedCheck_5093_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_before_5077_);
lean_dec(v_head_5072_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5093_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5081_; lean_object* v___x_5083_; 
v___x_5081_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0);
if (v_isShared_5080_ == 0)
{
lean_ctor_set_tag(v___x_5079_, 7);
lean_ctor_set(v___x_5079_, 1, v___x_5081_);
lean_ctor_set(v___x_5079_, 0, v_x_5070_);
v___x_5083_ = v___x_5079_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_x_5070_);
lean_ctor_set(v_reuseFailAlloc_5092_, 1, v___x_5081_);
v___x_5083_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
lean_object* v___x_5084_; lean_object* v___x_5086_; 
v___x_5084_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3);
if (v_isShared_5076_ == 0)
{
lean_ctor_set_tag(v___x_5075_, 7);
lean_ctor_set(v___x_5075_, 1, v___x_5084_);
lean_ctor_set(v___x_5075_, 0, v___x_5083_);
v___x_5086_ = v___x_5075_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v___x_5083_);
lean_ctor_set(v_reuseFailAlloc_5091_, 1, v___x_5084_);
v___x_5086_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5087_ = l_Lean_MessageData_ofSyntax(v_before_5077_);
v___x_5088_ = l_Lean_indentD(v___x_5087_);
v___x_5089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5089_, 0, v___x_5086_);
lean_ctor_set(v___x_5089_, 1, v___x_5088_);
v_x_5070_ = v___x_5089_;
v_x_5071_ = v_tail_5073_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2(void){
_start:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5099_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__1));
v___x_5100_ = l_Lean_MessageData_ofFormat(v___x_5099_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg(lean_object* v_msgData_5101_, lean_object* v_macroStack_5102_, lean_object* v___y_5103_){
_start:
{
lean_object* v___x_5105_; lean_object* v_scopes_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v_opts_5109_; lean_object* v___x_5110_; uint8_t v___x_5111_; 
v___x_5105_ = lean_st_ref_get(v___y_5103_);
v_scopes_5106_ = lean_ctor_get(v___x_5105_, 2);
lean_inc(v_scopes_5106_);
lean_dec(v___x_5105_);
v___x_5107_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_5108_ = l_List_head_x21___redArg(v___x_5107_, v_scopes_5106_);
lean_dec(v_scopes_5106_);
v_opts_5109_ = lean_ctor_get(v___x_5108_, 1);
lean_inc_ref(v_opts_5109_);
lean_dec(v___x_5108_);
v___x_5110_ = l_Lean_Elab_pp_macroStack;
v___x_5111_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21(v_opts_5109_, v___x_5110_);
lean_dec_ref(v_opts_5109_);
if (v___x_5111_ == 0)
{
lean_object* v___x_5112_; 
lean_dec(v_macroStack_5102_);
v___x_5112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5112_, 0, v_msgData_5101_);
return v___x_5112_;
}
else
{
if (lean_obj_tag(v_macroStack_5102_) == 0)
{
lean_object* v___x_5113_; 
v___x_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5113_, 0, v_msgData_5101_);
return v___x_5113_;
}
else
{
lean_object* v_head_5114_; lean_object* v_after_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5130_; 
v_head_5114_ = lean_ctor_get(v_macroStack_5102_, 0);
lean_inc(v_head_5114_);
v_after_5115_ = lean_ctor_get(v_head_5114_, 1);
v_isSharedCheck_5130_ = !lean_is_exclusive(v_head_5114_);
if (v_isSharedCheck_5130_ == 0)
{
lean_object* v_unused_5131_; 
v_unused_5131_ = lean_ctor_get(v_head_5114_, 0);
lean_dec(v_unused_5131_);
v___x_5117_ = v_head_5114_;
v_isShared_5118_ = v_isSharedCheck_5130_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_after_5115_);
lean_dec(v_head_5114_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5130_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5119_; lean_object* v___x_5121_; 
v___x_5119_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0);
if (v_isShared_5118_ == 0)
{
lean_ctor_set_tag(v___x_5117_, 7);
lean_ctor_set(v___x_5117_, 1, v___x_5119_);
lean_ctor_set(v___x_5117_, 0, v_msgData_5101_);
v___x_5121_ = v___x_5117_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_msgData_5101_);
lean_ctor_set(v_reuseFailAlloc_5129_, 1, v___x_5119_);
v___x_5121_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v_msgData_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v___x_5122_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2);
v___x_5123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5123_, 0, v___x_5121_);
lean_ctor_set(v___x_5123_, 1, v___x_5122_);
v___x_5124_ = l_Lean_MessageData_ofSyntax(v_after_5115_);
v___x_5125_ = l_Lean_indentD(v___x_5124_);
v_msgData_5126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5126_, 0, v___x_5123_);
lean_ctor_set(v_msgData_5126_, 1, v___x_5125_);
v___x_5127_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21(v_msgData_5126_, v_macroStack_5102_);
v___x_5128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5128_, 0, v___x_5127_);
return v___x_5128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___boxed(lean_object* v_msgData_5132_, lean_object* v_macroStack_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_){
_start:
{
lean_object* v_res_5136_; 
v_res_5136_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg(v_msgData_5132_, v_macroStack_5133_, v___y_5134_);
lean_dec(v___y_5134_);
return v_res_5136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg(lean_object* v_msg_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_){
_start:
{
lean_object* v___x_5141_; 
v___x_5141_ = l_Lean_Elab_Command_getRef___redArg(v___y_5138_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_object* v_a_5142_; lean_object* v_macroStack_5143_; lean_object* v___x_5144_; lean_object* v_a_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v_a_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5156_; 
v_a_5142_ = lean_ctor_get(v___x_5141_, 0);
lean_inc(v_a_5142_);
lean_dec_ref(v___x_5141_);
v_macroStack_5143_ = lean_ctor_get(v___y_5138_, 4);
lean_inc(v_macroStack_5143_);
lean_dec_ref(v___y_5138_);
v___x_5144_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(v_msg_5137_, v___y_5139_);
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
lean_dec_ref(v___x_5144_);
lean_inc(v_macroStack_5143_);
v___x_5146_ = l_Lean_Elab_getBetterRef(v_a_5142_, v_macroStack_5143_);
lean_dec(v_a_5142_);
v___x_5147_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg(v_a_5145_, v_macroStack_5143_, v___y_5139_);
v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5150_ = v___x_5147_;
v_isShared_5151_ = v_isSharedCheck_5156_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_a_5148_);
lean_dec(v___x_5147_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5156_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5152_; lean_object* v___x_5154_; 
v___x_5152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5152_, 0, v___x_5146_);
lean_ctor_set(v___x_5152_, 1, v_a_5148_);
if (v_isShared_5151_ == 0)
{
lean_ctor_set_tag(v___x_5150_, 1);
lean_ctor_set(v___x_5150_, 0, v___x_5152_);
v___x_5154_ = v___x_5150_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v___x_5152_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_dec_ref(v___y_5138_);
lean_dec_ref(v_msg_5137_);
v_a_5157_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5141_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5141_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg___boxed(lean_object* v_msg_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_){
_start:
{
lean_object* v_res_5169_; 
v_res_5169_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg(v_msg_5165_, v___y_5166_, v___y_5167_);
lean_dec(v___y_5167_);
return v_res_5169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg(lean_object* v_ref_5170_, lean_object* v_msg_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_){
_start:
{
lean_object* v___x_5175_; 
v___x_5175_ = l_Lean_Elab_Command_getRef___redArg(v___y_5172_);
if (lean_obj_tag(v___x_5175_) == 0)
{
lean_object* v_a_5176_; lean_object* v_fileName_5177_; lean_object* v_fileMap_5178_; lean_object* v_currRecDepth_5179_; lean_object* v_cmdPos_5180_; lean_object* v_macroStack_5181_; lean_object* v_quotContext_x3f_5182_; lean_object* v_currMacroScope_5183_; lean_object* v_snap_x3f_5184_; lean_object* v_cancelTk_x3f_5185_; uint8_t v_suppressElabErrors_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5195_; 
v_a_5176_ = lean_ctor_get(v___x_5175_, 0);
lean_inc(v_a_5176_);
lean_dec_ref(v___x_5175_);
v_fileName_5177_ = lean_ctor_get(v___y_5172_, 0);
v_fileMap_5178_ = lean_ctor_get(v___y_5172_, 1);
v_currRecDepth_5179_ = lean_ctor_get(v___y_5172_, 2);
v_cmdPos_5180_ = lean_ctor_get(v___y_5172_, 3);
v_macroStack_5181_ = lean_ctor_get(v___y_5172_, 4);
v_quotContext_x3f_5182_ = lean_ctor_get(v___y_5172_, 5);
v_currMacroScope_5183_ = lean_ctor_get(v___y_5172_, 6);
v_snap_x3f_5184_ = lean_ctor_get(v___y_5172_, 8);
v_cancelTk_x3f_5185_ = lean_ctor_get(v___y_5172_, 9);
v_suppressElabErrors_5186_ = lean_ctor_get_uint8(v___y_5172_, sizeof(void*)*10);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___y_5172_);
if (v_isSharedCheck_5195_ == 0)
{
lean_object* v_unused_5196_; 
v_unused_5196_ = lean_ctor_get(v___y_5172_, 7);
lean_dec(v_unused_5196_);
v___x_5188_ = v___y_5172_;
v_isShared_5189_ = v_isSharedCheck_5195_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_cancelTk_x3f_5185_);
lean_inc(v_snap_x3f_5184_);
lean_inc(v_currMacroScope_5183_);
lean_inc(v_quotContext_x3f_5182_);
lean_inc(v_macroStack_5181_);
lean_inc(v_cmdPos_5180_);
lean_inc(v_currRecDepth_5179_);
lean_inc(v_fileMap_5178_);
lean_inc(v_fileName_5177_);
lean_dec(v___y_5172_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5195_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v_ref_5190_; lean_object* v___x_5192_; 
v_ref_5190_ = l_Lean_replaceRef(v_ref_5170_, v_a_5176_);
lean_dec(v_a_5176_);
if (v_isShared_5189_ == 0)
{
lean_ctor_set(v___x_5188_, 7, v_ref_5190_);
v___x_5192_ = v___x_5188_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_fileName_5177_);
lean_ctor_set(v_reuseFailAlloc_5194_, 1, v_fileMap_5178_);
lean_ctor_set(v_reuseFailAlloc_5194_, 2, v_currRecDepth_5179_);
lean_ctor_set(v_reuseFailAlloc_5194_, 3, v_cmdPos_5180_);
lean_ctor_set(v_reuseFailAlloc_5194_, 4, v_macroStack_5181_);
lean_ctor_set(v_reuseFailAlloc_5194_, 5, v_quotContext_x3f_5182_);
lean_ctor_set(v_reuseFailAlloc_5194_, 6, v_currMacroScope_5183_);
lean_ctor_set(v_reuseFailAlloc_5194_, 7, v_ref_5190_);
lean_ctor_set(v_reuseFailAlloc_5194_, 8, v_snap_x3f_5184_);
lean_ctor_set(v_reuseFailAlloc_5194_, 9, v_cancelTk_x3f_5185_);
lean_ctor_set_uint8(v_reuseFailAlloc_5194_, sizeof(void*)*10, v_suppressElabErrors_5186_);
v___x_5192_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
lean_object* v___x_5193_; 
v___x_5193_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg(v_msg_5171_, v___x_5192_, v___y_5173_);
return v___x_5193_;
}
}
}
else
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5204_; 
lean_dec_ref(v___y_5172_);
lean_dec_ref(v_msg_5171_);
v_a_5197_ = lean_ctor_get(v___x_5175_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5175_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5199_ = v___x_5175_;
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_5175_);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg___boxed(lean_object* v_ref_5205_, lean_object* v_msg_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg(v_ref_5205_, v_msg_5206_, v___y_5207_, v___y_5208_);
lean_dec(v___y_5208_);
lean_dec(v_ref_5205_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__4(lean_object* v_env_5211_, lean_object* v_opts_5212_, lean_object* v_currNamespace_5213_, lean_object* v_openDecls_5214_, lean_object* v_n_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_){
_start:
{
lean_object* v___x_5218_; lean_object* v___x_5219_; 
v___x_5218_ = l_Lean_ResolveName_resolveGlobalName(v_env_5211_, v_opts_5212_, v_currNamespace_5213_, v_openDecls_5214_, v_n_5215_);
v___x_5219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5218_);
lean_ctor_set(v___x_5219_, 1, v___y_5217_);
return v___x_5219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__4___boxed(lean_object* v_env_5220_, lean_object* v_opts_5221_, lean_object* v_currNamespace_5222_, lean_object* v_openDecls_5223_, lean_object* v_n_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_){
_start:
{
lean_object* v_res_5227_; 
v_res_5227_ = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__4(v_env_5220_, v_opts_5221_, v_currNamespace_5222_, v_openDecls_5223_, v_n_5224_, v___y_5225_, v___y_5226_);
lean_dec_ref(v___y_5225_);
lean_dec_ref(v_opts_5221_);
return v_res_5227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__2(lean_object* v_currNamespace_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_){
_start:
{
lean_object* v___x_5231_; 
v___x_5231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5231_, 0, v_currNamespace_5228_);
lean_ctor_set(v___x_5231_, 1, v___y_5230_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_){
_start:
{
lean_object* v_res_5235_; 
v_res_5235_ = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__2(v_currNamespace_5232_, v___y_5233_, v___y_5234_);
lean_dec_ref(v___y_5233_);
return v_res_5235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg(lean_object* v_x_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_){
_start:
{
lean_object* v___x_5241_; lean_object* v_env_5242_; lean_object* v___x_5243_; lean_object* v_scopes_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v_opts_5247_; lean_object* v___x_5248_; 
v___x_5241_ = lean_st_ref_get(v___y_5239_);
v_env_5242_ = lean_ctor_get(v___x_5241_, 0);
lean_inc_ref(v_env_5242_);
lean_dec(v___x_5241_);
v___x_5243_ = lean_st_ref_get(v___y_5239_);
v_scopes_5244_ = lean_ctor_get(v___x_5243_, 2);
lean_inc(v_scopes_5244_);
lean_dec(v___x_5243_);
v___x_5245_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_5246_ = l_List_head_x21___redArg(v___x_5245_, v_scopes_5244_);
lean_dec(v_scopes_5244_);
v_opts_5247_ = lean_ctor_get(v___x_5246_, 1);
lean_inc_ref(v_opts_5247_);
lean_dec(v___x_5246_);
v___x_5248_ = l_Lean_Elab_Command_getScope___redArg(v___y_5239_);
if (lean_obj_tag(v___x_5248_) == 0)
{
lean_object* v_a_5249_; lean_object* v_currNamespace_5250_; lean_object* v___x_5251_; 
v_a_5249_ = lean_ctor_get(v___x_5248_, 0);
lean_inc(v_a_5249_);
lean_dec_ref(v___x_5248_);
v_currNamespace_5250_ = lean_ctor_get(v_a_5249_, 2);
lean_inc(v_currNamespace_5250_);
lean_dec(v_a_5249_);
v___x_5251_ = l_Lean_Elab_Command_getScope___redArg(v___y_5239_);
if (lean_obj_tag(v___x_5251_) == 0)
{
lean_object* v_a_5252_; lean_object* v_openDecls_5253_; lean_object* v___x_5254_; 
v_a_5252_ = lean_ctor_get(v___x_5251_, 0);
lean_inc(v_a_5252_);
lean_dec_ref(v___x_5251_);
v_openDecls_5253_ = lean_ctor_get(v_a_5252_, 3);
lean_inc(v_openDecls_5253_);
lean_dec(v_a_5252_);
v___x_5254_ = l_Lean_Elab_Command_getRef___redArg(v___y_5238_);
if (lean_obj_tag(v___x_5254_) == 0)
{
lean_object* v_a_5255_; lean_object* v___x_5256_; 
v_a_5255_ = lean_ctor_get(v___x_5254_, 0);
lean_inc(v_a_5255_);
lean_dec_ref(v___x_5254_);
v___x_5256_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_5238_);
if (lean_obj_tag(v___x_5256_) == 0)
{
lean_object* v_a_5257_; lean_object* v_currRecDepth_5258_; lean_object* v_quotContext_x3f_5259_; lean_object* v___f_5260_; lean_object* v___f_5261_; lean_object* v___f_5262_; lean_object* v___f_5263_; lean_object* v___f_5264_; lean_object* v_methods_5265_; lean_object* v_a_5267_; 
v_a_5257_ = lean_ctor_get(v___x_5256_, 0);
lean_inc(v_a_5257_);
lean_dec_ref(v___x_5256_);
v_currRecDepth_5258_ = lean_ctor_get(v___y_5238_, 2);
v_quotContext_x3f_5259_ = lean_ctor_get(v___y_5238_, 5);
lean_inc_ref(v_env_5242_);
v___f_5260_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_5260_, 0, v_env_5242_);
lean_inc_ref(v_env_5242_);
v___f_5261_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_5261_, 0, v_env_5242_);
lean_inc(v_currNamespace_5250_);
v___f_5262_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5262_, 0, v_currNamespace_5250_);
lean_inc(v_openDecls_5253_);
lean_inc(v_currNamespace_5250_);
lean_inc_ref(v_env_5242_);
v___f_5263_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_5263_, 0, v_env_5242_);
lean_closure_set(v___f_5263_, 1, v_currNamespace_5250_);
lean_closure_set(v___f_5263_, 2, v_openDecls_5253_);
v___f_5264_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_5264_, 0, v_env_5242_);
lean_closure_set(v___f_5264_, 1, v_opts_5247_);
lean_closure_set(v___f_5264_, 2, v_currNamespace_5250_);
lean_closure_set(v___f_5264_, 3, v_openDecls_5253_);
v_methods_5265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_5265_, 0, v___f_5261_);
lean_ctor_set(v_methods_5265_, 1, v___f_5262_);
lean_ctor_set(v_methods_5265_, 2, v___f_5260_);
lean_ctor_set(v_methods_5265_, 3, v___f_5263_);
lean_ctor_set(v_methods_5265_, 4, v___f_5264_);
if (lean_obj_tag(v_quotContext_x3f_5259_) == 0)
{
lean_object* v___x_5339_; lean_object* v_a_5340_; 
v___x_5339_ = l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg(v___y_5239_);
v_a_5340_ = lean_ctor_get(v___x_5339_, 0);
lean_inc(v_a_5340_);
lean_dec_ref(v___x_5339_);
v_a_5267_ = v_a_5340_;
goto v___jp_5266_;
}
else
{
lean_object* v_val_5341_; 
v_val_5341_ = lean_ctor_get(v_quotContext_x3f_5259_, 0);
lean_inc(v_val_5341_);
v_a_5267_ = v_val_5341_;
goto v___jp_5266_;
}
v___jp_5266_:
{
lean_object* v___x_5268_; lean_object* v_maxRecDepth_5269_; lean_object* v___x_5270_; lean_object* v_nextMacroScope_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; 
v___x_5268_ = lean_st_ref_get(v___y_5239_);
v_maxRecDepth_5269_ = lean_ctor_get(v___x_5268_, 5);
lean_inc(v_maxRecDepth_5269_);
lean_dec(v___x_5268_);
v___x_5270_ = lean_st_ref_get(v___y_5239_);
v_nextMacroScope_5271_ = lean_ctor_get(v___x_5270_, 4);
lean_inc(v_nextMacroScope_5271_);
lean_dec(v___x_5270_);
lean_inc(v_currRecDepth_5258_);
v___x_5272_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5272_, 0, v_methods_5265_);
lean_ctor_set(v___x_5272_, 1, v_a_5267_);
lean_ctor_set(v___x_5272_, 2, v_a_5257_);
lean_ctor_set(v___x_5272_, 3, v_currRecDepth_5258_);
lean_ctor_set(v___x_5272_, 4, v_maxRecDepth_5269_);
lean_ctor_set(v___x_5272_, 5, v_a_5255_);
v___x_5273_ = lean_box(0);
v___x_5274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5274_, 0, v_nextMacroScope_5271_);
lean_ctor_set(v___x_5274_, 1, v___x_5273_);
lean_ctor_set(v___x_5274_, 2, v___x_5273_);
v___x_5275_ = lean_apply_2(v_x_5237_, v___x_5272_, v___x_5274_);
if (lean_obj_tag(v___x_5275_) == 0)
{
lean_object* v_a_5276_; lean_object* v_a_5277_; lean_object* v_macroScope_5278_; lean_object* v_traceMsgs_5279_; lean_object* v_expandedMacroDecls_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; 
v_a_5276_ = lean_ctor_get(v___x_5275_, 1);
lean_inc(v_a_5276_);
v_a_5277_ = lean_ctor_get(v___x_5275_, 0);
lean_inc(v_a_5277_);
lean_dec_ref(v___x_5275_);
v_macroScope_5278_ = lean_ctor_get(v_a_5276_, 0);
lean_inc(v_macroScope_5278_);
v_traceMsgs_5279_ = lean_ctor_get(v_a_5276_, 1);
lean_inc(v_traceMsgs_5279_);
v_expandedMacroDecls_5280_ = lean_ctor_get(v_a_5276_, 2);
lean_inc(v_expandedMacroDecls_5280_);
lean_dec(v_a_5276_);
v___x_5281_ = lean_box(0);
v___x_5282_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg(v_expandedMacroDecls_5280_, v___x_5281_, v___y_5238_, v___y_5239_);
if (lean_obj_tag(v___x_5282_) == 0)
{
lean_object* v___x_5283_; lean_object* v_env_5284_; lean_object* v_messages_5285_; lean_object* v_scopes_5286_; lean_object* v_usedQuotCtxts_5287_; lean_object* v_maxRecDepth_5288_; lean_object* v_ngen_5289_; lean_object* v_auxDeclNGen_5290_; lean_object* v_infoState_5291_; lean_object* v_traceState_5292_; lean_object* v_snapshotTasks_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5319_; 
lean_dec_ref(v___x_5282_);
v___x_5283_ = lean_st_ref_take(v___y_5239_);
v_env_5284_ = lean_ctor_get(v___x_5283_, 0);
v_messages_5285_ = lean_ctor_get(v___x_5283_, 1);
v_scopes_5286_ = lean_ctor_get(v___x_5283_, 2);
v_usedQuotCtxts_5287_ = lean_ctor_get(v___x_5283_, 3);
v_maxRecDepth_5288_ = lean_ctor_get(v___x_5283_, 5);
v_ngen_5289_ = lean_ctor_get(v___x_5283_, 6);
v_auxDeclNGen_5290_ = lean_ctor_get(v___x_5283_, 7);
v_infoState_5291_ = lean_ctor_get(v___x_5283_, 8);
v_traceState_5292_ = lean_ctor_get(v___x_5283_, 9);
v_snapshotTasks_5293_ = lean_ctor_get(v___x_5283_, 10);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5319_ == 0)
{
lean_object* v_unused_5320_; 
v_unused_5320_ = lean_ctor_get(v___x_5283_, 4);
lean_dec(v_unused_5320_);
v___x_5295_ = v___x_5283_;
v_isShared_5296_ = v_isSharedCheck_5319_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_snapshotTasks_5293_);
lean_inc(v_traceState_5292_);
lean_inc(v_infoState_5291_);
lean_inc(v_auxDeclNGen_5290_);
lean_inc(v_ngen_5289_);
lean_inc(v_maxRecDepth_5288_);
lean_inc(v_usedQuotCtxts_5287_);
lean_inc(v_scopes_5286_);
lean_inc(v_messages_5285_);
lean_inc(v_env_5284_);
lean_dec(v___x_5283_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5319_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5298_; 
if (v_isShared_5296_ == 0)
{
lean_ctor_set(v___x_5295_, 4, v_macroScope_5278_);
v___x_5298_ = v___x_5295_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_env_5284_);
lean_ctor_set(v_reuseFailAlloc_5318_, 1, v_messages_5285_);
lean_ctor_set(v_reuseFailAlloc_5318_, 2, v_scopes_5286_);
lean_ctor_set(v_reuseFailAlloc_5318_, 3, v_usedQuotCtxts_5287_);
lean_ctor_set(v_reuseFailAlloc_5318_, 4, v_macroScope_5278_);
lean_ctor_set(v_reuseFailAlloc_5318_, 5, v_maxRecDepth_5288_);
lean_ctor_set(v_reuseFailAlloc_5318_, 6, v_ngen_5289_);
lean_ctor_set(v_reuseFailAlloc_5318_, 7, v_auxDeclNGen_5290_);
lean_ctor_set(v_reuseFailAlloc_5318_, 8, v_infoState_5291_);
lean_ctor_set(v_reuseFailAlloc_5318_, 9, v_traceState_5292_);
lean_ctor_set(v_reuseFailAlloc_5318_, 10, v_snapshotTasks_5293_);
v___x_5298_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; 
v___x_5299_ = lean_st_ref_set(v___y_5239_, v___x_5298_);
v___x_5300_ = l_List_reverse___redArg(v_traceMsgs_5279_);
v___x_5301_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6(v___x_5300_, v___y_5238_, v___y_5239_);
lean_dec_ref(v___y_5238_);
if (lean_obj_tag(v___x_5301_) == 0)
{
lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5308_; 
v_isSharedCheck_5308_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5308_ == 0)
{
lean_object* v_unused_5309_; 
v_unused_5309_ = lean_ctor_get(v___x_5301_, 0);
lean_dec(v_unused_5309_);
v___x_5303_ = v___x_5301_;
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
else
{
lean_dec(v___x_5301_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___x_5306_; 
if (v_isShared_5304_ == 0)
{
lean_ctor_set(v___x_5303_, 0, v_a_5277_);
v___x_5306_ = v___x_5303_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_a_5277_);
v___x_5306_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
return v___x_5306_;
}
}
}
else
{
lean_object* v_a_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5317_; 
lean_dec(v_a_5277_);
v_a_5310_ = lean_ctor_get(v___x_5301_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v___x_5301_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5312_ = v___x_5301_;
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_a_5310_);
lean_dec(v___x_5301_);
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
}
}
}
else
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5328_; 
lean_dec(v_traceMsgs_5279_);
lean_dec(v_macroScope_5278_);
lean_dec(v_a_5277_);
lean_dec_ref(v___y_5238_);
v_a_5321_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5323_ = v___x_5282_;
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5282_);
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
}
else
{
lean_object* v_a_5329_; 
v_a_5329_ = lean_ctor_get(v___x_5275_, 0);
lean_inc(v_a_5329_);
lean_dec_ref(v___x_5275_);
if (lean_obj_tag(v_a_5329_) == 0)
{
lean_object* v_a_5330_; lean_object* v_a_5331_; lean_object* v___x_5332_; uint8_t v___x_5333_; 
v_a_5330_ = lean_ctor_get(v_a_5329_, 0);
lean_inc(v_a_5330_);
v_a_5331_ = lean_ctor_get(v_a_5329_, 1);
lean_inc_ref(v_a_5331_);
lean_dec_ref(v_a_5329_);
v___x_5332_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___closed__0));
v___x_5333_ = lean_string_dec_eq(v_a_5331_, v___x_5332_);
if (v___x_5333_ == 0)
{
lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5334_, 0, v_a_5331_);
v___x_5335_ = l_Lean_MessageData_ofFormat(v___x_5334_);
v___x_5336_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg(v_a_5330_, v___x_5335_, v___y_5238_, v___y_5239_);
lean_dec(v_a_5330_);
return v___x_5336_;
}
else
{
lean_object* v___x_5337_; 
lean_dec_ref(v_a_5331_);
lean_dec_ref(v___y_5238_);
v___x_5337_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg(v_a_5330_);
return v___x_5337_;
}
}
else
{
lean_object* v___x_5338_; 
lean_dec_ref(v___y_5238_);
v___x_5338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg();
return v___x_5338_;
}
}
}
}
else
{
lean_object* v_a_5342_; lean_object* v___x_5344_; uint8_t v_isShared_5345_; uint8_t v_isSharedCheck_5349_; 
lean_dec(v_a_5255_);
lean_dec(v_openDecls_5253_);
lean_dec(v_currNamespace_5250_);
lean_dec_ref(v_opts_5247_);
lean_dec_ref(v_env_5242_);
lean_dec_ref(v___y_5238_);
lean_dec_ref(v_x_5237_);
v_a_5342_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5344_ = v___x_5256_;
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
else
{
lean_inc(v_a_5342_);
lean_dec(v___x_5256_);
v___x_5344_ = lean_box(0);
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
v_resetjp_5343_:
{
lean_object* v___x_5347_; 
if (v_isShared_5345_ == 0)
{
v___x_5347_ = v___x_5344_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_a_5342_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
}
}
else
{
lean_object* v_a_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5357_; 
lean_dec(v_openDecls_5253_);
lean_dec(v_currNamespace_5250_);
lean_dec_ref(v_opts_5247_);
lean_dec_ref(v_env_5242_);
lean_dec_ref(v___y_5238_);
lean_dec_ref(v_x_5237_);
v_a_5350_ = lean_ctor_get(v___x_5254_, 0);
v_isSharedCheck_5357_ = !lean_is_exclusive(v___x_5254_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5352_ = v___x_5254_;
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_a_5350_);
lean_dec(v___x_5254_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5355_; 
if (v_isShared_5353_ == 0)
{
v___x_5355_ = v___x_5352_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5350_);
v___x_5355_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
return v___x_5355_;
}
}
}
}
else
{
lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
lean_dec(v_currNamespace_5250_);
lean_dec_ref(v_opts_5247_);
lean_dec_ref(v_env_5242_);
lean_dec_ref(v___y_5238_);
lean_dec_ref(v_x_5237_);
v_a_5358_ = lean_ctor_get(v___x_5251_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5251_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5360_ = v___x_5251_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5251_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
}
else
{
lean_object* v_a_5366_; lean_object* v___x_5368_; uint8_t v_isShared_5369_; uint8_t v_isSharedCheck_5373_; 
lean_dec_ref(v_opts_5247_);
lean_dec_ref(v_env_5242_);
lean_dec_ref(v___y_5238_);
lean_dec_ref(v_x_5237_);
v_a_5366_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5368_ = v___x_5248_;
v_isShared_5369_ = v_isSharedCheck_5373_;
goto v_resetjp_5367_;
}
else
{
lean_inc(v_a_5366_);
lean_dec(v___x_5248_);
v___x_5368_ = lean_box(0);
v_isShared_5369_ = v_isSharedCheck_5373_;
goto v_resetjp_5367_;
}
v_resetjp_5367_:
{
lean_object* v___x_5371_; 
if (v_isShared_5369_ == 0)
{
v___x_5371_ = v___x_5368_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_a_5366_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___boxed(lean_object* v_x_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_){
_start:
{
lean_object* v_res_5378_; 
v_res_5378_ = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg(v_x_5374_, v___y_5375_, v___y_5376_);
lean_dec(v___y_5376_);
return v_res_5378_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__10(void){
_start:
{
lean_object* v___x_5400_; 
v___x_5400_ = l_Array_mkArray0(lean_box(0));
return v___x_5400_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__22(void){
_start:
{
lean_object* v___x_5428_; lean_object* v___x_5429_; 
v___x_5428_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
v___x_5429_ = l_String_toRawSubstring_x27(v___x_5428_);
return v___x_5429_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38(void){
_start:
{
lean_object* v___x_5473_; lean_object* v___x_5474_; 
v___x_5473_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__0___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
v___x_5474_ = l_String_toRawSubstring_x27(v___x_5473_);
return v___x_5474_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__57(void){
_start:
{
lean_object* v___x_5515_; lean_object* v___x_5516_; 
v___x_5515_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__56));
v___x_5516_ = l_Lean_MessageData_ofFormat(v___x_5515_);
return v___x_5516_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions(lean_object* v_x_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_){
_start:
{
lean_object* v___x_5521_; uint8_t v___x_5522_; 
v___x_5521_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1));
lean_inc(v_x_5517_);
v___x_5522_ = l_Lean_Syntax_isOfKind(v_x_5517_, v___x_5521_);
if (v___x_5522_ == 0)
{
lean_object* v___x_5523_; 
lean_dec(v_a_5519_);
lean_dec_ref(v_a_5518_);
lean_dec(v_x_5517_);
v___x_5523_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg();
return v___x_5523_;
}
else
{
lean_object* v___x_5524_; lean_object* v_env_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___y_5529_; lean_object* v___y_5530_; lean_object* v___y_5531_; lean_object* v___y_5532_; lean_object* v___y_5533_; lean_object* v_a_5534_; lean_object* v___y_5604_; lean_object* v___y_5605_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; uint8_t v___x_5647_; 
v___x_5524_ = lean_st_ref_get(v_a_5519_);
v_env_5525_ = lean_ctor_get(v___x_5524_, 0);
lean_inc_ref(v_env_5525_);
lean_dec(v___x_5524_);
v___x_5526_ = lean_unsigned_to_nat(1u);
v___x_5527_ = l_Lean_Syntax_getArg(v_x_5517_, v___x_5526_);
lean_dec(v_x_5517_);
v___x_5643_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__0));
v___x_5644_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__54));
v___x_5645_ = l_Lean_Environment_header(v_env_5525_);
lean_dec_ref(v_env_5525_);
v___x_5646_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5645_);
v___x_5647_ = l_Array_contains___redArg(v___x_5643_, v___x_5646_, v___x_5644_);
if (v___x_5647_ == 0)
{
if (v___x_5522_ == 0)
{
v___y_5604_ = v_a_5518_;
v___y_5605_ = v_a_5519_;
goto v___jp_5603_;
}
else
{
lean_object* v___x_5648_; lean_object* v___x_5649_; 
v___x_5648_ = lean_obj_once(&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__57, &l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__57_once, _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__57);
lean_inc_ref(v_a_5518_);
v___x_5649_ = l_Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3(v___x_5648_, v_a_5518_, v_a_5519_);
if (lean_obj_tag(v___x_5649_) == 0)
{
lean_dec_ref(v___x_5649_);
v___y_5604_ = v_a_5518_;
v___y_5605_ = v_a_5519_;
goto v___jp_5603_;
}
else
{
lean_dec(v___x_5527_);
lean_dec(v_a_5519_);
lean_dec_ref(v_a_5518_);
return v___x_5649_;
}
}
}
else
{
v___y_5604_ = v_a_5518_;
v___y_5605_ = v_a_5519_;
goto v___jp_5603_;
}
v___jp_5528_:
{
lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; 
v___x_5535_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5));
v___x_5536_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7));
v___x_5537_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__9));
v___x_5538_ = lean_obj_once(&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__10, &l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__10_once, _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__10);
lean_inc(v___y_5533_);
v___x_5539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5539_, 0, v___y_5533_);
lean_ctor_set(v___x_5539_, 1, v___x_5537_);
lean_ctor_set(v___x_5539_, 2, v___x_5538_);
v___x_5540_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13));
v___x_5541_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__14));
lean_inc(v___y_5533_);
v___x_5542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5542_, 0, v___y_5533_);
lean_ctor_set(v___x_5542_, 1, v___x_5541_);
v___x_5543_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16));
v___x_5544_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18));
lean_inc_ref(v___x_5539_);
lean_inc(v___y_5533_);
v___x_5545_ = l_Lean_Syntax_node1(v___y_5533_, v___x_5544_, v___x_5539_);
v___x_5546_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21));
v___x_5547_ = lean_obj_once(&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__22, &l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__22_once, _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__22);
v___x_5548_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
lean_inc(v___y_5530_);
lean_inc(v_a_5534_);
v___x_5549_ = l_Lean_addMacroScope(v_a_5534_, v___x_5548_, v___y_5530_);
v___x_5550_ = lean_box(0);
lean_inc(v___y_5533_);
v___x_5551_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5551_, 0, v___y_5533_);
lean_ctor_set(v___x_5551_, 1, v___x_5547_);
lean_ctor_set(v___x_5551_, 2, v___x_5549_);
lean_ctor_set(v___x_5551_, 3, v___x_5550_);
lean_inc_ref(v___x_5539_);
lean_inc(v___y_5533_);
v___x_5552_ = l_Lean_Syntax_node2(v___y_5533_, v___x_5546_, v___x_5551_, v___x_5539_);
lean_inc(v___y_5533_);
v___x_5553_ = l_Lean_Syntax_node2(v___y_5533_, v___x_5543_, v___x_5545_, v___x_5552_);
lean_inc(v___y_5533_);
v___x_5554_ = l_Lean_Syntax_node1(v___y_5533_, v___x_5537_, v___x_5553_);
v___x_5555_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__23));
lean_inc(v___y_5533_);
v___x_5556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5556_, 0, v___y_5533_);
lean_ctor_set(v___x_5556_, 1, v___x_5555_);
lean_inc(v___y_5533_);
v___x_5557_ = l_Lean_Syntax_node3(v___y_5533_, v___x_5540_, v___x_5542_, v___x_5554_, v___x_5556_);
lean_inc(v___y_5533_);
v___x_5558_ = l_Lean_Syntax_node1(v___y_5533_, v___x_5537_, v___x_5557_);
v___x_5559_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__17));
v___x_5560_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24));
lean_inc(v___y_5533_);
v___x_5561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5561_, 0, v___y_5533_);
lean_ctor_set(v___x_5561_, 1, v___x_5559_);
lean_inc(v___y_5533_);
v___x_5562_ = l_Lean_Syntax_node1(v___y_5533_, v___x_5560_, v___x_5561_);
lean_inc(v___y_5533_);
v___x_5563_ = l_Lean_Syntax_node1(v___y_5533_, v___x_5537_, v___x_5562_);
v___x_5564_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__15));
v___x_5565_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25));
lean_inc(v___y_5533_);
v___x_5566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5566_, 0, v___y_5533_);
lean_ctor_set(v___x_5566_, 1, v___x_5564_);
lean_inc(v___y_5533_);
v___x_5567_ = l_Lean_Syntax_node1(v___y_5533_, v___x_5565_, v___x_5566_);
lean_inc(v___y_5533_);
v___x_5568_ = l_Lean_Syntax_node1(v___y_5533_, v___x_5537_, v___x_5567_);
lean_inc_ref_n(v___x_5539_, 4);
lean_inc(v___y_5533_);
v___x_5569_ = l_Lean_Syntax_node7(v___y_5533_, v___x_5536_, v___x_5539_, v___x_5558_, v___x_5563_, v___x_5539_, v___x_5568_, v___x_5539_, v___x_5539_);
v___x_5570_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27));
v___x_5571_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28));
lean_inc(v___y_5533_);
v___x_5572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5572_, 0, v___y_5533_);
lean_ctor_set(v___x_5572_, 1, v___x_5571_);
v___x_5573_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30));
v___x_5574_ = lean_mk_syntax_ident(v___y_5529_);
v___x_5575_ = lean_box(2);
v___x_5576_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__32));
v___x_5577_ = lean_unsigned_to_nat(2u);
v___x_5578_ = lean_mk_empty_array_with_capacity(v___x_5577_);
v___x_5579_ = lean_array_push(v___x_5578_, v___x_5574_);
v___x_5580_ = lean_array_push(v___x_5579_, v___x_5576_);
v___x_5581_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5581_, 0, v___x_5575_);
lean_ctor_set(v___x_5581_, 1, v___x_5573_);
lean_ctor_set(v___x_5581_, 2, v___x_5580_);
v___x_5582_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34));
v___x_5583_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36));
v___x_5584_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__37));
lean_inc(v___y_5533_);
v___x_5585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5585_, 0, v___y_5533_);
lean_ctor_set(v___x_5585_, 1, v___x_5584_);
v___x_5586_ = lean_obj_once(&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38, &l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38_once, _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38);
v___x_5587_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__39));
v___x_5588_ = l_Lean_addMacroScope(v_a_5534_, v___x_5587_, v___y_5530_);
v___x_5589_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__43));
lean_inc(v___y_5533_);
v___x_5590_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5590_, 0, v___y_5533_);
lean_ctor_set(v___x_5590_, 1, v___x_5586_);
lean_ctor_set(v___x_5590_, 2, v___x_5588_);
lean_ctor_set(v___x_5590_, 3, v___x_5589_);
lean_inc(v___y_5533_);
v___x_5591_ = l_Lean_Syntax_node2(v___y_5533_, v___x_5583_, v___x_5585_, v___x_5590_);
lean_inc(v___y_5533_);
v___x_5592_ = l_Lean_Syntax_node1(v___y_5533_, v___x_5537_, v___x_5591_);
lean_inc_ref(v___x_5539_);
lean_inc(v___y_5533_);
v___x_5593_ = l_Lean_Syntax_node2(v___y_5533_, v___x_5582_, v___x_5539_, v___x_5592_);
v___x_5594_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45));
v___x_5595_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__46));
lean_inc(v___y_5533_);
v___x_5596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5596_, 0, v___y_5533_);
lean_ctor_set(v___x_5596_, 1, v___x_5595_);
v___x_5597_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49));
lean_inc_ref_n(v___x_5539_, 2);
lean_inc(v___y_5533_);
v___x_5598_ = l_Lean_Syntax_node2(v___y_5533_, v___x_5597_, v___x_5539_, v___x_5539_);
lean_inc_ref(v___x_5539_);
lean_inc(v___y_5533_);
v___x_5599_ = l_Lean_Syntax_node4(v___y_5533_, v___x_5594_, v___x_5596_, v___x_5527_, v___x_5598_, v___x_5539_);
lean_inc(v___y_5533_);
v___x_5600_ = l_Lean_Syntax_node5(v___y_5533_, v___x_5570_, v___x_5572_, v___x_5581_, v___x_5593_, v___x_5599_, v___x_5539_);
v___x_5601_ = l_Lean_Syntax_node2(v___y_5533_, v___x_5535_, v___x_5569_, v___x_5600_);
v___x_5602_ = l_Lean_Elab_Command_elabCommand(v___x_5601_, v___y_5532_, v___y_5531_);
return v___x_5602_;
}
v___jp_5603_:
{
lean_object* v___x_5606_; lean_object* v___x_5607_; 
v___x_5606_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__52));
lean_inc_ref(v___y_5604_);
v___x_5607_ = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg(v___x_5606_, v___y_5604_, v___y_5605_);
if (lean_obj_tag(v___x_5607_) == 0)
{
lean_object* v_a_5608_; lean_object* v___x_5609_; 
v_a_5608_ = lean_ctor_get(v___x_5607_, 0);
lean_inc(v_a_5608_);
lean_dec_ref(v___x_5607_);
v___x_5609_ = l_Lean_Elab_Command_getRef___redArg(v___y_5604_);
if (lean_obj_tag(v___x_5609_) == 0)
{
lean_object* v_a_5610_; lean_object* v___x_5611_; 
v_a_5610_ = lean_ctor_get(v___x_5609_, 0);
lean_inc(v_a_5610_);
lean_dec_ref(v___x_5609_);
v___x_5611_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_5604_);
if (lean_obj_tag(v___x_5611_) == 0)
{
lean_object* v_a_5612_; lean_object* v_quotContext_x3f_5613_; uint8_t v___x_5614_; lean_object* v___x_5615_; 
v_a_5612_ = lean_ctor_get(v___x_5611_, 0);
lean_inc(v_a_5612_);
lean_dec_ref(v___x_5611_);
v_quotContext_x3f_5613_ = lean_ctor_get(v___y_5604_, 5);
v___x_5614_ = 0;
v___x_5615_ = l_Lean_SourceInfo_fromRef(v_a_5610_, v___x_5614_);
lean_dec(v_a_5610_);
if (lean_obj_tag(v_quotContext_x3f_5613_) == 0)
{
lean_object* v___x_5616_; lean_object* v_a_5617_; 
v___x_5616_ = l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg(v___y_5605_);
v_a_5617_ = lean_ctor_get(v___x_5616_, 0);
lean_inc(v_a_5617_);
lean_dec_ref(v___x_5616_);
v___y_5529_ = v_a_5608_;
v___y_5530_ = v_a_5612_;
v___y_5531_ = v___y_5605_;
v___y_5532_ = v___y_5604_;
v___y_5533_ = v___x_5615_;
v_a_5534_ = v_a_5617_;
goto v___jp_5528_;
}
else
{
lean_object* v_val_5618_; 
v_val_5618_ = lean_ctor_get(v_quotContext_x3f_5613_, 0);
lean_inc(v_val_5618_);
v___y_5529_ = v_a_5608_;
v___y_5530_ = v_a_5612_;
v___y_5531_ = v___y_5605_;
v___y_5532_ = v___y_5604_;
v___y_5533_ = v___x_5615_;
v_a_5534_ = v_val_5618_;
goto v___jp_5528_;
}
}
else
{
lean_object* v_a_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5626_; 
lean_dec(v_a_5610_);
lean_dec(v_a_5608_);
lean_dec(v___y_5605_);
lean_dec_ref(v___y_5604_);
lean_dec(v___x_5527_);
v_a_5619_ = lean_ctor_get(v___x_5611_, 0);
v_isSharedCheck_5626_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5626_ == 0)
{
v___x_5621_ = v___x_5611_;
v_isShared_5622_ = v_isSharedCheck_5626_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_a_5619_);
lean_dec(v___x_5611_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5626_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v___x_5624_; 
if (v_isShared_5622_ == 0)
{
v___x_5624_ = v___x_5621_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5625_; 
v_reuseFailAlloc_5625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5625_, 0, v_a_5619_);
v___x_5624_ = v_reuseFailAlloc_5625_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
return v___x_5624_;
}
}
}
}
else
{
lean_object* v_a_5627_; lean_object* v___x_5629_; uint8_t v_isShared_5630_; uint8_t v_isSharedCheck_5634_; 
lean_dec(v_a_5608_);
lean_dec(v___y_5605_);
lean_dec_ref(v___y_5604_);
lean_dec(v___x_5527_);
v_a_5627_ = lean_ctor_get(v___x_5609_, 0);
v_isSharedCheck_5634_ = !lean_is_exclusive(v___x_5609_);
if (v_isSharedCheck_5634_ == 0)
{
v___x_5629_ = v___x_5609_;
v_isShared_5630_ = v_isSharedCheck_5634_;
goto v_resetjp_5628_;
}
else
{
lean_inc(v_a_5627_);
lean_dec(v___x_5609_);
v___x_5629_ = lean_box(0);
v_isShared_5630_ = v_isSharedCheck_5634_;
goto v_resetjp_5628_;
}
v_resetjp_5628_:
{
lean_object* v___x_5632_; 
if (v_isShared_5630_ == 0)
{
v___x_5632_ = v___x_5629_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_a_5627_);
v___x_5632_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
return v___x_5632_;
}
}
}
}
else
{
lean_object* v_a_5635_; lean_object* v___x_5637_; uint8_t v_isShared_5638_; uint8_t v_isSharedCheck_5642_; 
lean_dec(v___y_5605_);
lean_dec_ref(v___y_5604_);
lean_dec(v___x_5527_);
v_a_5635_ = lean_ctor_get(v___x_5607_, 0);
v_isSharedCheck_5642_ = !lean_is_exclusive(v___x_5607_);
if (v_isSharedCheck_5642_ == 0)
{
v___x_5637_ = v___x_5607_;
v_isShared_5638_ = v_isSharedCheck_5642_;
goto v_resetjp_5636_;
}
else
{
lean_inc(v_a_5635_);
lean_dec(v___x_5607_);
v___x_5637_ = lean_box(0);
v_isShared_5638_ = v_isSharedCheck_5642_;
goto v_resetjp_5636_;
}
v_resetjp_5636_:
{
lean_object* v___x_5640_; 
if (v_isShared_5638_ == 0)
{
v___x_5640_ = v___x_5637_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5641_; 
v_reuseFailAlloc_5641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5641_, 0, v_a_5635_);
v___x_5640_ = v_reuseFailAlloc_5641_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
return v___x_5640_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___boxed(lean_object* v_x_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_){
_start:
{
lean_object* v_res_5654_; 
v_res_5654_ = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions(v_x_5650_, v_a_5651_, v_a_5652_);
return v_res_5654_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1(lean_object* v_cls_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_){
_start:
{
lean_object* v___x_5659_; 
v___x_5659_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg(v_cls_5655_, v___y_5657_);
return v___x_5659_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___boxed(lean_object* v_cls_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_){
_start:
{
lean_object* v_res_5664_; 
v_res_5664_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1(v_cls_5660_, v___y_5661_, v___y_5662_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
return v_res_5664_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3(lean_object* v_00_u03b1_5665_, lean_object* v_x_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_){
_start:
{
lean_object* v___x_5669_; 
v___x_5669_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(v_x_5666_, v___y_5668_);
return v___x_5669_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___boxed(lean_object* v_00_u03b1_5670_, lean_object* v_x_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
lean_object* v_res_5674_; 
v_res_5674_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3(v_00_u03b1_5670_, v_x_5671_, v___y_5672_, v___y_5673_);
lean_dec_ref(v___y_5672_);
lean_dec_ref(v_x_5671_);
return v_res_5674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8(lean_object* v_00_u03b1_5675_, lean_object* v_ref_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_){
_start:
{
lean_object* v___x_5680_; 
v___x_5680_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg(v_ref_5676_);
return v___x_5680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___boxed(lean_object* v_00_u03b1_5681_, lean_object* v_ref_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_){
_start:
{
lean_object* v_res_5686_; 
v_res_5686_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8(v_00_u03b1_5681_, v_ref_5682_, v___y_5683_, v___y_5684_);
lean_dec(v___y_5684_);
lean_dec_ref(v___y_5683_);
return v_res_5686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1(lean_object* v_00_u03b1_5687_, lean_object* v_x_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_){
_start:
{
lean_object* v___x_5692_; 
v___x_5692_ = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg(v_x_5688_, v___y_5689_, v___y_5690_);
return v___x_5692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___boxed(lean_object* v_00_u03b1_5693_, lean_object* v_x_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_){
_start:
{
lean_object* v_res_5698_; 
v_res_5698_ = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1(v_00_u03b1_5693_, v_x_5694_, v___y_5695_, v___y_5696_);
lean_dec(v___y_5696_);
return v_res_5698_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4(lean_object* v_msgData_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_){
_start:
{
lean_object* v___x_5703_; 
v___x_5703_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(v_msgData_5699_, v___y_5701_);
return v___x_5703_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_){
_start:
{
lean_object* v_res_5708_; 
v_res_5708_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4(v_msgData_5704_, v___y_5705_, v___y_5706_);
lean_dec(v___y_5706_);
lean_dec_ref(v___y_5705_);
return v_res_5708_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5(lean_object* v_as_5709_, lean_object* v_as_x27_5710_, lean_object* v_b_5711_, lean_object* v_a_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_){
_start:
{
lean_object* v___x_5716_; 
v___x_5716_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg(v_as_x27_5710_, v_b_5711_, v___y_5713_, v___y_5714_);
return v___x_5716_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___boxed(lean_object* v_as_5717_, lean_object* v_as_x27_5718_, lean_object* v_b_5719_, lean_object* v_a_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_){
_start:
{
lean_object* v_res_5724_; 
v_res_5724_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5(v_as_5717_, v_as_x27_5718_, v_b_5719_, v_a_5720_, v___y_5721_, v___y_5722_);
lean_dec(v___y_5722_);
lean_dec_ref(v___y_5721_);
lean_dec(v_as_5717_);
return v_res_5724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7(lean_object* v_00_u03b1_5725_, lean_object* v_ref_5726_, lean_object* v_msg_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_){
_start:
{
lean_object* v___x_5731_; 
v___x_5731_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg(v_ref_5726_, v_msg_5727_, v___y_5728_, v___y_5729_);
return v___x_5731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___boxed(lean_object* v_00_u03b1_5732_, lean_object* v_ref_5733_, lean_object* v_msg_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_){
_start:
{
lean_object* v_res_5738_; 
v_res_5738_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7(v_00_u03b1_5732_, v_ref_5733_, v_msg_5734_, v___y_5735_, v___y_5736_);
lean_dec(v___y_5736_);
lean_dec(v_ref_5733_);
return v_res_5738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_5739_, lean_object* v_m_5740_, lean_object* v_a_5741_){
_start:
{
lean_object* v___x_5742_; 
v___x_5742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg(v_m_5740_, v_a_5741_);
return v___x_5742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___boxed(lean_object* v_00_u03b2_5743_, lean_object* v_m_5744_, lean_object* v_a_5745_){
_start:
{
lean_object* v_res_5746_; 
v_res_5746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9(v_00_u03b2_5743_, v_m_5744_, v_a_5745_);
lean_dec(v_a_5745_);
lean_dec_ref(v_m_5744_);
return v_res_5746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13(lean_object* v_00_u03b1_5747_, lean_object* v_msg_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_){
_start:
{
lean_object* v___x_5752_; 
v___x_5752_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg(v_msg_5748_, v___y_5749_, v___y_5750_);
return v___x_5752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___boxed(lean_object* v_00_u03b1_5753_, lean_object* v_msg_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_){
_start:
{
lean_object* v_res_5758_; 
v_res_5758_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13(v_00_u03b1_5753_, v_msg_5754_, v___y_5755_, v___y_5756_);
lean_dec(v___y_5756_);
return v_res_5758_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_5759_, lean_object* v_x_5760_, lean_object* v_x_5761_){
_start:
{
uint8_t v___x_5762_; 
v___x_5762_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg(v_x_5760_, v_x_5761_);
return v___x_5762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_5763_, lean_object* v_x_5764_, lean_object* v_x_5765_){
_start:
{
uint8_t v_res_5766_; lean_object* v_r_5767_; 
v_res_5766_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10(v_00_u03b2_5763_, v_x_5764_, v_x_5765_);
lean_dec_ref(v_x_5765_);
v_r_5767_ = lean_box(v_res_5766_);
return v_r_5767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13(lean_object* v_00_u03b2_5768_, lean_object* v_a_5769_, lean_object* v_x_5770_){
_start:
{
lean_object* v___x_5771_; 
v___x_5771_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg(v_a_5769_, v_x_5770_);
return v___x_5771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___boxed(lean_object* v_00_u03b2_5772_, lean_object* v_a_5773_, lean_object* v_x_5774_){
_start:
{
lean_object* v_res_5775_; 
v_res_5775_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13(v_00_u03b2_5772_, v_a_5773_, v_x_5774_);
lean_dec(v_x_5774_);
lean_dec(v_a_5773_);
return v_res_5775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18(lean_object* v_msgData_5776_, lean_object* v_macroStack_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_){
_start:
{
lean_object* v___x_5781_; 
v___x_5781_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg(v_msgData_5776_, v_macroStack_5777_, v___y_5779_);
return v___x_5781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___boxed(lean_object* v_msgData_5782_, lean_object* v_macroStack_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_){
_start:
{
lean_object* v_res_5787_; 
v_res_5787_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18(v_msgData_5782_, v_macroStack_5783_, v___y_5784_, v___y_5785_);
lean_dec(v___y_5785_);
lean_dec_ref(v___y_5784_);
return v_res_5787_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15(lean_object* v_00_u03b2_5788_, lean_object* v_x_5789_, size_t v_x_5790_, lean_object* v_x_5791_){
_start:
{
uint8_t v___x_5792_; 
v___x_5792_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg(v_x_5789_, v_x_5790_, v_x_5791_);
return v___x_5792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___boxed(lean_object* v_00_u03b2_5793_, lean_object* v_x_5794_, lean_object* v_x_5795_, lean_object* v_x_5796_){
_start:
{
size_t v_x_17372__boxed_5797_; uint8_t v_res_5798_; lean_object* v_r_5799_; 
v_x_17372__boxed_5797_ = lean_unbox_usize(v_x_5795_);
lean_dec(v_x_5795_);
v_res_5798_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15(v_00_u03b2_5793_, v_x_5794_, v_x_17372__boxed_5797_, v_x_5796_);
lean_dec_ref(v_x_5796_);
v_r_5799_ = lean_box(v_res_5798_);
return v_r_5799_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21(lean_object* v_00_u03b2_5800_, lean_object* v_keys_5801_, lean_object* v_vals_5802_, lean_object* v_heq_5803_, lean_object* v_i_5804_, lean_object* v_k_5805_){
_start:
{
uint8_t v___x_5806_; 
v___x_5806_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg(v_keys_5801_, v_i_5804_, v_k_5805_);
return v___x_5806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___boxed(lean_object* v_00_u03b2_5807_, lean_object* v_keys_5808_, lean_object* v_vals_5809_, lean_object* v_heq_5810_, lean_object* v_i_5811_, lean_object* v_k_5812_){
_start:
{
uint8_t v_res_5813_; lean_object* v_r_5814_; 
v_res_5813_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21(v_00_u03b2_5807_, v_keys_5808_, v_vals_5809_, v_heq_5810_, v_i_5811_, v_k_5812_);
lean_dec_ref(v_k_5812_);
lean_dec_ref(v_vals_5809_);
lean_dec_ref(v_keys_5808_);
v_r_5814_ = lean_box(v_res_5813_);
return v_r_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1(){
_start:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; 
v___x_5821_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_5822_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1));
v___x_5823_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1));
v___x_5824_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___boxed), 4, 0);
v___x_5825_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5821_, v___x_5822_, v___x_5823_, v___x_5824_);
return v___x_5825_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___boxed(lean_object* v_a_5826_){
_start:
{
lean_object* v_res_5827_; 
v_res_5827_ = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1();
return v_res_5827_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2(lean_object* v_as_5828_, size_t v_i_5829_, size_t v_stop_5830_){
_start:
{
uint8_t v___x_5831_; 
v___x_5831_ = lean_usize_dec_eq(v_i_5829_, v_stop_5830_);
if (v___x_5831_ == 0)
{
lean_object* v___x_5832_; double v_score_5833_; uint8_t v___x_5834_; double v___x_5835_; uint8_t v___x_5836_; 
v___x_5832_ = lean_array_uget_borrowed(v_as_5828_, v_i_5829_);
v_score_5833_ = lean_ctor_get_float(v___x_5832_, sizeof(void*)*2);
v___x_5834_ = 1;
v___x_5835_ = lean_float_once(&l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___closed__0, &l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___closed__0_once, _init_l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___closed__0);
v___x_5836_ = lean_float_beq(v_score_5833_, v___x_5835_);
if (v___x_5836_ == 0)
{
return v___x_5834_;
}
else
{
if (v___x_5831_ == 0)
{
size_t v___x_5837_; size_t v___x_5838_; 
v___x_5837_ = ((size_t)1ULL);
v___x_5838_ = lean_usize_add(v_i_5829_, v___x_5837_);
v_i_5829_ = v___x_5838_;
goto _start;
}
else
{
return v___x_5834_;
}
}
}
else
{
uint8_t v___x_5840_; 
v___x_5840_ = 0;
return v___x_5840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2___boxed(lean_object* v_as_5841_, lean_object* v_i_5842_, lean_object* v_stop_5843_){
_start:
{
size_t v_i_boxed_5844_; size_t v_stop_boxed_5845_; uint8_t v_res_5846_; lean_object* v_r_5847_; 
v_i_boxed_5844_ = lean_unbox_usize(v_i_5842_);
lean_dec(v_i_5842_);
v_stop_boxed_5845_ = lean_unbox_usize(v_stop_5843_);
lean_dec(v_stop_5843_);
v_res_5846_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2(v_as_5841_, v_i_boxed_5844_, v_stop_boxed_5845_);
lean_dec_ref(v_as_5841_);
v_r_5847_ = lean_box(v_res_5846_);
return v_r_5847_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0(uint8_t v___y_5854_, uint8_t v_suppressElabErrors_5855_, lean_object* v_x_5856_){
_start:
{
if (lean_obj_tag(v_x_5856_) == 1)
{
lean_object* v_pre_5857_; 
v_pre_5857_ = lean_ctor_get(v_x_5856_, 0);
switch(lean_obj_tag(v_pre_5857_))
{
case 1:
{
lean_object* v_pre_5858_; 
v_pre_5858_ = lean_ctor_get(v_pre_5857_, 0);
switch(lean_obj_tag(v_pre_5858_))
{
case 0:
{
lean_object* v_str_5859_; lean_object* v_str_5860_; lean_object* v___x_5861_; uint8_t v___x_5862_; 
v_str_5859_ = lean_ctor_get(v_x_5856_, 1);
v_str_5860_ = lean_ctor_get(v_pre_5857_, 1);
v___x_5861_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_5862_ = lean_string_dec_eq(v_str_5860_, v___x_5861_);
if (v___x_5862_ == 0)
{
lean_object* v___x_5863_; uint8_t v___x_5864_; 
v___x_5863_ = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_));
v___x_5864_ = lean_string_dec_eq(v_str_5860_, v___x_5863_);
if (v___x_5864_ == 0)
{
return v___y_5854_;
}
else
{
lean_object* v___x_5865_; uint8_t v___x_5866_; 
v___x_5865_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__1));
v___x_5866_ = lean_string_dec_eq(v_str_5859_, v___x_5865_);
if (v___x_5866_ == 0)
{
return v___y_5854_;
}
else
{
return v_suppressElabErrors_5855_;
}
}
}
else
{
lean_object* v___x_5867_; uint8_t v___x_5868_; 
v___x_5867_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__2));
v___x_5868_ = lean_string_dec_eq(v_str_5859_, v___x_5867_);
if (v___x_5868_ == 0)
{
return v___y_5854_;
}
else
{
return v_suppressElabErrors_5855_;
}
}
}
case 1:
{
lean_object* v_pre_5869_; 
v_pre_5869_ = lean_ctor_get(v_pre_5858_, 0);
if (lean_obj_tag(v_pre_5869_) == 0)
{
lean_object* v_str_5870_; lean_object* v_str_5871_; lean_object* v_str_5872_; lean_object* v___x_5873_; uint8_t v___x_5874_; 
v_str_5870_ = lean_ctor_get(v_x_5856_, 1);
v_str_5871_ = lean_ctor_get(v_pre_5857_, 1);
v_str_5872_ = lean_ctor_get(v_pre_5858_, 1);
v___x_5873_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__3));
v___x_5874_ = lean_string_dec_eq(v_str_5872_, v___x_5873_);
if (v___x_5874_ == 0)
{
return v___y_5854_;
}
else
{
lean_object* v___x_5875_; uint8_t v___x_5876_; 
v___x_5875_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__4));
v___x_5876_ = lean_string_dec_eq(v_str_5871_, v___x_5875_);
if (v___x_5876_ == 0)
{
return v___y_5854_;
}
else
{
lean_object* v___x_5877_; uint8_t v___x_5878_; 
v___x_5877_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__5));
v___x_5878_ = lean_string_dec_eq(v_str_5870_, v___x_5877_);
if (v___x_5878_ == 0)
{
return v___y_5854_;
}
else
{
return v_suppressElabErrors_5855_;
}
}
}
}
else
{
return v___y_5854_;
}
}
default: 
{
return v___y_5854_;
}
}
}
case 0:
{
lean_object* v_str_5879_; lean_object* v___x_5880_; uint8_t v___x_5881_; 
v_str_5879_ = lean_ctor_get(v_x_5856_, 1);
v___x_5880_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___closed__0));
v___x_5881_ = lean_string_dec_eq(v_str_5879_, v___x_5880_);
if (v___x_5881_ == 0)
{
return v___y_5854_;
}
else
{
return v_suppressElabErrors_5855_;
}
}
default: 
{
return v___y_5854_;
}
}
}
else
{
return v___y_5854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v___y_5882_, lean_object* v_suppressElabErrors_5883_, lean_object* v_x_5884_){
_start:
{
uint8_t v___y_4976__boxed_5885_; uint8_t v_suppressElabErrors_boxed_5886_; uint8_t v_res_5887_; lean_object* v_r_5888_; 
v___y_4976__boxed_5885_ = lean_unbox(v___y_5882_);
v_suppressElabErrors_boxed_5886_ = lean_unbox(v_suppressElabErrors_5883_);
v_res_5887_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0(v___y_4976__boxed_5885_, v_suppressElabErrors_boxed_5886_, v_x_5884_);
lean_dec(v_x_5884_);
v_r_5888_ = lean_box(v_res_5887_);
return v_r_5888_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2(lean_object* v_ref_5889_, lean_object* v_msgData_5890_, uint8_t v_severity_5891_, uint8_t v_isSilent_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_){
_start:
{
uint8_t v___y_5899_; lean_object* v___y_5900_; uint8_t v___y_5901_; lean_object* v___y_5902_; lean_object* v___y_5903_; lean_object* v___y_5904_; lean_object* v___y_5905_; lean_object* v___y_5906_; lean_object* v___y_5907_; lean_object* v___y_5935_; uint8_t v___y_5936_; uint8_t v___y_5937_; lean_object* v___y_5938_; lean_object* v___y_5939_; lean_object* v___y_5940_; uint8_t v___y_5941_; lean_object* v___y_5942_; lean_object* v___y_5960_; uint8_t v___y_5961_; uint8_t v___y_5962_; lean_object* v___y_5963_; lean_object* v___y_5964_; lean_object* v___y_5965_; uint8_t v___y_5966_; lean_object* v___y_5967_; lean_object* v___y_5971_; lean_object* v___y_5972_; uint8_t v___y_5973_; lean_object* v___y_5974_; lean_object* v___y_5975_; uint8_t v___y_5976_; uint8_t v___y_5977_; uint8_t v___x_5982_; lean_object* v___y_5984_; lean_object* v___y_5985_; lean_object* v___y_5986_; lean_object* v___y_5987_; uint8_t v___y_5988_; uint8_t v___y_5989_; uint8_t v___y_5990_; uint8_t v___y_5992_; uint8_t v___x_6007_; 
v___x_5982_ = 2;
v___x_6007_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5891_, v___x_5982_);
if (v___x_6007_ == 0)
{
v___y_5992_ = v___x_6007_;
goto v___jp_5991_;
}
else
{
uint8_t v___x_6008_; 
lean_inc_ref(v_msgData_5890_);
v___x_6008_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5890_);
v___y_5992_ = v___x_6008_;
goto v___jp_5991_;
}
v___jp_5898_:
{
lean_object* v___x_5908_; lean_object* v_currNamespace_5909_; lean_object* v_openDecls_5910_; lean_object* v_env_5911_; lean_object* v_nextMacroScope_5912_; lean_object* v_ngen_5913_; lean_object* v_auxDeclNGen_5914_; lean_object* v_traceState_5915_; lean_object* v_cache_5916_; lean_object* v_messages_5917_; lean_object* v_infoState_5918_; lean_object* v_snapshotTasks_5919_; lean_object* v___x_5921_; uint8_t v_isShared_5922_; uint8_t v_isSharedCheck_5933_; 
v___x_5908_ = lean_st_ref_take(v___y_5907_);
v_currNamespace_5909_ = lean_ctor_get(v___y_5906_, 6);
lean_inc(v_currNamespace_5909_);
v_openDecls_5910_ = lean_ctor_get(v___y_5906_, 7);
lean_inc(v_openDecls_5910_);
lean_dec_ref(v___y_5906_);
v_env_5911_ = lean_ctor_get(v___x_5908_, 0);
v_nextMacroScope_5912_ = lean_ctor_get(v___x_5908_, 1);
v_ngen_5913_ = lean_ctor_get(v___x_5908_, 2);
v_auxDeclNGen_5914_ = lean_ctor_get(v___x_5908_, 3);
v_traceState_5915_ = lean_ctor_get(v___x_5908_, 4);
v_cache_5916_ = lean_ctor_get(v___x_5908_, 5);
v_messages_5917_ = lean_ctor_get(v___x_5908_, 6);
v_infoState_5918_ = lean_ctor_get(v___x_5908_, 7);
v_snapshotTasks_5919_ = lean_ctor_get(v___x_5908_, 8);
v_isSharedCheck_5933_ = !lean_is_exclusive(v___x_5908_);
if (v_isSharedCheck_5933_ == 0)
{
v___x_5921_ = v___x_5908_;
v_isShared_5922_ = v_isSharedCheck_5933_;
goto v_resetjp_5920_;
}
else
{
lean_inc(v_snapshotTasks_5919_);
lean_inc(v_infoState_5918_);
lean_inc(v_messages_5917_);
lean_inc(v_cache_5916_);
lean_inc(v_traceState_5915_);
lean_inc(v_auxDeclNGen_5914_);
lean_inc(v_ngen_5913_);
lean_inc(v_nextMacroScope_5912_);
lean_inc(v_env_5911_);
lean_dec(v___x_5908_);
v___x_5921_ = lean_box(0);
v_isShared_5922_ = v_isSharedCheck_5933_;
goto v_resetjp_5920_;
}
v_resetjp_5920_:
{
lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5928_; 
v___x_5923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5923_, 0, v_currNamespace_5909_);
lean_ctor_set(v___x_5923_, 1, v_openDecls_5910_);
v___x_5924_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5924_, 0, v___x_5923_);
lean_ctor_set(v___x_5924_, 1, v___y_5904_);
v___x_5925_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_5925_, 0, v___y_5903_);
lean_ctor_set(v___x_5925_, 1, v___y_5902_);
lean_ctor_set(v___x_5925_, 2, v___y_5900_);
lean_ctor_set(v___x_5925_, 3, v___y_5905_);
lean_ctor_set(v___x_5925_, 4, v___x_5924_);
lean_ctor_set_uint8(v___x_5925_, sizeof(void*)*5, v___y_5899_);
lean_ctor_set_uint8(v___x_5925_, sizeof(void*)*5 + 1, v___y_5901_);
lean_ctor_set_uint8(v___x_5925_, sizeof(void*)*5 + 2, v_isSilent_5892_);
v___x_5926_ = l_Lean_MessageLog_add(v___x_5925_, v_messages_5917_);
if (v_isShared_5922_ == 0)
{
lean_ctor_set(v___x_5921_, 6, v___x_5926_);
v___x_5928_ = v___x_5921_;
goto v_reusejp_5927_;
}
else
{
lean_object* v_reuseFailAlloc_5932_; 
v_reuseFailAlloc_5932_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5932_, 0, v_env_5911_);
lean_ctor_set(v_reuseFailAlloc_5932_, 1, v_nextMacroScope_5912_);
lean_ctor_set(v_reuseFailAlloc_5932_, 2, v_ngen_5913_);
lean_ctor_set(v_reuseFailAlloc_5932_, 3, v_auxDeclNGen_5914_);
lean_ctor_set(v_reuseFailAlloc_5932_, 4, v_traceState_5915_);
lean_ctor_set(v_reuseFailAlloc_5932_, 5, v_cache_5916_);
lean_ctor_set(v_reuseFailAlloc_5932_, 6, v___x_5926_);
lean_ctor_set(v_reuseFailAlloc_5932_, 7, v_infoState_5918_);
lean_ctor_set(v_reuseFailAlloc_5932_, 8, v_snapshotTasks_5919_);
v___x_5928_ = v_reuseFailAlloc_5932_;
goto v_reusejp_5927_;
}
v_reusejp_5927_:
{
lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; 
v___x_5929_ = lean_st_ref_set(v___y_5907_, v___x_5928_);
v___x_5930_ = lean_box(0);
v___x_5931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5931_, 0, v___x_5930_);
return v___x_5931_;
}
}
}
v___jp_5934_:
{
lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v_a_5945_; lean_object* v___x_5947_; uint8_t v_isShared_5948_; uint8_t v_isSharedCheck_5958_; 
v___x_5943_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_5890_);
v___x_5944_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3(v___x_5943_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_);
v_a_5945_ = lean_ctor_get(v___x_5944_, 0);
v_isSharedCheck_5958_ = !lean_is_exclusive(v___x_5944_);
if (v_isSharedCheck_5958_ == 0)
{
v___x_5947_ = v___x_5944_;
v_isShared_5948_ = v_isSharedCheck_5958_;
goto v_resetjp_5946_;
}
else
{
lean_inc(v_a_5945_);
lean_dec(v___x_5944_);
v___x_5947_ = lean_box(0);
v_isShared_5948_ = v_isSharedCheck_5958_;
goto v_resetjp_5946_;
}
v_resetjp_5946_:
{
lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; 
lean_inc_ref(v___y_5940_);
v___x_5949_ = l_Lean_FileMap_toPosition(v___y_5940_, v___y_5938_);
lean_dec(v___y_5938_);
v___x_5950_ = l_Lean_FileMap_toPosition(v___y_5940_, v___y_5942_);
lean_dec(v___y_5942_);
v___x_5951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5951_, 0, v___x_5950_);
v___x_5952_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
if (v___y_5941_ == 0)
{
lean_del_object(v___x_5947_);
lean_dec_ref(v___y_5935_);
v___y_5899_ = v___y_5936_;
v___y_5900_ = v___x_5951_;
v___y_5901_ = v___y_5937_;
v___y_5902_ = v___x_5949_;
v___y_5903_ = v___y_5939_;
v___y_5904_ = v_a_5945_;
v___y_5905_ = v___x_5952_;
v___y_5906_ = v___y_5895_;
v___y_5907_ = v___y_5896_;
goto v___jp_5898_;
}
else
{
uint8_t v___x_5953_; 
lean_inc(v_a_5945_);
v___x_5953_ = l_Lean_MessageData_hasTag(v___y_5935_, v_a_5945_);
if (v___x_5953_ == 0)
{
lean_object* v___x_5954_; lean_object* v___x_5956_; 
lean_dec_ref(v___x_5951_);
lean_dec_ref(v___x_5949_);
lean_dec(v_a_5945_);
lean_dec_ref(v___y_5939_);
lean_dec_ref(v___y_5895_);
v___x_5954_ = lean_box(0);
if (v_isShared_5948_ == 0)
{
lean_ctor_set(v___x_5947_, 0, v___x_5954_);
v___x_5956_ = v___x_5947_;
goto v_reusejp_5955_;
}
else
{
lean_object* v_reuseFailAlloc_5957_; 
v_reuseFailAlloc_5957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5957_, 0, v___x_5954_);
v___x_5956_ = v_reuseFailAlloc_5957_;
goto v_reusejp_5955_;
}
v_reusejp_5955_:
{
return v___x_5956_;
}
}
else
{
lean_del_object(v___x_5947_);
v___y_5899_ = v___y_5936_;
v___y_5900_ = v___x_5951_;
v___y_5901_ = v___y_5937_;
v___y_5902_ = v___x_5949_;
v___y_5903_ = v___y_5939_;
v___y_5904_ = v_a_5945_;
v___y_5905_ = v___x_5952_;
v___y_5906_ = v___y_5895_;
v___y_5907_ = v___y_5896_;
goto v___jp_5898_;
}
}
}
}
v___jp_5959_:
{
lean_object* v___x_5968_; 
v___x_5968_ = l_Lean_Syntax_getTailPos_x3f(v___y_5964_, v___y_5961_);
lean_dec(v___y_5964_);
if (lean_obj_tag(v___x_5968_) == 0)
{
lean_inc(v___y_5967_);
v___y_5935_ = v___y_5960_;
v___y_5936_ = v___y_5961_;
v___y_5937_ = v___y_5962_;
v___y_5938_ = v___y_5967_;
v___y_5939_ = v___y_5963_;
v___y_5940_ = v___y_5965_;
v___y_5941_ = v___y_5966_;
v___y_5942_ = v___y_5967_;
goto v___jp_5934_;
}
else
{
lean_object* v_val_5969_; 
v_val_5969_ = lean_ctor_get(v___x_5968_, 0);
lean_inc(v_val_5969_);
lean_dec_ref(v___x_5968_);
v___y_5935_ = v___y_5960_;
v___y_5936_ = v___y_5961_;
v___y_5937_ = v___y_5962_;
v___y_5938_ = v___y_5967_;
v___y_5939_ = v___y_5963_;
v___y_5940_ = v___y_5965_;
v___y_5941_ = v___y_5966_;
v___y_5942_ = v_val_5969_;
goto v___jp_5934_;
}
}
v___jp_5970_:
{
lean_object* v_ref_5978_; lean_object* v___x_5979_; 
v_ref_5978_ = l_Lean_replaceRef(v_ref_5889_, v___y_5972_);
lean_dec(v___y_5972_);
v___x_5979_ = l_Lean_Syntax_getPos_x3f(v_ref_5978_, v___y_5973_);
if (lean_obj_tag(v___x_5979_) == 0)
{
lean_object* v___x_5980_; 
v___x_5980_ = lean_unsigned_to_nat(0u);
v___y_5960_ = v___y_5971_;
v___y_5961_ = v___y_5973_;
v___y_5962_ = v___y_5977_;
v___y_5963_ = v___y_5974_;
v___y_5964_ = v_ref_5978_;
v___y_5965_ = v___y_5975_;
v___y_5966_ = v___y_5976_;
v___y_5967_ = v___x_5980_;
goto v___jp_5959_;
}
else
{
lean_object* v_val_5981_; 
v_val_5981_ = lean_ctor_get(v___x_5979_, 0);
lean_inc(v_val_5981_);
lean_dec_ref(v___x_5979_);
v___y_5960_ = v___y_5971_;
v___y_5961_ = v___y_5973_;
v___y_5962_ = v___y_5977_;
v___y_5963_ = v___y_5974_;
v___y_5964_ = v_ref_5978_;
v___y_5965_ = v___y_5975_;
v___y_5966_ = v___y_5976_;
v___y_5967_ = v_val_5981_;
goto v___jp_5959_;
}
}
v___jp_5983_:
{
if (v___y_5990_ == 0)
{
v___y_5971_ = v___y_5985_;
v___y_5972_ = v___y_5984_;
v___y_5973_ = v___y_5989_;
v___y_5974_ = v___y_5986_;
v___y_5975_ = v___y_5987_;
v___y_5976_ = v___y_5988_;
v___y_5977_ = v_severity_5891_;
goto v___jp_5970_;
}
else
{
v___y_5971_ = v___y_5985_;
v___y_5972_ = v___y_5984_;
v___y_5973_ = v___y_5989_;
v___y_5974_ = v___y_5986_;
v___y_5975_ = v___y_5987_;
v___y_5976_ = v___y_5988_;
v___y_5977_ = v___x_5982_;
goto v___jp_5970_;
}
}
v___jp_5991_:
{
if (v___y_5992_ == 0)
{
lean_object* v_fileName_5993_; lean_object* v_fileMap_5994_; lean_object* v_options_5995_; lean_object* v_ref_5996_; uint8_t v_suppressElabErrors_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___f_6000_; uint8_t v___x_6001_; uint8_t v___x_6002_; 
v_fileName_5993_ = lean_ctor_get(v___y_5895_, 0);
v_fileMap_5994_ = lean_ctor_get(v___y_5895_, 1);
v_options_5995_ = lean_ctor_get(v___y_5895_, 2);
v_ref_5996_ = lean_ctor_get(v___y_5895_, 5);
v_suppressElabErrors_5997_ = lean_ctor_get_uint8(v___y_5895_, sizeof(void*)*14 + 1);
v___x_5998_ = lean_box(v___y_5992_);
v___x_5999_ = lean_box(v_suppressElabErrors_5997_);
v___f_6000_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6000_, 0, v___x_5998_);
lean_closure_set(v___f_6000_, 1, v___x_5999_);
v___x_6001_ = 1;
v___x_6002_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5891_, v___x_6001_);
if (v___x_6002_ == 0)
{
lean_inc_ref(v_fileMap_5994_);
lean_inc_ref(v_fileName_5993_);
lean_inc(v_ref_5996_);
v___y_5984_ = v_ref_5996_;
v___y_5985_ = v___f_6000_;
v___y_5986_ = v_fileName_5993_;
v___y_5987_ = v_fileMap_5994_;
v___y_5988_ = v_suppressElabErrors_5997_;
v___y_5989_ = v___y_5992_;
v___y_5990_ = v___x_6002_;
goto v___jp_5983_;
}
else
{
lean_object* v___x_6003_; uint8_t v___x_6004_; 
v___x_6003_ = l_Lean_warningAsError;
v___x_6004_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21(v_options_5995_, v___x_6003_);
lean_inc_ref(v_fileMap_5994_);
lean_inc_ref(v_fileName_5993_);
lean_inc(v_ref_5996_);
v___y_5984_ = v_ref_5996_;
v___y_5985_ = v___f_6000_;
v___y_5986_ = v_fileName_5993_;
v___y_5987_ = v_fileMap_5994_;
v___y_5988_ = v_suppressElabErrors_5997_;
v___y_5989_ = v___y_5992_;
v___y_5990_ = v___x_6004_;
goto v___jp_5983_;
}
}
else
{
lean_object* v___x_6005_; lean_object* v___x_6006_; 
lean_dec_ref(v___y_5895_);
lean_dec_ref(v_msgData_5890_);
v___x_6005_ = lean_box(0);
v___x_6006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6006_, 0, v___x_6005_);
return v___x_6006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_6009_, lean_object* v_msgData_6010_, lean_object* v_severity_6011_, lean_object* v_isSilent_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_){
_start:
{
uint8_t v_severity_boxed_6018_; uint8_t v_isSilent_boxed_6019_; lean_object* v_res_6020_; 
v_severity_boxed_6018_ = lean_unbox(v_severity_6011_);
v_isSilent_boxed_6019_ = lean_unbox(v_isSilent_6012_);
v_res_6020_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2(v_ref_6009_, v_msgData_6010_, v_severity_boxed_6018_, v_isSilent_boxed_6019_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_);
lean_dec(v___y_6016_);
lean_dec(v___y_6014_);
lean_dec_ref(v___y_6013_);
lean_dec(v_ref_6009_);
return v_res_6020_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1(lean_object* v_msgData_6021_, uint8_t v_severity_6022_, uint8_t v_isSilent_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_){
_start:
{
lean_object* v_ref_6029_; lean_object* v___x_6030_; 
v_ref_6029_ = lean_ctor_get(v___y_6026_, 5);
lean_inc(v_ref_6029_);
v___x_6030_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2(v_ref_6029_, v_msgData_6021_, v_severity_6022_, v_isSilent_6023_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_);
lean_dec(v_ref_6029_);
return v___x_6030_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1___boxed(lean_object* v_msgData_6031_, lean_object* v_severity_6032_, lean_object* v_isSilent_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_){
_start:
{
uint8_t v_severity_boxed_6039_; uint8_t v_isSilent_boxed_6040_; lean_object* v_res_6041_; 
v_severity_boxed_6039_ = lean_unbox(v_severity_6032_);
v_isSilent_boxed_6040_ = lean_unbox(v_isSilent_6033_);
v_res_6041_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1(v_msgData_6031_, v_severity_boxed_6039_, v_isSilent_boxed_6040_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_);
lean_dec(v___y_6037_);
lean_dec(v___y_6035_);
lean_dec_ref(v___y_6034_);
return v_res_6041_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1(lean_object* v_msgData_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_){
_start:
{
uint8_t v___x_6048_; uint8_t v___x_6049_; lean_object* v___x_6050_; 
v___x_6048_ = 0;
v___x_6049_ = 0;
v___x_6050_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1(v_msgData_6042_, v___x_6048_, v___x_6049_, v___y_6043_, v___y_6044_, v___y_6045_, v___y_6046_);
return v___x_6050_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1___boxed(lean_object* v_msgData_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_){
_start:
{
lean_object* v_res_6057_; 
v_res_6057_ = l_Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1(v_msgData_6051_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_);
lean_dec(v___y_6055_);
lean_dec(v___y_6053_);
lean_dec_ref(v___y_6052_);
return v_res_6057_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6059_; lean_object* v___x_6060_; 
v___x_6059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__0));
v___x_6060_ = l_Lean_stringToMessageData(v___x_6059_);
return v___x_6060_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_6061_; lean_object* v___x_6062_; 
v___x_6061_ = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__23));
v___x_6062_ = l_Lean_stringToMessageData(v___x_6061_);
return v___x_6062_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_6066_; lean_object* v___x_6067_; 
v___x_6066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__4));
v___x_6067_ = l_Lean_MessageData_ofFormat(v___x_6066_);
return v___x_6067_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_6069_; lean_object* v___x_6070_; 
v___x_6069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__6));
v___x_6070_ = l_Lean_stringToMessageData(v___x_6069_);
return v___x_6070_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__9(void){
_start:
{
lean_object* v___x_6072_; lean_object* v___x_6073_; 
v___x_6072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__8));
v___x_6073_ = l_Lean_stringToMessageData(v___x_6072_);
return v___x_6073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg(uint8_t v___y_6074_, lean_object* v_as_6075_, size_t v_sz_6076_, size_t v_i_6077_, lean_object* v_b_6078_){
_start:
{
lean_object* v_a_6081_; uint8_t v___x_6085_; 
v___x_6085_ = lean_usize_dec_lt(v_i_6077_, v_sz_6076_);
if (v___x_6085_ == 0)
{
lean_object* v___x_6086_; 
v___x_6086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6086_, 0, v_b_6078_);
return v___x_6086_;
}
else
{
lean_object* v_a_6087_; lean_object* v_msg_6089_; lean_object* v_name_6098_; double v_score_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; uint8_t v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; 
v_a_6087_ = lean_array_uget_borrowed(v_as_6075_, v_i_6077_);
v_name_6098_ = lean_ctor_get(v_a_6087_, 0);
v_score_6099_ = lean_ctor_get_float(v_a_6087_, sizeof(void*)*2);
v___x_6100_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0);
v___x_6101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6101_, 0, v_b_6078_);
lean_ctor_set(v___x_6101_, 1, v___x_6100_);
v___x_6102_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__5);
v___x_6103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6101_);
lean_ctor_set(v___x_6103_, 1, v___x_6102_);
v___x_6104_ = 0;
lean_inc(v_name_6098_);
v___x_6105_ = l_Lean_MessageData_ofConstName(v_name_6098_, v___x_6104_);
v___x_6106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6106_, 0, v___x_6103_);
lean_ctor_set(v___x_6106_, 1, v___x_6105_);
if (v___y_6074_ == 0)
{
lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; 
v___x_6107_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__7);
v___x_6108_ = lean_float_to_string(v_score_6099_);
v___x_6109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6108_);
v___x_6110_ = l_Lean_MessageData_ofFormat(v___x_6109_);
v___x_6111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6111_, 0, v___x_6107_);
lean_ctor_set(v___x_6111_, 1, v___x_6110_);
v___x_6112_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__9);
v___x_6113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6111_);
lean_ctor_set(v___x_6113_, 1, v___x_6112_);
v___x_6114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6106_);
lean_ctor_set(v___x_6114_, 1, v___x_6113_);
v_msg_6089_ = v___x_6114_;
goto v___jp_6088_;
}
else
{
v_msg_6089_ = v___x_6106_;
goto v___jp_6088_;
}
v___jp_6088_:
{
lean_object* v_flag_6090_; 
v_flag_6090_ = lean_ctor_get(v_a_6087_, 1);
if (lean_obj_tag(v_flag_6090_) == 1)
{
lean_object* v_val_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; 
v_val_6091_ = lean_ctor_get(v_flag_6090_, 0);
v___x_6092_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__1);
lean_inc(v_val_6091_);
v___x_6093_ = l_Lean_stringToMessageData(v_val_6091_);
v___x_6094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6092_);
lean_ctor_set(v___x_6094_, 1, v___x_6093_);
v___x_6095_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__2);
v___x_6096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6094_);
lean_ctor_set(v___x_6096_, 1, v___x_6095_);
v___x_6097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6097_, 0, v_msg_6089_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v_a_6081_ = v___x_6097_;
goto v___jp_6080_;
}
else
{
v_a_6081_ = v_msg_6089_;
goto v___jp_6080_;
}
}
}
v___jp_6080_:
{
size_t v___x_6082_; size_t v___x_6083_; 
v___x_6082_ = ((size_t)1ULL);
v___x_6083_ = lean_usize_add(v_i_6077_, v___x_6082_);
v_i_6077_ = v___x_6083_;
v_b_6078_ = v_a_6081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___boxed(lean_object* v___y_6115_, lean_object* v_as_6116_, lean_object* v_sz_6117_, lean_object* v_i_6118_, lean_object* v_b_6119_, lean_object* v___y_6120_){
_start:
{
uint8_t v___y_5324__boxed_6121_; size_t v_sz_boxed_6122_; size_t v_i_boxed_6123_; lean_object* v_res_6124_; 
v___y_5324__boxed_6121_ = lean_unbox(v___y_6115_);
v_sz_boxed_6122_ = lean_unbox_usize(v_sz_6117_);
lean_dec(v_sz_6117_);
v_i_boxed_6123_ = lean_unbox_usize(v_i_6118_);
lean_dec(v_i_6118_);
v_res_6124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg(v___y_5324__boxed_6121_, v_as_6116_, v_sz_boxed_6122_, v_i_boxed_6123_, v_b_6119_);
lean_dec_ref(v_as_6116_);
return v_res_6124_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_6128_; lean_object* v___x_6129_; 
v___x_6128_ = ((lean_object*)(l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__1));
v___x_6129_ = l_Lean_MessageData_ofFormat(v___x_6128_);
return v___x_6129_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1(lean_object* v___f_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_){
_start:
{
lean_object* v___x_6140_; 
v___x_6140_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6132_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_);
if (lean_obj_tag(v___x_6140_) == 0)
{
lean_object* v_a_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; 
v_a_6141_ = lean_ctor_get(v___x_6140_, 0);
lean_inc(v_a_6141_);
lean_dec_ref(v___x_6140_);
v___x_6142_ = lean_unsigned_to_nat(100u);
v___x_6143_ = lean_box(0);
v___x_6144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6142_);
lean_ctor_set(v___x_6144_, 1, v___x_6143_);
lean_ctor_set(v___x_6144_, 2, v___f_6130_);
lean_ctor_set(v___x_6144_, 3, v___x_6143_);
lean_inc(v___y_6138_);
lean_inc_ref(v___y_6137_);
lean_inc(v___y_6136_);
lean_inc_ref(v___y_6135_);
lean_inc(v_a_6141_);
v___x_6145_ = l_Lean_LibrarySuggestions_select(v_a_6141_, v___x_6144_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_);
if (lean_obj_tag(v___x_6145_) == 0)
{
lean_object* v_a_6146_; lean_object* v___x_6147_; uint8_t v___y_6149_; lean_object* v___x_6166_; lean_object* v___x_6167_; uint8_t v___x_6168_; 
v_a_6146_ = lean_ctor_get(v___x_6145_, 0);
lean_inc(v_a_6146_);
lean_dec_ref(v___x_6145_);
v___x_6147_ = lean_obj_once(&l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__2, &l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__2_once, _init_l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__2);
v___x_6166_ = lean_unsigned_to_nat(0u);
v___x_6167_ = lean_array_get_size(v_a_6146_);
v___x_6168_ = lean_nat_dec_lt(v___x_6166_, v___x_6167_);
if (v___x_6168_ == 0)
{
uint8_t v___x_6169_; 
v___x_6169_ = 1;
v___y_6149_ = v___x_6169_;
goto v___jp_6148_;
}
else
{
if (v___x_6168_ == 0)
{
v___y_6149_ = v___x_6168_;
goto v___jp_6148_;
}
else
{
size_t v___x_6170_; size_t v___x_6171_; uint8_t v___x_6172_; 
v___x_6170_ = ((size_t)0ULL);
v___x_6171_ = lean_usize_of_nat(v___x_6167_);
v___x_6172_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2(v_a_6146_, v___x_6170_, v___x_6171_);
if (v___x_6172_ == 0)
{
v___y_6149_ = v___x_6168_;
goto v___jp_6148_;
}
else
{
uint8_t v___x_6173_; 
v___x_6173_ = 0;
v___y_6149_ = v___x_6173_;
goto v___jp_6148_;
}
}
}
v___jp_6148_:
{
size_t v_sz_6150_; size_t v___x_6151_; lean_object* v___x_6152_; 
v_sz_6150_ = lean_array_size(v_a_6146_);
v___x_6151_ = ((size_t)0ULL);
v___x_6152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg(v___y_6149_, v_a_6146_, v_sz_6150_, v___x_6151_, v___x_6147_);
lean_dec(v_a_6146_);
if (lean_obj_tag(v___x_6152_) == 0)
{
lean_object* v_a_6153_; lean_object* v___x_6154_; 
v_a_6153_ = lean_ctor_get(v___x_6152_, 0);
lean_inc(v_a_6153_);
lean_dec_ref(v___x_6152_);
lean_inc_ref(v___y_6137_);
v___x_6154_ = l_Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1(v_a_6153_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_);
if (lean_obj_tag(v___x_6154_) == 0)
{
lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; 
lean_dec_ref(v___x_6154_);
v___x_6155_ = lean_box(0);
v___x_6156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6156_, 0, v_a_6141_);
lean_ctor_set(v___x_6156_, 1, v___x_6155_);
v___x_6157_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_6156_, v___y_6132_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_);
lean_dec(v___y_6138_);
lean_dec_ref(v___y_6137_);
lean_dec(v___y_6136_);
lean_dec_ref(v___y_6135_);
return v___x_6157_;
}
else
{
lean_dec(v_a_6141_);
lean_dec(v___y_6138_);
lean_dec_ref(v___y_6137_);
lean_dec(v___y_6136_);
lean_dec_ref(v___y_6135_);
return v___x_6154_;
}
}
else
{
lean_object* v_a_6158_; lean_object* v___x_6160_; uint8_t v_isShared_6161_; uint8_t v_isSharedCheck_6165_; 
lean_dec(v_a_6141_);
lean_dec(v___y_6138_);
lean_dec_ref(v___y_6137_);
lean_dec(v___y_6136_);
lean_dec_ref(v___y_6135_);
v_a_6158_ = lean_ctor_get(v___x_6152_, 0);
v_isSharedCheck_6165_ = !lean_is_exclusive(v___x_6152_);
if (v_isSharedCheck_6165_ == 0)
{
v___x_6160_ = v___x_6152_;
v_isShared_6161_ = v_isSharedCheck_6165_;
goto v_resetjp_6159_;
}
else
{
lean_inc(v_a_6158_);
lean_dec(v___x_6152_);
v___x_6160_ = lean_box(0);
v_isShared_6161_ = v_isSharedCheck_6165_;
goto v_resetjp_6159_;
}
v_resetjp_6159_:
{
lean_object* v___x_6163_; 
if (v_isShared_6161_ == 0)
{
v___x_6163_ = v___x_6160_;
goto v_reusejp_6162_;
}
else
{
lean_object* v_reuseFailAlloc_6164_; 
v_reuseFailAlloc_6164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6164_, 0, v_a_6158_);
v___x_6163_ = v_reuseFailAlloc_6164_;
goto v_reusejp_6162_;
}
v_reusejp_6162_:
{
return v___x_6163_;
}
}
}
}
}
else
{
lean_object* v_a_6174_; lean_object* v___x_6176_; uint8_t v_isShared_6177_; uint8_t v_isSharedCheck_6181_; 
lean_dec(v_a_6141_);
lean_dec(v___y_6138_);
lean_dec_ref(v___y_6137_);
lean_dec(v___y_6136_);
lean_dec_ref(v___y_6135_);
v_a_6174_ = lean_ctor_get(v___x_6145_, 0);
v_isSharedCheck_6181_ = !lean_is_exclusive(v___x_6145_);
if (v_isSharedCheck_6181_ == 0)
{
v___x_6176_ = v___x_6145_;
v_isShared_6177_ = v_isSharedCheck_6181_;
goto v_resetjp_6175_;
}
else
{
lean_inc(v_a_6174_);
lean_dec(v___x_6145_);
v___x_6176_ = lean_box(0);
v_isShared_6177_ = v_isSharedCheck_6181_;
goto v_resetjp_6175_;
}
v_resetjp_6175_:
{
lean_object* v___x_6179_; 
if (v_isShared_6177_ == 0)
{
v___x_6179_ = v___x_6176_;
goto v_reusejp_6178_;
}
else
{
lean_object* v_reuseFailAlloc_6180_; 
v_reuseFailAlloc_6180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6180_, 0, v_a_6174_);
v___x_6179_ = v_reuseFailAlloc_6180_;
goto v_reusejp_6178_;
}
v_reusejp_6178_:
{
return v___x_6179_;
}
}
}
}
else
{
lean_object* v_a_6182_; lean_object* v___x_6184_; uint8_t v_isShared_6185_; uint8_t v_isSharedCheck_6189_; 
lean_dec(v___y_6138_);
lean_dec_ref(v___y_6137_);
lean_dec(v___y_6136_);
lean_dec_ref(v___y_6135_);
lean_dec_ref(v___f_6130_);
v_a_6182_ = lean_ctor_get(v___x_6140_, 0);
v_isSharedCheck_6189_ = !lean_is_exclusive(v___x_6140_);
if (v_isSharedCheck_6189_ == 0)
{
v___x_6184_ = v___x_6140_;
v_isShared_6185_ = v_isSharedCheck_6189_;
goto v_resetjp_6183_;
}
else
{
lean_inc(v_a_6182_);
lean_dec(v___x_6140_);
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
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___boxed(lean_object* v___f_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_){
_start:
{
lean_object* v_res_6200_; 
v_res_6200_ = l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1(v___f_6190_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_, v___y_6198_);
lean_dec(v___y_6194_);
lean_dec_ref(v___y_6193_);
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
return v_res_6200_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg(lean_object* v_a_6203_, lean_object* v_a_6204_, lean_object* v_a_6205_, lean_object* v_a_6206_, lean_object* v_a_6207_, lean_object* v_a_6208_, lean_object* v_a_6209_, lean_object* v_a_6210_){
_start:
{
lean_object* v___f_6212_; lean_object* v___x_6213_; 
v___f_6212_ = ((lean_object*)(l_Lean_LibrarySuggestions_evalSuggestions___redArg___closed__0));
v___x_6213_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_6212_, v_a_6203_, v_a_6204_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_);
return v___x_6213_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___boxed(lean_object* v_a_6214_, lean_object* v_a_6215_, lean_object* v_a_6216_, lean_object* v_a_6217_, lean_object* v_a_6218_, lean_object* v_a_6219_, lean_object* v_a_6220_, lean_object* v_a_6221_, lean_object* v_a_6222_){
_start:
{
lean_object* v_res_6223_; 
v_res_6223_ = l_Lean_LibrarySuggestions_evalSuggestions___redArg(v_a_6214_, v_a_6215_, v_a_6216_, v_a_6217_, v_a_6218_, v_a_6219_, v_a_6220_, v_a_6221_);
return v_res_6223_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions(lean_object* v_x_6224_, lean_object* v_a_6225_, lean_object* v_a_6226_, lean_object* v_a_6227_, lean_object* v_a_6228_, lean_object* v_a_6229_, lean_object* v_a_6230_, lean_object* v_a_6231_, lean_object* v_a_6232_){
_start:
{
lean_object* v___x_6234_; 
v___x_6234_ = l_Lean_LibrarySuggestions_evalSuggestions___redArg(v_a_6225_, v_a_6226_, v_a_6227_, v_a_6228_, v_a_6229_, v_a_6230_, v_a_6231_, v_a_6232_);
return v___x_6234_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___boxed(lean_object* v_x_6235_, lean_object* v_a_6236_, lean_object* v_a_6237_, lean_object* v_a_6238_, lean_object* v_a_6239_, lean_object* v_a_6240_, lean_object* v_a_6241_, lean_object* v_a_6242_, lean_object* v_a_6243_, lean_object* v_a_6244_){
_start:
{
lean_object* v_res_6245_; 
v_res_6245_ = l_Lean_LibrarySuggestions_evalSuggestions(v_x_6235_, v_a_6236_, v_a_6237_, v_a_6238_, v_a_6239_, v_a_6240_, v_a_6241_, v_a_6242_, v_a_6243_);
lean_dec(v_x_6235_);
return v_res_6245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0(uint8_t v___y_6246_, lean_object* v_as_6247_, size_t v_sz_6248_, size_t v_i_6249_, lean_object* v_b_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_){
_start:
{
lean_object* v___x_6256_; 
v___x_6256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg(v___y_6246_, v_as_6247_, v_sz_6248_, v_i_6249_, v_b_6250_);
return v___x_6256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___boxed(lean_object* v___y_6257_, lean_object* v_as_6258_, lean_object* v_sz_6259_, lean_object* v_i_6260_, lean_object* v_b_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_){
_start:
{
uint8_t v___y_5621__boxed_6267_; size_t v_sz_boxed_6268_; size_t v_i_boxed_6269_; lean_object* v_res_6270_; 
v___y_5621__boxed_6267_ = lean_unbox(v___y_6257_);
v_sz_boxed_6268_ = lean_unbox_usize(v_sz_6259_);
lean_dec(v_sz_6259_);
v_i_boxed_6269_ = lean_unbox_usize(v_i_6260_);
lean_dec(v_i_6260_);
v_res_6270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0(v___y_5621__boxed_6267_, v_as_6258_, v_sz_boxed_6268_, v_i_boxed_6269_, v_b_6261_, v___y_6262_, v___y_6263_, v___y_6264_, v___y_6265_);
lean_dec(v___y_6265_);
lean_dec_ref(v___y_6264_);
lean_dec(v___y_6263_);
lean_dec_ref(v___y_6262_);
lean_dec_ref(v_as_6258_);
return v_res_6270_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1(){
_start:
{
lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; 
v___x_6283_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6284_ = ((lean_object*)(l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1));
v___x_6285_ = ((lean_object*)(l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3));
v___x_6286_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_evalSuggestions___boxed), 10, 0);
v___x_6287_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6283_, v___x_6284_, v___x_6285_, v___x_6286_);
return v___x_6287_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___boxed(lean_object* v_a_6288_){
_start:
{
lean_object* v_res_6289_; 
v_res_6289_ = l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1();
return v_res_6289_;
}
}
lean_object* runtime_initialize_Lean_Meta_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Random(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Annotated(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Random(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_LibrarySuggestions_Selector_intersperse___closed__1___boxed__const__1 = _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_LibrarySuggestions_Selector_intersperse___closed__1___boxed__const__1);
res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_LibrarySuggestions_moduleDenyListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_LibrarySuggestions_moduleDenyListExt);
lean_dec_ref(res);
res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_LibrarySuggestions_nameDenyListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_LibrarySuggestions_nameDenyListExt);
lean_dec_ref(res);
res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_LibrarySuggestions_typePrefixDenyListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_LibrarySuggestions_typePrefixDenyListExt);
lean_dec_ref(res);
res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_LibrarySuggestions_librarySuggestionsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_LibrarySuggestions_librarySuggestionsExt);
lean_dec_ref(res);
res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_LibrarySuggestions_librarySuggestionsAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_LibrarySuggestions_librarySuggestionsAttr);
lean_dec_ref(res);
res = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* initialize_Init_Data_Random(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Annotated(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Random(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_LibrarySuggestions_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
