// Lean compiler output
// Module: Lean.Elab.ErrorExplanation
// Imports: public import Lean.Widget.UserWidget meta import Lean.Widget.UserWidget
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_string_intercalate(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
extern lean_object* l_Lean_errorExplanationExt;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_throwAbortTerm___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_errorDescriptionWidget;
lean_object* l_Lean_Widget_addBuiltinModule(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "errorDescriptionWidget"};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(97, 213, 240, 52, 84, 173, 13, 164)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "throwNamedErrorMacro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(147, 71, 28, 75, 97, 117, 128, 98)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "throwNamedErrorAtMacro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4_value),LEAN_SCALAR_PTR_LITERAL(123, 65, 2, 235, 170, 76, 164, 46)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "logNamedErrorMacro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6_value),LEAN_SCALAR_PTR_LITERAL(73, 64, 162, 114, 236, 8, 247, 133)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "logNamedErrorAtMacro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8_value),LEAN_SCALAR_PTR_LITERAL(78, 239, 95, 34, 175, 88, 94, 179)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "logNamedWarningMacro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10_value),LEAN_SCALAR_PTR_LITERAL(2, 91, 200, 35, 216, 48, 104, 184)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "logNamedWarningAtMacro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12_value),LEAN_SCALAR_PTR_LITERAL(15, 172, 147, 28, 87, 118, 172, 232)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.logNamedWarningAt"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "logNamedWarningAt"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20_value),LEAN_SCALAR_PTR_LITERAL(165, 244, 38, 255, 142, 163, 212, 242)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termM!_"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_value),LEAN_SCALAR_PTR_LITERAL(241, 254, 249, 246, 41, 222, 210, 184)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "m!"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.logNamedWarning"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "logNamedWarning"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35_value),LEAN_SCALAR_PTR_LITERAL(34, 53, 86, 106, 208, 200, 15, 240)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.logNamedErrorAt"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "logNamedErrorAt"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41_value),LEAN_SCALAR_PTR_LITERAL(215, 212, 218, 121, 130, 143, 154, 83)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.logNamedError"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "logNamedError"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47_value),LEAN_SCALAR_PTR_LITERAL(193, 48, 226, 102, 122, 31, 140, 200)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.throwNamedErrorAt"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "throwNamedErrorAt"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53_value),LEAN_SCALAR_PTR_LITERAL(151, 5, 168, 142, 232, 160, 229, 118)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.throwNamedError"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60;
static const lean_string_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "throwNamedError"};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61_value),LEAN_SCALAR_PTR_LITERAL(55, 87, 79, 197, 235, 27, 154, 123)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Exception"};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 208, 119, 110, 215, 6, 136, 235)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5_value;
static const lean_string_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Log"};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6_value),LEAN_SCALAR_PTR_LITERAL(151, 176, 165, 28, 129, 118, 207, 221)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3_value),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20_value)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21_value;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "The error name `"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "` was removed in Lean version "};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = " and should not be used."};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "There is no explanation registered with the name `"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "`. Register an explanation for this error in the `Lean.ErrorExplanation` module."};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "The constant `"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` has not been imported"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Add `import "};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` to this file's header to use this macro"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ErrorExplanation"};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabCheckedNamedError"};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 18, 113, 52, 22, 68, 187, 184)}};
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(29, 92, 138, 205, 69, 125, 159, 73)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11;
static lean_once_cell_t l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "registerErrorExplanationStx"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1_value),LEAN_SCALAR_PTR_LITERAL(150, 121, 11, 220, 201, 134, 39, 253)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "Cannot add explanation: An error explanation already exists for `"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Invalid name `"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "`: Error explanation names must have two components"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 149, .m_capacity = 149, .m_length = 148, .m_data = "The first component of an error explanation name identifies the package from which the error originates, and the second identifies the error itself."};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 132, .m_capacity = 132, .m_length = 131, .m_data = "`: Error explanations cannot have inaccessible names. This error often occurs when an error explanation is generated using a macro."};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Metadata"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15_value;
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 124, 72, 60, 38, 86, 32, 253)}};
static const lean_ctor_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15_value),LEAN_SCALAR_PTR_LITERAL(228, 194, 107, 149, 38, 116, 86, 230)}};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid name for error explanation: `"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19;
static const lean_string_object l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "To use this command, add `import Lean.ErrorExplanation` to the header of this file"};
static const lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20 = (const lean_object*)&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20_value;
static lean_once_cell_t l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "elabRegisterErrorExplanation"};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 18, 113, 52, 22, 68, 187, 184)}};
static const lean_ctor_object l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 148, 59, 123, 129, 88, 83, 38)}};
static const lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1(){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2));
v___x_8_ = l_Lean_errorDescriptionWidget;
v___x_9_ = l_Lean_Widget_addBuiltinModule(v___x_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___boxed(lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1();
return v_res_11_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18));
v___x_61_ = l_String_toRawSubstring_x27(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33));
v___x_90_ = l_String_toRawSubstring_x27(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39));
v___x_103_ = l_String_toRawSubstring_x27(v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45));
v___x_116_ = l_String_toRawSubstring_x27(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51));
v___x_129_ = l_String_toRawSubstring_x27(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59));
v___x_145_ = l_String_toRawSubstring_x27(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(lean_object* v_x_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3));
lean_inc(v_x_156_);
v___x_160_ = l_Lean_Syntax_isOfKind(v_x_156_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
lean_inc(v_x_156_);
v___x_162_ = l_Lean_Syntax_isOfKind(v_x_156_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7));
lean_inc(v_x_156_);
v___x_164_ = l_Lean_Syntax_isOfKind(v_x_156_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
lean_inc(v_x_156_);
v___x_166_ = l_Lean_Syntax_isOfKind(v_x_156_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11));
lean_inc(v_x_156_);
v___x_168_ = l_Lean_Syntax_isOfKind(v_x_156_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
lean_inc(v_x_156_);
v___x_170_ = l_Lean_Syntax_isOfKind(v_x_156_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; 
lean_dec(v_x_156_);
v___x_171_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_unsigned_to_nat(3u);
v___x_174_ = l_Lean_Syntax_getArg(v_x_156_, v___x_173_);
v___x_175_ = l_Lean_Syntax_matchesNull(v___x_174_, v___x_172_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
lean_dec(v_x_156_);
v___x_176_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_id_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = l_Lean_Syntax_getArg(v_x_156_, v___x_177_);
v___x_179_ = lean_unsigned_to_nat(2u);
v_id_180_ = l_Lean_Syntax_getArg(v_x_156_, v___x_179_);
v___x_181_ = lean_unsigned_to_nat(4u);
v___x_182_ = l_Lean_Syntax_getArg(v_x_156_, v___x_181_);
lean_dec(v_x_156_);
v___x_183_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
lean_inc(v___x_182_);
v___x_184_ = l_Lean_Syntax_isOfKind(v___x_182_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v_quotContext_185_; lean_object* v_currMacroScope_186_; lean_object* v_ref_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___y_198_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_quotContext_185_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_186_ = lean_ctor_get(v_a_157_, 2);
v_ref_187_ = lean_ctor_get(v_a_157_, 5);
v___x_188_ = l_Lean_SourceInfo_fromRef(v_ref_187_, v___x_168_);
v___x_189_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_190_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19);
v___x_191_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21));
lean_inc(v_currMacroScope_186_);
lean_inc(v_quotContext_185_);
v___x_192_ = l_Lean_addMacroScope(v_quotContext_185_, v___x_191_, v_currMacroScope_186_);
v___x_193_ = lean_box(0);
v___x_194_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23));
lean_inc(v___x_188_);
v___x_195_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_195_, 0, v___x_188_);
lean_ctor_set(v___x_195_, 1, v___x_190_);
lean_ctor_set(v___x_195_, 2, v___x_192_);
lean_ctor_set(v___x_195_, 3, v___x_194_);
v___x_196_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_202_ = l_Lean_TSyntax_getId(v_id_180_);
lean_dec(v_id_180_);
lean_inc(v___x_202_);
v___x_203_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_193_, v___x_202_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_quoteNameMk(v___x_202_);
v___y_198_ = v___x_204_;
goto v___jp_197_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v___x_202_);
v_val_205_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v___x_203_, 1);
v___x_206_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_207_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_208_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_209_ = lean_string_intercalate(v___x_208_, v_val_205_);
v___x_210_ = lean_string_append(v___x_207_, v___x_209_);
lean_dec_ref(v___x_209_);
v___x_211_ = lean_box(2);
v___x_212_ = l_Lean_Syntax_mkNameLit(v___x_210_, v___x_211_);
v___x_213_ = lean_mk_empty_array_with_capacity(v___x_177_);
v___x_214_ = lean_array_push(v___x_213_, v___x_212_);
v___x_215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_215_, 0, v___x_211_);
lean_ctor_set(v___x_215_, 1, v___x_206_);
lean_ctor_set(v___x_215_, 2, v___x_214_);
v___y_198_ = v___x_215_;
goto v___jp_197_;
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_inc(v___x_188_);
v___x_199_ = l_Lean_Syntax_node3(v___x_188_, v___x_196_, v___x_178_, v___y_198_, v___x_182_);
v___x_200_ = l_Lean_Syntax_node2(v___x_188_, v___x_189_, v___x_195_, v___x_199_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v_a_158_);
return v___x_201_;
}
}
else
{
lean_object* v_quotContext_216_; lean_object* v_currMacroScope_217_; lean_object* v_ref_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___y_229_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_quotContext_216_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_217_ = lean_ctor_get(v_a_157_, 2);
v_ref_218_ = lean_ctor_get(v_a_157_, 5);
v___x_219_ = l_Lean_SourceInfo_fromRef(v_ref_218_, v___x_168_);
v___x_220_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_221_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19);
v___x_222_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21));
lean_inc(v_currMacroScope_217_);
lean_inc(v_quotContext_216_);
v___x_223_ = l_Lean_addMacroScope(v_quotContext_216_, v___x_222_, v_currMacroScope_217_);
v___x_224_ = lean_box(0);
v___x_225_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23));
lean_inc(v___x_219_);
v___x_226_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_226_, 0, v___x_219_);
lean_ctor_set(v___x_226_, 1, v___x_221_);
lean_ctor_set(v___x_226_, 2, v___x_223_);
lean_ctor_set(v___x_226_, 3, v___x_225_);
v___x_227_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_237_ = l_Lean_TSyntax_getId(v_id_180_);
lean_dec(v_id_180_);
lean_inc(v___x_237_);
v___x_238_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_224_, v___x_237_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_quoteNameMk(v___x_237_);
v___y_229_ = v___x_239_;
goto v___jp_228_;
}
else
{
lean_object* v_val_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v___x_237_);
v_val_240_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_val_240_);
lean_dec_ref_known(v___x_238_, 1);
v___x_241_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_242_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_243_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_244_ = lean_string_intercalate(v___x_243_, v_val_240_);
v___x_245_ = lean_string_append(v___x_242_, v___x_244_);
lean_dec_ref(v___x_244_);
v___x_246_ = lean_box(2);
v___x_247_ = l_Lean_Syntax_mkNameLit(v___x_245_, v___x_246_);
v___x_248_ = lean_mk_empty_array_with_capacity(v___x_177_);
v___x_249_ = lean_array_push(v___x_248_, v___x_247_);
v___x_250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_250_, 0, v___x_246_);
lean_ctor_set(v___x_250_, 1, v___x_241_);
lean_ctor_set(v___x_250_, 2, v___x_249_);
v___y_229_ = v___x_250_;
goto v___jp_228_;
}
v___jp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_230_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31));
v___x_231_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
lean_inc_n(v___x_219_, 3);
v___x_232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_219_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = l_Lean_Syntax_node2(v___x_219_, v___x_230_, v___x_232_, v___x_182_);
v___x_234_ = l_Lean_Syntax_node3(v___x_219_, v___x_227_, v___x_178_, v___y_229_, v___x_233_);
v___x_235_ = l_Lean_Syntax_node2(v___x_219_, v___x_220_, v___x_226_, v___x_234_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v_a_158_);
return v___x_236_;
}
}
}
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_unsigned_to_nat(2u);
v___x_253_ = l_Lean_Syntax_getArg(v_x_156_, v___x_252_);
v___x_254_ = l_Lean_Syntax_matchesNull(v___x_253_, v___x_251_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v_x_156_);
v___x_255_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v_id_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_256_ = lean_unsigned_to_nat(1u);
v_id_257_ = l_Lean_Syntax_getArg(v_x_156_, v___x_256_);
v___x_258_ = lean_unsigned_to_nat(3u);
v___x_259_ = l_Lean_Syntax_getArg(v_x_156_, v___x_258_);
lean_dec(v_x_156_);
v___x_260_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
lean_inc(v___x_259_);
v___x_261_ = l_Lean_Syntax_isOfKind(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v_quotContext_262_; lean_object* v_currMacroScope_263_; lean_object* v_ref_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___y_275_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_quotContext_262_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_263_ = lean_ctor_get(v_a_157_, 2);
v_ref_264_ = lean_ctor_get(v_a_157_, 5);
v___x_265_ = l_Lean_SourceInfo_fromRef(v_ref_264_, v___x_166_);
v___x_266_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_267_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34);
v___x_268_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36));
lean_inc(v_currMacroScope_263_);
lean_inc(v_quotContext_262_);
v___x_269_ = l_Lean_addMacroScope(v_quotContext_262_, v___x_268_, v_currMacroScope_263_);
v___x_270_ = lean_box(0);
v___x_271_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38));
lean_inc(v___x_265_);
v___x_272_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_272_, 0, v___x_265_);
lean_ctor_set(v___x_272_, 1, v___x_267_);
lean_ctor_set(v___x_272_, 2, v___x_269_);
lean_ctor_set(v___x_272_, 3, v___x_271_);
v___x_273_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_279_ = l_Lean_TSyntax_getId(v_id_257_);
lean_dec(v_id_257_);
lean_inc(v___x_279_);
v___x_280_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_270_, v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_quoteNameMk(v___x_279_);
v___y_275_ = v___x_281_;
goto v___jp_274_;
}
else
{
lean_object* v_val_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec(v___x_279_);
v_val_282_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_282_);
lean_dec_ref_known(v___x_280_, 1);
v___x_283_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_284_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_285_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_286_ = lean_string_intercalate(v___x_285_, v_val_282_);
v___x_287_ = lean_string_append(v___x_284_, v___x_286_);
lean_dec_ref(v___x_286_);
v___x_288_ = lean_box(2);
v___x_289_ = l_Lean_Syntax_mkNameLit(v___x_287_, v___x_288_);
v___x_290_ = lean_mk_empty_array_with_capacity(v___x_256_);
v___x_291_ = lean_array_push(v___x_290_, v___x_289_);
v___x_292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_292_, 0, v___x_288_);
lean_ctor_set(v___x_292_, 1, v___x_283_);
lean_ctor_set(v___x_292_, 2, v___x_291_);
v___y_275_ = v___x_292_;
goto v___jp_274_;
}
v___jp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
lean_inc(v___x_265_);
v___x_276_ = l_Lean_Syntax_node2(v___x_265_, v___x_273_, v___y_275_, v___x_259_);
v___x_277_ = l_Lean_Syntax_node2(v___x_265_, v___x_266_, v___x_272_, v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v_a_158_);
return v___x_278_;
}
}
else
{
lean_object* v_quotContext_293_; lean_object* v_currMacroScope_294_; lean_object* v_ref_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___y_306_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_quotContext_293_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_294_ = lean_ctor_get(v_a_157_, 2);
v_ref_295_ = lean_ctor_get(v_a_157_, 5);
v___x_296_ = l_Lean_SourceInfo_fromRef(v_ref_295_, v___x_166_);
v___x_297_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_298_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34);
v___x_299_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36));
lean_inc(v_currMacroScope_294_);
lean_inc(v_quotContext_293_);
v___x_300_ = l_Lean_addMacroScope(v_quotContext_293_, v___x_299_, v_currMacroScope_294_);
v___x_301_ = lean_box(0);
v___x_302_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38));
lean_inc(v___x_296_);
v___x_303_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_303_, 0, v___x_296_);
lean_ctor_set(v___x_303_, 1, v___x_298_);
lean_ctor_set(v___x_303_, 2, v___x_300_);
lean_ctor_set(v___x_303_, 3, v___x_302_);
v___x_304_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_314_ = l_Lean_TSyntax_getId(v_id_257_);
lean_dec(v_id_257_);
lean_inc(v___x_314_);
v___x_315_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_301_, v___x_314_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_quoteNameMk(v___x_314_);
v___y_306_ = v___x_316_;
goto v___jp_305_;
}
else
{
lean_object* v_val_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec(v___x_314_);
v_val_317_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_val_317_);
lean_dec_ref_known(v___x_315_, 1);
v___x_318_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_319_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_320_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_321_ = lean_string_intercalate(v___x_320_, v_val_317_);
v___x_322_ = lean_string_append(v___x_319_, v___x_321_);
lean_dec_ref(v___x_321_);
v___x_323_ = lean_box(2);
v___x_324_ = l_Lean_Syntax_mkNameLit(v___x_322_, v___x_323_);
v___x_325_ = lean_mk_empty_array_with_capacity(v___x_256_);
v___x_326_ = lean_array_push(v___x_325_, v___x_324_);
v___x_327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_327_, 0, v___x_323_);
lean_ctor_set(v___x_327_, 1, v___x_318_);
lean_ctor_set(v___x_327_, 2, v___x_326_);
v___y_306_ = v___x_327_;
goto v___jp_305_;
}
v___jp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_307_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31));
v___x_308_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
lean_inc_n(v___x_296_, 3);
v___x_309_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_296_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = l_Lean_Syntax_node2(v___x_296_, v___x_307_, v___x_309_, v___x_259_);
v___x_311_ = l_Lean_Syntax_node2(v___x_296_, v___x_304_, v___y_306_, v___x_310_);
v___x_312_ = l_Lean_Syntax_node2(v___x_296_, v___x_297_, v___x_303_, v___x_311_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v_a_158_);
return v___x_313_;
}
}
}
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_unsigned_to_nat(3u);
v___x_330_ = l_Lean_Syntax_getArg(v_x_156_, v___x_329_);
v___x_331_ = l_Lean_Syntax_matchesNull(v___x_330_, v___x_328_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
lean_dec(v_x_156_);
v___x_332_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v_id_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = l_Lean_Syntax_getArg(v_x_156_, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(2u);
v_id_336_ = l_Lean_Syntax_getArg(v_x_156_, v___x_335_);
v___x_337_ = lean_unsigned_to_nat(4u);
v___x_338_ = l_Lean_Syntax_getArg(v_x_156_, v___x_337_);
lean_dec(v_x_156_);
v___x_339_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
lean_inc(v___x_338_);
v___x_340_ = l_Lean_Syntax_isOfKind(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v_quotContext_341_; lean_object* v_currMacroScope_342_; lean_object* v_ref_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___y_354_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_quotContext_341_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_342_ = lean_ctor_get(v_a_157_, 2);
v_ref_343_ = lean_ctor_get(v_a_157_, 5);
v___x_344_ = l_Lean_SourceInfo_fromRef(v_ref_343_, v___x_164_);
v___x_345_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_346_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40);
v___x_347_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42));
lean_inc(v_currMacroScope_342_);
lean_inc(v_quotContext_341_);
v___x_348_ = l_Lean_addMacroScope(v_quotContext_341_, v___x_347_, v_currMacroScope_342_);
v___x_349_ = lean_box(0);
v___x_350_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44));
lean_inc(v___x_344_);
v___x_351_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_351_, 0, v___x_344_);
lean_ctor_set(v___x_351_, 1, v___x_346_);
lean_ctor_set(v___x_351_, 2, v___x_348_);
lean_ctor_set(v___x_351_, 3, v___x_350_);
v___x_352_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_358_ = l_Lean_TSyntax_getId(v_id_336_);
lean_dec(v_id_336_);
lean_inc(v___x_358_);
v___x_359_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_349_, v___x_358_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_quoteNameMk(v___x_358_);
v___y_354_ = v___x_360_;
goto v___jp_353_;
}
else
{
lean_object* v_val_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec(v___x_358_);
v_val_361_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_val_361_);
lean_dec_ref_known(v___x_359_, 1);
v___x_362_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_363_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_364_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_365_ = lean_string_intercalate(v___x_364_, v_val_361_);
v___x_366_ = lean_string_append(v___x_363_, v___x_365_);
lean_dec_ref(v___x_365_);
v___x_367_ = lean_box(2);
v___x_368_ = l_Lean_Syntax_mkNameLit(v___x_366_, v___x_367_);
v___x_369_ = lean_mk_empty_array_with_capacity(v___x_333_);
v___x_370_ = lean_array_push(v___x_369_, v___x_368_);
v___x_371_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_371_, 0, v___x_367_);
lean_ctor_set(v___x_371_, 1, v___x_362_);
lean_ctor_set(v___x_371_, 2, v___x_370_);
v___y_354_ = v___x_371_;
goto v___jp_353_;
}
v___jp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
lean_inc(v___x_344_);
v___x_355_ = l_Lean_Syntax_node3(v___x_344_, v___x_352_, v___x_334_, v___y_354_, v___x_338_);
v___x_356_ = l_Lean_Syntax_node2(v___x_344_, v___x_345_, v___x_351_, v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v_a_158_);
return v___x_357_;
}
}
else
{
lean_object* v_quotContext_372_; lean_object* v_currMacroScope_373_; lean_object* v_ref_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___y_385_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_quotContext_372_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_373_ = lean_ctor_get(v_a_157_, 2);
v_ref_374_ = lean_ctor_get(v_a_157_, 5);
v___x_375_ = l_Lean_SourceInfo_fromRef(v_ref_374_, v___x_164_);
v___x_376_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_377_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40);
v___x_378_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42));
lean_inc(v_currMacroScope_373_);
lean_inc(v_quotContext_372_);
v___x_379_ = l_Lean_addMacroScope(v_quotContext_372_, v___x_378_, v_currMacroScope_373_);
v___x_380_ = lean_box(0);
v___x_381_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44));
lean_inc(v___x_375_);
v___x_382_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_382_, 0, v___x_375_);
lean_ctor_set(v___x_382_, 1, v___x_377_);
lean_ctor_set(v___x_382_, 2, v___x_379_);
lean_ctor_set(v___x_382_, 3, v___x_381_);
v___x_383_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_393_ = l_Lean_TSyntax_getId(v_id_336_);
lean_dec(v_id_336_);
lean_inc(v___x_393_);
v___x_394_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_380_, v___x_393_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_quoteNameMk(v___x_393_);
v___y_385_ = v___x_395_;
goto v___jp_384_;
}
else
{
lean_object* v_val_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v___x_393_);
v_val_396_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v___x_394_, 1);
v___x_397_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_398_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_399_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_400_ = lean_string_intercalate(v___x_399_, v_val_396_);
v___x_401_ = lean_string_append(v___x_398_, v___x_400_);
lean_dec_ref(v___x_400_);
v___x_402_ = lean_box(2);
v___x_403_ = l_Lean_Syntax_mkNameLit(v___x_401_, v___x_402_);
v___x_404_ = lean_mk_empty_array_with_capacity(v___x_333_);
v___x_405_ = lean_array_push(v___x_404_, v___x_403_);
v___x_406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_406_, 0, v___x_402_);
lean_ctor_set(v___x_406_, 1, v___x_397_);
lean_ctor_set(v___x_406_, 2, v___x_405_);
v___y_385_ = v___x_406_;
goto v___jp_384_;
}
v___jp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_386_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31));
v___x_387_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
lean_inc_n(v___x_375_, 3);
v___x_388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_375_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_Syntax_node2(v___x_375_, v___x_386_, v___x_388_, v___x_338_);
v___x_390_ = l_Lean_Syntax_node3(v___x_375_, v___x_383_, v___x_334_, v___y_385_, v___x_389_);
v___x_391_ = l_Lean_Syntax_node2(v___x_375_, v___x_376_, v___x_382_, v___x_390_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_a_158_);
return v___x_392_;
}
}
}
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_unsigned_to_nat(2u);
v___x_409_ = l_Lean_Syntax_getArg(v_x_156_, v___x_408_);
v___x_410_ = l_Lean_Syntax_matchesNull(v___x_409_, v___x_407_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec(v_x_156_);
v___x_411_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v_id_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_412_ = lean_unsigned_to_nat(1u);
v_id_413_ = l_Lean_Syntax_getArg(v_x_156_, v___x_412_);
v___x_414_ = lean_unsigned_to_nat(3u);
v___x_415_ = l_Lean_Syntax_getArg(v_x_156_, v___x_414_);
lean_dec(v_x_156_);
v___x_416_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
lean_inc(v___x_415_);
v___x_417_ = l_Lean_Syntax_isOfKind(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v_quotContext_418_; lean_object* v_currMacroScope_419_; lean_object* v_ref_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___y_431_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_quotContext_418_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_419_ = lean_ctor_get(v_a_157_, 2);
v_ref_420_ = lean_ctor_get(v_a_157_, 5);
v___x_421_ = l_Lean_SourceInfo_fromRef(v_ref_420_, v___x_162_);
v___x_422_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_423_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46);
v___x_424_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48));
lean_inc(v_currMacroScope_419_);
lean_inc(v_quotContext_418_);
v___x_425_ = l_Lean_addMacroScope(v_quotContext_418_, v___x_424_, v_currMacroScope_419_);
v___x_426_ = lean_box(0);
v___x_427_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50));
lean_inc(v___x_421_);
v___x_428_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_428_, 0, v___x_421_);
lean_ctor_set(v___x_428_, 1, v___x_423_);
lean_ctor_set(v___x_428_, 2, v___x_425_);
lean_ctor_set(v___x_428_, 3, v___x_427_);
v___x_429_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_435_ = l_Lean_TSyntax_getId(v_id_413_);
lean_dec(v_id_413_);
lean_inc(v___x_435_);
v___x_436_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_426_, v___x_435_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_quoteNameMk(v___x_435_);
v___y_431_ = v___x_437_;
goto v___jp_430_;
}
else
{
lean_object* v_val_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec(v___x_435_);
v_val_438_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v___x_436_, 1);
v___x_439_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_440_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_441_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_442_ = lean_string_intercalate(v___x_441_, v_val_438_);
v___x_443_ = lean_string_append(v___x_440_, v___x_442_);
lean_dec_ref(v___x_442_);
v___x_444_ = lean_box(2);
v___x_445_ = l_Lean_Syntax_mkNameLit(v___x_443_, v___x_444_);
v___x_446_ = lean_mk_empty_array_with_capacity(v___x_412_);
v___x_447_ = lean_array_push(v___x_446_, v___x_445_);
v___x_448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_448_, 0, v___x_444_);
lean_ctor_set(v___x_448_, 1, v___x_439_);
lean_ctor_set(v___x_448_, 2, v___x_447_);
v___y_431_ = v___x_448_;
goto v___jp_430_;
}
v___jp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
lean_inc(v___x_421_);
v___x_432_ = l_Lean_Syntax_node2(v___x_421_, v___x_429_, v___y_431_, v___x_415_);
v___x_433_ = l_Lean_Syntax_node2(v___x_421_, v___x_422_, v___x_428_, v___x_432_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v_a_158_);
return v___x_434_;
}
}
else
{
lean_object* v_quotContext_449_; lean_object* v_currMacroScope_450_; lean_object* v_ref_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___y_462_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_quotContext_449_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_450_ = lean_ctor_get(v_a_157_, 2);
v_ref_451_ = lean_ctor_get(v_a_157_, 5);
v___x_452_ = l_Lean_SourceInfo_fromRef(v_ref_451_, v___x_162_);
v___x_453_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_454_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46);
v___x_455_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48));
lean_inc(v_currMacroScope_450_);
lean_inc(v_quotContext_449_);
v___x_456_ = l_Lean_addMacroScope(v_quotContext_449_, v___x_455_, v_currMacroScope_450_);
v___x_457_ = lean_box(0);
v___x_458_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50));
lean_inc(v___x_452_);
v___x_459_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_459_, 0, v___x_452_);
lean_ctor_set(v___x_459_, 1, v___x_454_);
lean_ctor_set(v___x_459_, 2, v___x_456_);
lean_ctor_set(v___x_459_, 3, v___x_458_);
v___x_460_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_470_ = l_Lean_TSyntax_getId(v_id_413_);
lean_dec(v_id_413_);
lean_inc(v___x_470_);
v___x_471_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_457_, v___x_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_quoteNameMk(v___x_470_);
v___y_462_ = v___x_472_;
goto v___jp_461_;
}
else
{
lean_object* v_val_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec(v___x_470_);
v_val_473_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_473_);
lean_dec_ref_known(v___x_471_, 1);
v___x_474_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_475_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_476_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_477_ = lean_string_intercalate(v___x_476_, v_val_473_);
v___x_478_ = lean_string_append(v___x_475_, v___x_477_);
lean_dec_ref(v___x_477_);
v___x_479_ = lean_box(2);
v___x_480_ = l_Lean_Syntax_mkNameLit(v___x_478_, v___x_479_);
v___x_481_ = lean_mk_empty_array_with_capacity(v___x_412_);
v___x_482_ = lean_array_push(v___x_481_, v___x_480_);
v___x_483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_483_, 0, v___x_479_);
lean_ctor_set(v___x_483_, 1, v___x_474_);
lean_ctor_set(v___x_483_, 2, v___x_482_);
v___y_462_ = v___x_483_;
goto v___jp_461_;
}
v___jp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_463_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31));
v___x_464_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
lean_inc_n(v___x_452_, 3);
v___x_465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_452_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_Syntax_node2(v___x_452_, v___x_463_, v___x_465_, v___x_415_);
v___x_467_ = l_Lean_Syntax_node2(v___x_452_, v___x_460_, v___y_462_, v___x_466_);
v___x_468_ = l_Lean_Syntax_node2(v___x_452_, v___x_453_, v___x_459_, v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v_a_158_);
return v___x_469_;
}
}
}
}
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = lean_unsigned_to_nat(3u);
v___x_486_ = l_Lean_Syntax_getArg(v_x_156_, v___x_485_);
v___x_487_ = l_Lean_Syntax_matchesNull(v___x_486_, v___x_484_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_dec(v_x_156_);
v___x_488_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_id_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = l_Lean_Syntax_getArg(v_x_156_, v___x_489_);
v___x_491_ = lean_unsigned_to_nat(2u);
v_id_492_ = l_Lean_Syntax_getArg(v_x_156_, v___x_491_);
v___x_493_ = lean_unsigned_to_nat(4u);
v___x_494_ = l_Lean_Syntax_getArg(v_x_156_, v___x_493_);
lean_dec(v_x_156_);
v___x_495_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
lean_inc(v___x_494_);
v___x_496_ = l_Lean_Syntax_isOfKind(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v_quotContext_497_; lean_object* v_currMacroScope_498_; lean_object* v_ref_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___y_510_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_quotContext_497_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_498_ = lean_ctor_get(v_a_157_, 2);
v_ref_499_ = lean_ctor_get(v_a_157_, 5);
v___x_500_ = l_Lean_SourceInfo_fromRef(v_ref_499_, v___x_160_);
v___x_501_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_502_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52);
v___x_503_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54));
lean_inc(v_currMacroScope_498_);
lean_inc(v_quotContext_497_);
v___x_504_ = l_Lean_addMacroScope(v_quotContext_497_, v___x_503_, v_currMacroScope_498_);
v___x_505_ = lean_box(0);
v___x_506_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56));
lean_inc(v___x_500_);
v___x_507_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_507_, 0, v___x_500_);
lean_ctor_set(v___x_507_, 1, v___x_502_);
lean_ctor_set(v___x_507_, 2, v___x_504_);
lean_ctor_set(v___x_507_, 3, v___x_506_);
v___x_508_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_514_ = l_Lean_TSyntax_getId(v_id_492_);
lean_dec(v_id_492_);
lean_inc(v___x_514_);
v___x_515_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_505_, v___x_514_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_quoteNameMk(v___x_514_);
v___y_510_ = v___x_516_;
goto v___jp_509_;
}
else
{
lean_object* v_val_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v___x_514_);
v_val_517_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v___x_515_, 1);
v___x_518_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_519_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_520_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_521_ = lean_string_intercalate(v___x_520_, v_val_517_);
v___x_522_ = lean_string_append(v___x_519_, v___x_521_);
lean_dec_ref(v___x_521_);
v___x_523_ = lean_box(2);
v___x_524_ = l_Lean_Syntax_mkNameLit(v___x_522_, v___x_523_);
v___x_525_ = lean_mk_empty_array_with_capacity(v___x_489_);
v___x_526_ = lean_array_push(v___x_525_, v___x_524_);
v___x_527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_527_, 0, v___x_523_);
lean_ctor_set(v___x_527_, 1, v___x_518_);
lean_ctor_set(v___x_527_, 2, v___x_526_);
v___y_510_ = v___x_527_;
goto v___jp_509_;
}
v___jp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_inc(v___x_500_);
v___x_511_ = l_Lean_Syntax_node3(v___x_500_, v___x_508_, v___x_490_, v___y_510_, v___x_494_);
v___x_512_ = l_Lean_Syntax_node2(v___x_500_, v___x_501_, v___x_507_, v___x_511_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v_a_158_);
return v___x_513_;
}
}
else
{
lean_object* v_quotContext_528_; lean_object* v_currMacroScope_529_; lean_object* v_ref_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___y_541_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_quotContext_528_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_529_ = lean_ctor_get(v_a_157_, 2);
v_ref_530_ = lean_ctor_get(v_a_157_, 5);
v___x_531_ = l_Lean_SourceInfo_fromRef(v_ref_530_, v___x_160_);
v___x_532_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_533_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52);
v___x_534_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54));
lean_inc(v_currMacroScope_529_);
lean_inc(v_quotContext_528_);
v___x_535_ = l_Lean_addMacroScope(v_quotContext_528_, v___x_534_, v_currMacroScope_529_);
v___x_536_ = lean_box(0);
v___x_537_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56));
lean_inc(v___x_531_);
v___x_538_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_538_, 0, v___x_531_);
lean_ctor_set(v___x_538_, 1, v___x_533_);
lean_ctor_set(v___x_538_, 2, v___x_535_);
lean_ctor_set(v___x_538_, 3, v___x_537_);
v___x_539_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_549_ = l_Lean_TSyntax_getId(v_id_492_);
lean_dec(v_id_492_);
lean_inc(v___x_549_);
v___x_550_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_536_, v___x_549_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_quoteNameMk(v___x_549_);
v___y_541_ = v___x_551_;
goto v___jp_540_;
}
else
{
lean_object* v_val_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v___x_549_);
v_val_552_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_val_552_);
lean_dec_ref_known(v___x_550_, 1);
v___x_553_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_554_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_555_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_556_ = lean_string_intercalate(v___x_555_, v_val_552_);
v___x_557_ = lean_string_append(v___x_554_, v___x_556_);
lean_dec_ref(v___x_556_);
v___x_558_ = lean_box(2);
v___x_559_ = l_Lean_Syntax_mkNameLit(v___x_557_, v___x_558_);
v___x_560_ = lean_mk_empty_array_with_capacity(v___x_489_);
v___x_561_ = lean_array_push(v___x_560_, v___x_559_);
v___x_562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_562_, 0, v___x_558_);
lean_ctor_set(v___x_562_, 1, v___x_553_);
lean_ctor_set(v___x_562_, 2, v___x_561_);
v___y_541_ = v___x_562_;
goto v___jp_540_;
}
v___jp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_542_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31));
v___x_543_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
lean_inc_n(v___x_531_, 3);
v___x_544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_531_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = l_Lean_Syntax_node2(v___x_531_, v___x_542_, v___x_544_, v___x_494_);
v___x_546_ = l_Lean_Syntax_node3(v___x_531_, v___x_539_, v___x_490_, v___y_541_, v___x_545_);
v___x_547_ = l_Lean_Syntax_node2(v___x_531_, v___x_532_, v___x_538_, v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_a_158_);
return v___x_548_;
}
}
}
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_id_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_unsigned_to_nat(1u);
v_id_565_ = l_Lean_Syntax_getArg(v_x_156_, v___x_564_);
v___x_566_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58));
lean_inc(v_id_565_);
v___x_567_ = l_Lean_Syntax_isOfKind(v_id_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_568_ = lean_unsigned_to_nat(2u);
v___x_569_ = l_Lean_Syntax_getArg(v_x_156_, v___x_568_);
v___x_570_ = l_Lean_Syntax_matchesNull(v___x_569_, v___x_563_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
lean_dec(v_id_565_);
lean_dec(v_x_156_);
v___x_571_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_571_;
}
else
{
lean_object* v_quotContext_572_; lean_object* v_currMacroScope_573_; lean_object* v_ref_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___y_587_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_quotContext_572_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_573_ = lean_ctor_get(v_a_157_, 2);
v_ref_574_ = lean_ctor_get(v_a_157_, 5);
v___x_575_ = lean_unsigned_to_nat(3u);
v___x_576_ = l_Lean_Syntax_getArg(v_x_156_, v___x_575_);
lean_dec(v_x_156_);
v___x_577_ = l_Lean_SourceInfo_fromRef(v_ref_574_, v___x_567_);
v___x_578_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_579_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
v___x_580_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62));
lean_inc(v_currMacroScope_573_);
lean_inc(v_quotContext_572_);
v___x_581_ = l_Lean_addMacroScope(v_quotContext_572_, v___x_580_, v_currMacroScope_573_);
v___x_582_ = lean_box(0);
v___x_583_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64));
lean_inc(v___x_577_);
v___x_584_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_584_, 0, v___x_577_);
lean_ctor_set(v___x_584_, 1, v___x_579_);
lean_ctor_set(v___x_584_, 2, v___x_581_);
lean_ctor_set(v___x_584_, 3, v___x_583_);
v___x_585_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_591_ = l_Lean_TSyntax_getId(v_id_565_);
lean_dec(v_id_565_);
lean_inc(v___x_591_);
v___x_592_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_582_, v___x_591_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_quoteNameMk(v___x_591_);
v___y_587_ = v___x_593_;
goto v___jp_586_;
}
else
{
lean_object* v_val_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v___x_591_);
v_val_594_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_val_594_);
lean_dec_ref_known(v___x_592_, 1);
v___x_595_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_596_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_597_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_598_ = lean_string_intercalate(v___x_597_, v_val_594_);
v___x_599_ = lean_string_append(v___x_596_, v___x_598_);
lean_dec_ref(v___x_598_);
v___x_600_ = lean_box(2);
v___x_601_ = l_Lean_Syntax_mkNameLit(v___x_599_, v___x_600_);
v___x_602_ = lean_mk_empty_array_with_capacity(v___x_564_);
v___x_603_ = lean_array_push(v___x_602_, v___x_601_);
v___x_604_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_604_, 0, v___x_600_);
lean_ctor_set(v___x_604_, 1, v___x_595_);
lean_ctor_set(v___x_604_, 2, v___x_603_);
v___y_587_ = v___x_604_;
goto v___jp_586_;
}
v___jp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
lean_inc(v___x_577_);
v___x_588_ = l_Lean_Syntax_node2(v___x_577_, v___x_585_, v___y_587_, v___x_576_);
v___x_589_ = l_Lean_Syntax_node2(v___x_577_, v___x_578_, v___x_584_, v___x_588_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v_a_158_);
return v___x_590_;
}
}
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_605_ = lean_unsigned_to_nat(2u);
v___x_606_ = l_Lean_Syntax_getArg(v_x_156_, v___x_605_);
v___x_607_ = l_Lean_Syntax_matchesNull(v___x_606_, v___x_563_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
lean_dec(v_id_565_);
lean_dec(v_x_156_);
v___x_608_ = l_Lean_Macro_throwUnsupported___redArg(v_a_158_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_609_ = lean_unsigned_to_nat(3u);
v___x_610_ = l_Lean_Syntax_getArg(v_x_156_, v___x_609_);
lean_dec(v_x_156_);
v___x_611_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15));
lean_inc(v___x_610_);
v___x_612_ = l_Lean_Syntax_isOfKind(v___x_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v_quotContext_613_; lean_object* v_currMacroScope_614_; lean_object* v_ref_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___y_626_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_quotContext_613_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_614_ = lean_ctor_get(v_a_157_, 2);
v_ref_615_ = lean_ctor_get(v_a_157_, 5);
v___x_616_ = l_Lean_SourceInfo_fromRef(v_ref_615_, v___x_612_);
v___x_617_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_618_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
v___x_619_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62));
lean_inc(v_currMacroScope_614_);
lean_inc(v_quotContext_613_);
v___x_620_ = l_Lean_addMacroScope(v_quotContext_613_, v___x_619_, v_currMacroScope_614_);
v___x_621_ = lean_box(0);
v___x_622_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64));
lean_inc(v___x_616_);
v___x_623_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_623_, 0, v___x_616_);
lean_ctor_set(v___x_623_, 1, v___x_618_);
lean_ctor_set(v___x_623_, 2, v___x_620_);
lean_ctor_set(v___x_623_, 3, v___x_622_);
v___x_624_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_630_ = l_Lean_TSyntax_getId(v_id_565_);
lean_dec(v_id_565_);
lean_inc(v___x_630_);
v___x_631_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_621_, v___x_630_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_quoteNameMk(v___x_630_);
v___y_626_ = v___x_632_;
goto v___jp_625_;
}
else
{
lean_object* v_val_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec(v___x_630_);
v_val_633_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_val_633_);
lean_dec_ref_known(v___x_631_, 1);
v___x_634_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_635_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_636_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_637_ = lean_string_intercalate(v___x_636_, v_val_633_);
v___x_638_ = lean_string_append(v___x_635_, v___x_637_);
lean_dec_ref(v___x_637_);
v___x_639_ = lean_box(2);
v___x_640_ = l_Lean_Syntax_mkNameLit(v___x_638_, v___x_639_);
v___x_641_ = lean_mk_empty_array_with_capacity(v___x_564_);
v___x_642_ = lean_array_push(v___x_641_, v___x_640_);
v___x_643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_643_, 0, v___x_639_);
lean_ctor_set(v___x_643_, 1, v___x_634_);
lean_ctor_set(v___x_643_, 2, v___x_642_);
v___y_626_ = v___x_643_;
goto v___jp_625_;
}
v___jp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_inc(v___x_616_);
v___x_627_ = l_Lean_Syntax_node2(v___x_616_, v___x_624_, v___y_626_, v___x_610_);
v___x_628_ = l_Lean_Syntax_node2(v___x_616_, v___x_617_, v___x_623_, v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_a_158_);
return v___x_629_;
}
}
else
{
lean_object* v_quotContext_644_; lean_object* v_currMacroScope_645_; lean_object* v_ref_646_; uint8_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___y_658_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_quotContext_644_ = lean_ctor_get(v_a_157_, 1);
v_currMacroScope_645_ = lean_ctor_get(v_a_157_, 2);
v_ref_646_ = lean_ctor_get(v_a_157_, 5);
v___x_647_ = 0;
v___x_648_ = l_Lean_SourceInfo_fromRef(v_ref_646_, v___x_647_);
v___x_649_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17));
v___x_650_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60, &l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once, _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
v___x_651_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62));
lean_inc(v_currMacroScope_645_);
lean_inc(v_quotContext_644_);
v___x_652_ = l_Lean_addMacroScope(v_quotContext_644_, v___x_651_, v_currMacroScope_645_);
v___x_653_ = lean_box(0);
v___x_654_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64));
lean_inc(v___x_648_);
v___x_655_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_655_, 0, v___x_648_);
lean_ctor_set(v___x_655_, 1, v___x_650_);
lean_ctor_set(v___x_655_, 2, v___x_652_);
lean_ctor_set(v___x_655_, 3, v___x_654_);
v___x_656_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25));
v___x_666_ = l_Lean_TSyntax_getId(v_id_565_);
lean_dec(v_id_565_);
lean_inc(v___x_666_);
v___x_667_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_653_, v___x_666_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_quoteNameMk(v___x_666_);
v___y_658_ = v___x_668_;
goto v___jp_657_;
}
else
{
lean_object* v_val_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec(v___x_666_);
v_val_669_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_669_);
lean_dec_ref_known(v___x_667_, 1);
v___x_670_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27));
v___x_671_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_672_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29));
v___x_673_ = lean_string_intercalate(v___x_672_, v_val_669_);
v___x_674_ = lean_string_append(v___x_671_, v___x_673_);
lean_dec_ref(v___x_673_);
v___x_675_ = lean_box(2);
v___x_676_ = l_Lean_Syntax_mkNameLit(v___x_674_, v___x_675_);
v___x_677_ = lean_mk_empty_array_with_capacity(v___x_564_);
v___x_678_ = lean_array_push(v___x_677_, v___x_676_);
v___x_679_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_679_, 0, v___x_675_);
lean_ctor_set(v___x_679_, 1, v___x_670_);
lean_ctor_set(v___x_679_, 2, v___x_678_);
v___y_658_ = v___x_679_;
goto v___jp_657_;
}
v___jp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_659_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31));
v___x_660_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32));
lean_inc_n(v___x_648_, 3);
v___x_661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_648_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = l_Lean_Syntax_node2(v___x_648_, v___x_659_, v___x_661_, v___x_610_);
v___x_663_ = l_Lean_Syntax_node2(v___x_648_, v___x_656_, v___y_658_, v___x_662_);
v___x_664_ = l_Lean_Syntax_node2(v___x_648_, v___x_649_, v___x_655_, v___x_663_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v_a_158_);
return v___x_665_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___boxed(lean_object* v_x_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(v_x_680_, v_a_681_, v_a_682_);
lean_dec_ref(v_a_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(lean_object* v_a_684_, lean_object* v_b_685_, lean_object* v_x_686_){
_start:
{
if (lean_obj_tag(v_x_686_) == 0)
{
lean_dec(v_b_685_);
lean_dec(v_a_684_);
return v_x_686_;
}
else
{
lean_object* v_key_687_; lean_object* v_value_688_; lean_object* v_tail_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_701_; 
v_key_687_ = lean_ctor_get(v_x_686_, 0);
v_value_688_ = lean_ctor_get(v_x_686_, 1);
v_tail_689_ = lean_ctor_get(v_x_686_, 2);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_686_);
if (v_isSharedCheck_701_ == 0)
{
v___x_691_ = v_x_686_;
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_tail_689_);
lean_inc(v_value_688_);
lean_inc(v_key_687_);
lean_dec(v_x_686_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v___x_693_; 
v___x_693_ = lean_name_eq(v_key_687_, v_a_684_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_684_, v_b_685_, v_tail_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 2, v___x_694_);
v___x_696_ = v___x_691_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_value_688_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
else
{
lean_object* v___x_699_; 
lean_dec(v_value_688_);
lean_dec(v_key_687_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_b_685_);
lean_ctor_set(v___x_691_, 0, v_a_684_);
v___x_699_ = v___x_691_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_684_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_b_685_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_tail_689_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
return v_x_702_;
}
else
{
lean_object* v_key_704_; lean_object* v_value_705_; lean_object* v_tail_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_732_; 
v_key_704_ = lean_ctor_get(v_x_703_, 0);
v_value_705_ = lean_ctor_get(v_x_703_, 1);
v_tail_706_ = lean_ctor_get(v_x_703_, 2);
v_isSharedCheck_732_ = !lean_is_exclusive(v_x_703_);
if (v_isSharedCheck_732_ == 0)
{
v___x_708_ = v_x_703_;
v_isShared_709_ = v_isSharedCheck_732_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_tail_706_);
lean_inc(v_value_705_);
lean_inc(v_key_704_);
lean_dec(v_x_703_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_732_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; uint64_t v___y_712_; 
v___x_710_ = lean_array_get_size(v_x_702_);
if (lean_obj_tag(v_key_704_) == 0)
{
uint64_t v___x_730_; 
v___x_730_ = 1723ULL;
v___y_712_ = v___x_730_;
goto v___jp_711_;
}
else
{
uint64_t v_hash_731_; 
v_hash_731_ = lean_ctor_get_uint64(v_key_704_, sizeof(void*)*2);
v___y_712_ = v_hash_731_;
goto v___jp_711_;
}
v___jp_711_:
{
uint64_t v___x_713_; uint64_t v___x_714_; uint64_t v_fold_715_; uint64_t v___x_716_; uint64_t v___x_717_; uint64_t v___x_718_; size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; size_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_713_ = 32ULL;
v___x_714_ = lean_uint64_shift_right(v___y_712_, v___x_713_);
v_fold_715_ = lean_uint64_xor(v___y_712_, v___x_714_);
v___x_716_ = 16ULL;
v___x_717_ = lean_uint64_shift_right(v_fold_715_, v___x_716_);
v___x_718_ = lean_uint64_xor(v_fold_715_, v___x_717_);
v___x_719_ = lean_uint64_to_usize(v___x_718_);
v___x_720_ = lean_usize_of_nat(v___x_710_);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_sub(v___x_720_, v___x_721_);
v___x_723_ = lean_usize_land(v___x_719_, v___x_722_);
v___x_724_ = lean_array_uget_borrowed(v_x_702_, v___x_723_);
lean_inc(v___x_724_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 2, v___x_724_);
v___x_726_ = v___x_708_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_key_704_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_value_705_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v___x_724_);
v___x_726_ = v_reuseFailAlloc_729_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_727_; 
v___x_727_ = lean_array_uset(v_x_702_, v___x_723_, v___x_726_);
v_x_702_ = v___x_727_;
v_x_703_ = v_tail_706_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_733_, lean_object* v_source_734_, lean_object* v_target_735_){
_start:
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_array_get_size(v_source_734_);
v___x_737_ = lean_nat_dec_lt(v_i_733_, v___x_736_);
if (v___x_737_ == 0)
{
lean_dec_ref(v_source_734_);
lean_dec(v_i_733_);
return v_target_735_;
}
else
{
lean_object* v_es_738_; lean_object* v___x_739_; lean_object* v_source_740_; lean_object* v_target_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_es_738_ = lean_array_fget(v_source_734_, v_i_733_);
v___x_739_ = lean_box(0);
v_source_740_ = lean_array_fset(v_source_734_, v_i_733_, v___x_739_);
v_target_741_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_735_, v_es_738_);
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_nat_add(v_i_733_, v___x_742_);
lean_dec(v_i_733_);
v_i_733_ = v___x_743_;
v_source_734_ = v_source_740_;
v_target_735_ = v_target_741_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(lean_object* v_data_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v_nbuckets_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_746_ = lean_array_get_size(v_data_745_);
v___x_747_ = lean_unsigned_to_nat(2u);
v_nbuckets_748_ = lean_nat_mul(v___x_746_, v___x_747_);
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_box(0);
v___x_751_ = lean_mk_array(v_nbuckets_748_, v___x_750_);
v___x_752_ = lean_array_propagate_mark(v_data_745_, v___x_751_);
v___x_753_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v___x_749_, v_data_745_, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(lean_object* v_a_754_, lean_object* v_x_755_){
_start:
{
if (lean_obj_tag(v_x_755_) == 0)
{
uint8_t v___x_756_; 
v___x_756_ = 0;
return v___x_756_;
}
else
{
lean_object* v_key_757_; lean_object* v_tail_758_; uint8_t v___x_759_; 
v_key_757_ = lean_ctor_get(v_x_755_, 0);
v_tail_758_ = lean_ctor_get(v_x_755_, 2);
v___x_759_ = lean_name_eq(v_key_757_, v_a_754_);
if (v___x_759_ == 0)
{
v_x_755_ = v_tail_758_;
goto _start;
}
else
{
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_761_, lean_object* v_x_762_){
_start:
{
uint8_t v_res_763_; lean_object* v_r_764_; 
v_res_763_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_761_, v_x_762_);
lean_dec(v_x_762_);
lean_dec(v_a_761_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(lean_object* v_m_765_, lean_object* v_a_766_, lean_object* v_b_767_){
_start:
{
lean_object* v_size_768_; lean_object* v_buckets_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_815_; 
v_size_768_ = lean_ctor_get(v_m_765_, 0);
v_buckets_769_ = lean_ctor_get(v_m_765_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_m_765_);
if (v_isSharedCheck_815_ == 0)
{
v___x_771_ = v_m_765_;
v_isShared_772_ = v_isSharedCheck_815_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_buckets_769_);
lean_inc(v_size_768_);
lean_dec(v_m_765_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_815_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; uint64_t v___y_775_; 
v___x_773_ = lean_array_get_size(v_buckets_769_);
if (lean_obj_tag(v_a_766_) == 0)
{
uint64_t v___x_813_; 
v___x_813_ = 1723ULL;
v___y_775_ = v___x_813_;
goto v___jp_774_;
}
else
{
uint64_t v_hash_814_; 
v_hash_814_ = lean_ctor_get_uint64(v_a_766_, sizeof(void*)*2);
v___y_775_ = v_hash_814_;
goto v___jp_774_;
}
v___jp_774_:
{
uint64_t v___x_776_; uint64_t v___x_777_; uint64_t v_fold_778_; uint64_t v___x_779_; uint64_t v___x_780_; uint64_t v___x_781_; size_t v___x_782_; size_t v___x_783_; size_t v___x_784_; size_t v___x_785_; size_t v___x_786_; lean_object* v_bkt_787_; uint8_t v___x_788_; 
v___x_776_ = 32ULL;
v___x_777_ = lean_uint64_shift_right(v___y_775_, v___x_776_);
v_fold_778_ = lean_uint64_xor(v___y_775_, v___x_777_);
v___x_779_ = 16ULL;
v___x_780_ = lean_uint64_shift_right(v_fold_778_, v___x_779_);
v___x_781_ = lean_uint64_xor(v_fold_778_, v___x_780_);
v___x_782_ = lean_uint64_to_usize(v___x_781_);
v___x_783_ = lean_usize_of_nat(v___x_773_);
v___x_784_ = ((size_t)1ULL);
v___x_785_ = lean_usize_sub(v___x_783_, v___x_784_);
v___x_786_ = lean_usize_land(v___x_782_, v___x_785_);
v_bkt_787_ = lean_array_uget_borrowed(v_buckets_769_, v___x_786_);
v___x_788_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_766_, v_bkt_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v_size_x27_790_; lean_object* v___x_791_; lean_object* v_buckets_x27_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v_size_x27_790_ = lean_nat_add(v_size_768_, v___x_789_);
lean_dec(v_size_768_);
lean_inc(v_bkt_787_);
v___x_791_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_791_, 0, v_a_766_);
lean_ctor_set(v___x_791_, 1, v_b_767_);
lean_ctor_set(v___x_791_, 2, v_bkt_787_);
v_buckets_x27_792_ = lean_array_uset(v_buckets_769_, v___x_786_, v___x_791_);
v___x_793_ = lean_unsigned_to_nat(4u);
v___x_794_ = lean_nat_mul(v_size_x27_790_, v___x_793_);
v___x_795_ = lean_unsigned_to_nat(3u);
v___x_796_ = lean_nat_div(v___x_794_, v___x_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_array_get_size(v_buckets_x27_792_);
v___x_798_ = lean_nat_dec_le(v___x_796_, v___x_797_);
lean_dec(v___x_796_);
if (v___x_798_ == 0)
{
lean_object* v_val_799_; lean_object* v___x_801_; 
v_val_799_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_buckets_x27_792_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v_val_799_);
lean_ctor_set(v___x_771_, 0, v_size_x27_790_);
v___x_801_ = v___x_771_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_size_x27_790_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_val_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
else
{
lean_object* v___x_804_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v_buckets_x27_792_);
lean_ctor_set(v___x_771_, 0, v_size_x27_790_);
v___x_804_ = v___x_771_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_size_x27_790_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_buckets_x27_792_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
else
{
lean_object* v___x_806_; lean_object* v_buckets_x27_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
lean_inc(v_bkt_787_);
v___x_806_ = lean_box(0);
v_buckets_x27_807_ = lean_array_uset(v_buckets_769_, v___x_786_, v___x_806_);
v___x_808_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_766_, v_b_767_, v_bkt_787_);
v___x_809_ = lean_array_uset(v_buckets_x27_807_, v___x_786_, v___x_808_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_809_);
v___x_811_ = v___x_771_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_size_768_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(lean_object* v_as_x27_816_, lean_object* v_b_817_){
_start:
{
if (lean_obj_tag(v_as_x27_816_) == 0)
{
return v_b_817_;
}
else
{
lean_object* v_head_818_; lean_object* v_tail_819_; lean_object* v_fst_820_; lean_object* v_snd_821_; lean_object* v_r_822_; 
v_head_818_ = lean_ctor_get(v_as_x27_816_, 0);
v_tail_819_ = lean_ctor_get(v_as_x27_816_, 1);
v_fst_820_ = lean_ctor_get(v_head_818_, 0);
v_snd_821_ = lean_ctor_get(v_head_818_, 1);
lean_inc(v_snd_821_);
lean_inc(v_fst_820_);
v_r_822_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_b_817_, v_fst_820_, v_snd_821_);
v_as_x27_816_ = v_tail_819_;
v_b_817_ = v_r_822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg___boxed(lean_object* v_as_x27_824_, lean_object* v_b_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_824_, v_b_825_);
lean_dec(v_as_x27_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(lean_object* v_m_827_, lean_object* v_l_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_l_828_, v_m_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___boxed(lean_object* v_m_830_, lean_object* v_l_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(v_m_830_, v_l_831_);
lean_dec(v_l_831_);
return v_res_832_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_box(0);
v___x_896_ = lean_unsigned_to_nat(16u);
v___x_897_ = lean_mk_array(v___x_896_, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22);
v___x_899_ = lean_unsigned_to_nat(0u);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23);
v___x_902_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21));
v___x_903_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap(void){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0(lean_object* v_00_u03b2_905_, lean_object* v_m_906_, lean_object* v_a_907_, lean_object* v_b_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_m_906_, v_a_907_, v_b_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(lean_object* v_as_910_, lean_object* v_as_x27_911_, lean_object* v_b_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_911_, v_b_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___boxed(lean_object* v_as_915_, lean_object* v_as_x27_916_, lean_object* v_b_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(v_as_915_, v_as_x27_916_, v_b_917_, v_a_918_);
lean_dec(v_as_x27_916_);
lean_dec(v_as_915_);
return v_res_919_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_920_, lean_object* v_a_921_, lean_object* v_x_922_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_921_, v_x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_924_, lean_object* v_a_925_, lean_object* v_x_926_){
_start:
{
uint8_t v_res_927_; lean_object* v_r_928_; 
v_res_927_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(v_00_u03b2_924_, v_a_925_, v_x_926_);
lean_dec(v_x_926_);
lean_dec(v_a_925_);
v_r_928_ = lean_box(v_res_927_);
return v_r_928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_929_, lean_object* v_data_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_data_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_932_, lean_object* v_a_933_, lean_object* v_b_934_, lean_object* v_x_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_933_, v_b_934_, v_x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_937_, lean_object* v_i_938_, lean_object* v_source_939_, lean_object* v_target_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_938_, v_source_939_, v_target_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_943_, v_x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(lean_object* v_name_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_env_951_; lean_object* v___x_952_; lean_object* v_toEnvExtension_953_; lean_object* v_asyncMode_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_949_ = lean_box(1);
v___x_950_ = lean_st_ref_get(v___y_947_);
v_env_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc_ref(v_env_951_);
lean_dec(v___x_950_);
v___x_952_ = l_Lean_errorExplanationExt;
v_toEnvExtension_953_ = lean_ctor_get(v___x_952_, 0);
v_asyncMode_954_ = lean_ctor_get(v_toEnvExtension_953_, 2);
v___x_955_ = lean_box(0);
v___x_956_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_949_, v___x_952_, v_env_951_, v_asyncMode_954_, v___x_955_);
v___x_957_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_956_, v_name_946_);
lean_dec(v___x_956_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg___boxed(lean_object* v_name_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec(v_name_959_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(lean_object* v_name_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_963_, v___y_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___boxed(lean_object* v_name_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(v_name_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v_name_972_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(lean_object* v_msgData_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; lean_object* v_env_988_; uint8_t v___x_989_; lean_object* v_env_990_; lean_object* v___x_991_; lean_object* v_toCold_992_; lean_object* v_mctx_993_; lean_object* v_lctx_994_; lean_object* v_options_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_987_ = lean_st_ref_get(v___y_985_);
v_env_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc_ref(v_env_988_);
lean_dec(v___x_987_);
v___x_989_ = 0;
v_env_990_ = l_Lean_Environment_setRecordingDeps(v_env_988_, v___x_989_);
v___x_991_ = lean_st_ref_get(v___y_983_);
v_toCold_992_ = lean_ctor_get(v___y_984_, 0);
v_mctx_993_ = lean_ctor_get(v___x_991_, 0);
lean_inc_ref(v_mctx_993_);
lean_dec(v___x_991_);
v_lctx_994_ = lean_ctor_get(v___y_982_, 2);
v_options_995_ = lean_ctor_get(v_toCold_992_, 2);
lean_inc_ref(v_options_995_);
lean_inc_ref(v_lctx_994_);
v___x_996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_996_, 0, v_env_990_);
lean_ctor_set(v___x_996_, 1, v_mctx_993_);
lean_ctor_set(v___x_996_, 2, v_lctx_994_);
lean_ctor_set(v___x_996_, 3, v_options_995_);
v___x_997_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v_msgData_981_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18___boxed(lean_object* v_msgData_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msgData_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1005_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1006_; double v___x_1007_; 
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_float_of_nat(v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(lean_object* v_cls_1011_, lean_object* v_msg_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_ref_1018_; lean_object* v___x_1019_; lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1065_; 
v_ref_1018_ = lean_ctor_get(v___y_1015_, 2);
v___x_1019_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1065_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1065_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v_traceState_1025_; lean_object* v_env_1026_; lean_object* v_nextMacroScope_1027_; lean_object* v_ngen_1028_; lean_object* v_auxDeclNGen_1029_; lean_object* v_cache_1030_; lean_object* v_recordedDeps_1031_; lean_object* v_messages_1032_; lean_object* v_infoState_1033_; lean_object* v_snapshotTasks_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1064_; 
v___x_1024_ = lean_st_ref_take(v___y_1016_);
v_traceState_1025_ = lean_ctor_get(v___x_1024_, 4);
v_env_1026_ = lean_ctor_get(v___x_1024_, 0);
v_nextMacroScope_1027_ = lean_ctor_get(v___x_1024_, 1);
v_ngen_1028_ = lean_ctor_get(v___x_1024_, 2);
v_auxDeclNGen_1029_ = lean_ctor_get(v___x_1024_, 3);
v_cache_1030_ = lean_ctor_get(v___x_1024_, 5);
v_recordedDeps_1031_ = lean_ctor_get(v___x_1024_, 6);
v_messages_1032_ = lean_ctor_get(v___x_1024_, 7);
v_infoState_1033_ = lean_ctor_get(v___x_1024_, 8);
v_snapshotTasks_1034_ = lean_ctor_get(v___x_1024_, 9);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1036_ = v___x_1024_;
v_isShared_1037_ = v_isSharedCheck_1064_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_snapshotTasks_1034_);
lean_inc(v_infoState_1033_);
lean_inc(v_messages_1032_);
lean_inc(v_recordedDeps_1031_);
lean_inc(v_cache_1030_);
lean_inc(v_traceState_1025_);
lean_inc(v_auxDeclNGen_1029_);
lean_inc(v_ngen_1028_);
lean_inc(v_nextMacroScope_1027_);
lean_inc(v_env_1026_);
lean_dec(v___x_1024_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1064_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
uint64_t v_tid_1038_; lean_object* v_traces_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1063_; 
v_tid_1038_ = lean_ctor_get_uint64(v_traceState_1025_, sizeof(void*)*1);
v_traces_1039_ = lean_ctor_get(v_traceState_1025_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_traceState_1025_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1041_ = v_traceState_1025_;
v_isShared_1042_ = v_isSharedCheck_1063_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_traces_1039_);
lean_dec(v_traceState_1025_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1063_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; double v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
v___x_1046_ = 0;
v___x_1047_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_1048_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1048_, 0, v_cls_1011_);
lean_ctor_set(v___x_1048_, 1, v___x_1044_);
lean_ctor_set(v___x_1048_, 2, v___x_1047_);
lean_ctor_set_float(v___x_1048_, sizeof(void*)*3, v___x_1045_);
lean_ctor_set_float(v___x_1048_, sizeof(void*)*3 + 8, v___x_1045_);
lean_ctor_set_uint8(v___x_1048_, sizeof(void*)*3 + 16, v___x_1046_);
v___x_1049_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2));
v___x_1050_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1048_);
lean_ctor_set(v___x_1050_, 1, v_a_1020_);
lean_ctor_set(v___x_1050_, 2, v___x_1049_);
lean_inc(v_ref_1018_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_ref_1018_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = l_Lean_PersistentArray_push___redArg(v_traces_1039_, v___x_1051_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1052_);
v___x_1054_ = v___x_1041_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1052_);
lean_ctor_set_uint64(v_reuseFailAlloc_1062_, sizeof(void*)*1, v_tid_1038_);
v___x_1054_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1056_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1054_);
v___x_1056_ = v___x_1036_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_env_1026_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_nextMacroScope_1027_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v_ngen_1028_);
lean_ctor_set(v_reuseFailAlloc_1061_, 3, v_auxDeclNGen_1029_);
lean_ctor_set(v_reuseFailAlloc_1061_, 4, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1061_, 5, v_cache_1030_);
lean_ctor_set(v_reuseFailAlloc_1061_, 6, v_recordedDeps_1031_);
lean_ctor_set(v_reuseFailAlloc_1061_, 7, v_messages_1032_);
lean_ctor_set(v_reuseFailAlloc_1061_, 8, v_infoState_1033_);
lean_ctor_set(v_reuseFailAlloc_1061_, 9, v_snapshotTasks_1034_);
v___x_1056_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_st_ref_put(v___y_1016_, v___x_1056_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1043_);
v___x_1059_ = v___x_1022_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1043_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___boxed(lean_object* v_cls_1066_, lean_object* v_msg_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_1066_, v_msg_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(lean_object* v_as_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
if (lean_obj_tag(v_as_1077_) == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
else
{
lean_object* v_toCold_1087_; lean_object* v_options_1088_; uint8_t v_hasTrace_1089_; 
v_toCold_1087_ = lean_ctor_get(v___y_1082_, 0);
v_options_1088_ = lean_ctor_get(v_toCold_1087_, 2);
v_hasTrace_1089_ = lean_ctor_get_uint8(v_options_1088_, sizeof(void*)*1);
if (v_hasTrace_1089_ == 0)
{
lean_object* v_tail_1090_; 
v_tail_1090_ = lean_ctor_get(v_as_1077_, 1);
lean_inc(v_tail_1090_);
lean_dec_ref_known(v_as_1077_, 2);
v_as_1077_ = v_tail_1090_;
goto _start;
}
else
{
lean_object* v_head_1092_; lean_object* v_tail_1093_; lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v_inheritedTraceOptions_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_head_1092_ = lean_ctor_get(v_as_1077_, 0);
lean_inc(v_head_1092_);
v_tail_1093_ = lean_ctor_get(v_as_1077_, 1);
lean_inc(v_tail_1093_);
lean_dec_ref_known(v_as_1077_, 2);
v_fst_1094_ = lean_ctor_get(v_head_1092_, 0);
lean_inc_n(v_fst_1094_, 2);
v_snd_1095_ = lean_ctor_get(v_head_1092_, 1);
lean_inc(v_snd_1095_);
lean_dec(v_head_1092_);
v_inheritedTraceOptions_1096_ = lean_ctor_get(v_toCold_1087_, 11);
v___x_1097_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1));
v___x_1098_ = l_Lean_Name_append(v___x_1097_, v_fst_1094_);
v___x_1099_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1096_, v_options_1088_, v___x_1098_);
lean_dec(v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec(v_snd_1095_);
lean_dec(v_fst_1094_);
v_as_1077_ = v_tail_1093_;
goto _start;
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_snd_1095_);
v___x_1102_ = l_Lean_MessageData_ofFormat(v___x_1101_);
v___x_1103_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_fst_1094_, v___x_1102_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_dec_ref_known(v___x_1103_, 1);
v_as_1077_ = v_tail_1093_;
goto _start;
}
else
{
lean_dec(v_tail_1093_);
return v___x_1103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___boxed(lean_object* v_as_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v_as_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
return v_res_1113_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_box(0);
v___x_1115_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v___x_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg(){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___boxed(lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v_res_1121_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = l_Lean_maxRecDepthErrorMessage;
v___x_1128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3);
v___x_1130_ = l_Lean_MessageData_ofFormat(v___x_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4);
v___x_1132_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2));
v___x_1133_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v___x_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(lean_object* v_ref_1134_){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_ref_1134_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(lean_object* v_x_1142_, lean_object* v___y_1143_){
_start:
{
if (lean_obj_tag(v_x_1142_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; 
v_a_1144_ = lean_ctor_get(v_x_1142_, 0);
lean_inc(v_a_1144_);
v___x_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1145_, 0, v_a_1144_);
lean_ctor_set(v___x_1145_, 1, v___y_1143_);
return v___x_1145_;
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1147_; 
v_a_1146_ = lean_ctor_get(v_x_1142_, 0);
lean_inc(v_a_1146_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_a_1146_);
lean_ctor_set(v___x_1147_, 1, v___y_1143_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___boxed(lean_object* v_x_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_1148_, v___y_1149_);
lean_dec_ref(v_x_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(lean_object* v_env_1151_, lean_object* v_stx_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1151_, v_stx_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
if (lean_obj_tag(v_a_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1165_; 
v_a_1157_ = lean_ctor_get(v___x_1155_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v___x_1155_, 0);
lean_dec(v_unused_1166_);
v___x_1159_ = v___x_1155_;
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1155_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = lean_box(0);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1161_);
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_a_1157_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
lean_object* v_val_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1195_; 
v_val_1167_ = lean_ctor_get(v_a_1156_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_a_1156_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1169_ = v_a_1156_;
v_isShared_1170_ = v_isSharedCheck_1195_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_val_1167_);
lean_dec(v_a_1156_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1195_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_snd_1171_; 
v_snd_1171_ = lean_ctor_get(v_val_1167_, 1);
lean_inc(v_snd_1171_);
lean_dec(v_val_1167_);
if (lean_obj_tag(v_snd_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1181_; 
lean_del_object(v___x_1169_);
v_a_1172_ = lean_ctor_get(v___x_1155_, 1);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1155_, 2);
v_a_1173_ = lean_ctor_get(v_snd_1171_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_snd_1171_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1175_ = v_snd_1171_;
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v_snd_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_1178_, v_a_1172_);
lean_dec_ref(v___x_1178_);
return v___x_1179_;
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1194_; 
v_a_1182_ = lean_ctor_get(v___x_1155_, 1);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1155_, 2);
v_a_1183_ = lean_ctor_get(v_snd_1171_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_snd_1171_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1185_ = v_snd_1171_;
v_isShared_1186_ = v_isSharedCheck_1194_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v_snd_1171_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1194_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v_a_1183_);
v___x_1188_ = v___x_1169_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1190_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_1190_, v_a_1182_);
lean_dec_ref(v___x_1190_);
return v___x_1191_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_a_1196_ = lean_ctor_get(v___x_1155_, 0);
v_a_1197_ = lean_ctor_get(v___x_1155_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1155_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_inc(v_a_1196_);
lean_dec(v___x_1155_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1196_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed(lean_object* v_env_1205_, lean_object* v_stx_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(v_env_1205_, v_stx_1206_, v___y_1207_, v___y_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(lean_object* v_env_1210_, lean_object* v_declName_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
uint8_t v___x_1214_; lean_object* v_env_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; uint8_t v___x_1218_; 
v___x_1214_ = 0;
v_env_1215_ = l_Lean_Environment_setExporting(v_env_1210_, v___x_1214_);
lean_inc(v_declName_1211_);
v___x_1216_ = l_Lean_mkPrivateName(v_env_1215_, v_declName_1211_);
v___x_1217_ = 1;
lean_inc_ref(v_env_1215_);
v___x_1218_ = l_Lean_Environment_contains(v_env_1215_, v___x_1216_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1219_ = l_Lean_privateToUserName(v_declName_1211_);
v___x_1220_ = l_Lean_Environment_contains(v_env_1215_, v___x_1219_, v___x_1217_);
v___x_1221_ = lean_box(v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v___y_1213_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec_ref(v_env_1215_);
lean_dec(v_declName_1211_);
v___x_1223_ = lean_box(v___x_1218_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v___y_1213_);
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed(lean_object* v_env_1225_, lean_object* v_declName_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(v_env_1225_, v_declName_1226_, v___y_1227_, v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(lean_object* v_env_1230_, lean_object* v_currNamespace_1231_, lean_object* v_openDecls_1232_, lean_object* v_n_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = l_Lean_ResolveName_resolveNamespace(v_env_1230_, v_currNamespace_1231_, v_openDecls_1232_, v_n_1233_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v___y_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed(lean_object* v_env_1238_, lean_object* v_currNamespace_1239_, lean_object* v_openDecls_1240_, lean_object* v_n_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(v_env_1238_, v_currNamespace_1239_, v_openDecls_1240_, v_n_1241_, v___y_1242_, v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(lean_object* v_env_1245_, lean_object* v___x_1246_, lean_object* v_currNamespace_1247_, lean_object* v_openDecls_1248_, lean_object* v_n_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = l_Lean_ResolveName_resolveGlobalName(v_env_1245_, v___x_1246_, v_currNamespace_1247_, v_openDecls_1248_, v_n_1249_);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v___y_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed(lean_object* v_env_1254_, lean_object* v___x_1255_, lean_object* v_currNamespace_1256_, lean_object* v_openDecls_1257_, lean_object* v_n_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(v_env_1254_, v___x_1255_, v_currNamespace_1256_, v_openDecls_1257_, v_n_1258_, v___y_1259_, v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec_ref(v___x_1255_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(lean_object* v_a_1262_, lean_object* v_x_1263_){
_start:
{
if (lean_obj_tag(v_x_1263_) == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_box(0);
return v___x_1264_;
}
else
{
lean_object* v_key_1265_; lean_object* v_value_1266_; lean_object* v_tail_1267_; uint8_t v___x_1268_; 
v_key_1265_ = lean_ctor_get(v_x_1263_, 0);
v_value_1266_ = lean_ctor_get(v_x_1263_, 1);
v_tail_1267_ = lean_ctor_get(v_x_1263_, 2);
v___x_1268_ = lean_name_eq(v_key_1265_, v_a_1262_);
if (v___x_1268_ == 0)
{
v_x_1263_ = v_tail_1267_;
goto _start;
}
else
{
lean_object* v___x_1270_; 
lean_inc(v_value_1266_);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_value_1266_);
return v___x_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg___boxed(lean_object* v_a_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_1271_, v_x_1272_);
lean_dec(v_x_1272_);
lean_dec(v_a_1271_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(lean_object* v_m_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_buckets_1276_; lean_object* v___x_1277_; uint64_t v___y_1279_; 
v_buckets_1276_ = lean_ctor_get(v_m_1274_, 1);
v___x_1277_ = lean_array_get_size(v_buckets_1276_);
if (lean_obj_tag(v_a_1275_) == 0)
{
uint64_t v___x_1293_; 
v___x_1293_ = 1723ULL;
v___y_1279_ = v___x_1293_;
goto v___jp_1278_;
}
else
{
uint64_t v_hash_1294_; 
v_hash_1294_ = lean_ctor_get_uint64(v_a_1275_, sizeof(void*)*2);
v___y_1279_ = v_hash_1294_;
goto v___jp_1278_;
}
v___jp_1278_:
{
uint64_t v___x_1280_; uint64_t v___x_1281_; uint64_t v_fold_1282_; uint64_t v___x_1283_; uint64_t v___x_1284_; uint64_t v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1280_ = 32ULL;
v___x_1281_ = lean_uint64_shift_right(v___y_1279_, v___x_1280_);
v_fold_1282_ = lean_uint64_xor(v___y_1279_, v___x_1281_);
v___x_1283_ = 16ULL;
v___x_1284_ = lean_uint64_shift_right(v_fold_1282_, v___x_1283_);
v___x_1285_ = lean_uint64_xor(v_fold_1282_, v___x_1284_);
v___x_1286_ = lean_uint64_to_usize(v___x_1285_);
v___x_1287_ = lean_usize_of_nat(v___x_1277_);
v___x_1288_ = ((size_t)1ULL);
v___x_1289_ = lean_usize_sub(v___x_1287_, v___x_1288_);
v___x_1290_ = lean_usize_land(v___x_1286_, v___x_1289_);
v___x_1291_ = lean_array_uget_borrowed(v_buckets_1276_, v___x_1290_);
v___x_1292_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_1275_, v___x_1291_);
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg___boxed(lean_object* v_m_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_m_1295_);
return v_res_1297_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(lean_object* v_keys_1298_, lean_object* v_i_1299_, lean_object* v_k_1300_){
_start:
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = lean_array_get_size(v_keys_1298_);
v___x_1302_ = lean_nat_dec_lt(v_i_1299_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_dec(v_i_1299_);
return v___x_1302_;
}
else
{
lean_object* v_k_x27_1303_; uint8_t v___x_1304_; 
v_k_x27_1303_ = lean_array_fget_borrowed(v_keys_1298_, v_i_1299_);
v___x_1304_ = l_Lean_instBEqExtraModUse_beq(v_k_1300_, v_k_x27_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_unsigned_to_nat(1u);
v___x_1306_ = lean_nat_add(v_i_1299_, v___x_1305_);
lean_dec(v_i_1299_);
v_i_1299_ = v___x_1306_;
goto _start;
}
else
{
lean_dec(v_i_1299_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg___boxed(lean_object* v_keys_1308_, lean_object* v_i_1309_, lean_object* v_k_1310_){
_start:
{
uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_res_1311_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_1308_, v_i_1309_, v_k_1310_);
lean_dec_ref(v_k_1310_);
lean_dec_ref(v_keys_1308_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(lean_object* v_x_1313_, size_t v_x_1314_, lean_object* v_x_1315_){
_start:
{
if (lean_obj_tag(v_x_1313_) == 0)
{
lean_object* v_es_1316_; lean_object* v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; lean_object* v_j_1320_; lean_object* v___x_1321_; 
v_es_1316_ = lean_ctor_get(v_x_1313_, 0);
v___x_1317_ = lean_box(2);
v___x_1318_ = ((size_t)31ULL);
v___x_1319_ = lean_usize_land(v_x_1314_, v___x_1318_);
v_j_1320_ = lean_usize_to_nat(v___x_1319_);
v___x_1321_ = lean_array_get_borrowed(v___x_1317_, v_es_1316_, v_j_1320_);
lean_dec(v_j_1320_);
switch(lean_obj_tag(v___x_1321_))
{
case 0:
{
lean_object* v_key_1322_; uint8_t v___x_1323_; 
v_key_1322_ = lean_ctor_get(v___x_1321_, 0);
v___x_1323_ = l_Lean_instBEqExtraModUse_beq(v_x_1315_, v_key_1322_);
return v___x_1323_;
}
case 1:
{
lean_object* v_node_1324_; size_t v___x_1325_; size_t v___x_1326_; 
v_node_1324_ = lean_ctor_get(v___x_1321_, 0);
v___x_1325_ = ((size_t)5ULL);
v___x_1326_ = lean_usize_shift_right(v_x_1314_, v___x_1325_);
v_x_1313_ = v_node_1324_;
v_x_1314_ = v___x_1326_;
goto _start;
}
default: 
{
uint8_t v___x_1328_; 
v___x_1328_ = 0;
return v___x_1328_;
}
}
}
else
{
lean_object* v_ks_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_ks_1329_ = lean_ctor_get(v_x_1313_, 0);
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_ks_1329_, v___x_1330_, v_x_1315_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___boxed(lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_){
_start:
{
size_t v_x_20782__boxed_1335_; uint8_t v_res_1336_; lean_object* v_r_1337_; 
v_x_20782__boxed_1335_ = lean_unbox_usize(v_x_1333_);
lean_dec(v_x_1333_);
v_res_1336_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_1332_, v_x_20782__boxed_1335_, v_x_1334_);
lean_dec_ref(v_x_1334_);
lean_dec_ref(v_x_1332_);
v_r_1337_ = lean_box(v_res_1336_);
return v_r_1337_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(lean_object* v_x_1338_, lean_object* v_x_1339_){
_start:
{
uint64_t v___x_1340_; size_t v___x_1341_; uint8_t v___x_1342_; 
v___x_1340_ = l_Lean_instHashableExtraModUse_hash(v_x_1339_);
v___x_1341_ = lean_uint64_to_usize(v___x_1340_);
v___x_1342_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_1338_, v___x_1341_, v_x_1339_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg___boxed(lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
uint8_t v_res_1345_; lean_object* v_r_1346_; 
v_res_1345_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_1343_, v_x_1344_);
lean_dec_ref(v_x_1344_);
lean_dec_ref(v_x_1343_);
v_r_1346_ = lean_box(v_res_1345_);
return v_r_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___lam__0(lean_object* v___x_1347_, lean_object* v_entry_1348_, lean_object* v_s_1349_){
_start:
{
lean_object* v_addEntryFn_1350_; lean_object* v_importedEntries_1351_; lean_object* v_state_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
v_addEntryFn_1350_ = lean_ctor_get(v___x_1347_, 3);
lean_inc(v_addEntryFn_1350_);
lean_dec_ref(v___x_1347_);
v_importedEntries_1351_ = lean_ctor_get(v_s_1349_, 0);
v_state_1352_ = lean_ctor_get(v_s_1349_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_s_1349_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1354_ = v_s_1349_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_state_1352_);
lean_inc(v_importedEntries_1351_);
lean_dec(v_s_1349_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v_state_1356_; lean_object* v___x_1358_; 
v_state_1356_ = lean_apply_2(v_addEntryFn_1350_, v_state_1352_, v_entry_1348_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v_state_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_importedEntries_1351_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_state_1356_);
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
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1361_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0);
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
return v___x_1365_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1);
v___x_1367_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
lean_ctor_set(v___x_1367_, 2, v___x_1366_);
lean_ctor_set(v___x_1367_, 3, v___x_1366_);
lean_ctor_set(v___x_1367_, 4, v___x_1366_);
lean_ctor_set(v___x_1367_, 5, v___x_1366_);
return v___x_1367_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1368_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7));
v___x_1374_ = l_Lean_stringToMessageData(v___x_1373_);
return v___x_1374_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9));
v___x_1377_ = l_Lean_stringToMessageData(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_1379_ = l_Lean_stringToMessageData(v___x_1378_);
return v___x_1379_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v_cls_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_cls_1380_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6));
v___x_1381_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1));
v___x_1382_ = l_Lean_Name_append(v___x_1381_, v_cls_1380_);
return v___x_1382_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13));
v___x_1385_ = l_Lean_stringToMessageData(v___x_1384_);
return v___x_1385_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15));
v___x_1388_ = l_Lean_stringToMessageData(v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(lean_object* v_mod_1393_, uint8_t v_isMeta_1394_, lean_object* v_hint_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_env_1437_; uint8_t v_isExporting_1438_; lean_object* v_entry_1439_; lean_object* v___x_1440_; lean_object* v_env_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1435_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
v___x_1436_ = lean_st_ref_get(v___y_1401_);
v_env_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc_ref(v_env_1437_);
lean_dec(v___x_1436_);
v_isExporting_1438_ = lean_ctor_get_uint8(v_env_1437_, sizeof(void*)*13);
lean_dec_ref(v_env_1437_);
lean_inc(v_mod_1393_);
v_entry_1439_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1439_, 0, v_mod_1393_);
lean_ctor_set_uint8(v_entry_1439_, sizeof(void*)*1, v_isExporting_1438_);
lean_ctor_set_uint8(v_entry_1439_, sizeof(void*)*1 + 1, v_isMeta_1394_);
v___x_1440_ = lean_st_ref_get(v___y_1401_);
v_env_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc_ref(v_env_1441_);
lean_dec(v___x_1440_);
v___x_1442_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1443_ = lean_box(1);
v___x_1444_ = lean_box(0);
v___x_1445_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1435_, v___x_1442_, v_env_1441_, v___x_1443_, v___x_1444_);
v___x_1446_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_1445_, v_entry_1439_);
lean_dec(v___x_1445_);
if (v___x_1446_ == 0)
{
lean_object* v_toCold_1447_; lean_object* v_options_1448_; lean_object* v_inheritedTraceOptions_1449_; uint8_t v_hasTrace_1450_; lean_object* v___f_1451_; uint8_t v___x_1452_; lean_object* v___y_1454_; lean_object* v___y_1455_; 
v_toCold_1447_ = lean_ctor_get(v___y_1400_, 0);
v_options_1448_ = lean_ctor_get(v_toCold_1447_, 2);
v_inheritedTraceOptions_1449_ = lean_ctor_get(v_toCold_1447_, 11);
v_hasTrace_1450_ = lean_ctor_get_uint8(v_options_1448_, sizeof(void*)*1);
v___f_1451_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_1451_, 0, v___x_1442_);
lean_closure_set(v___f_1451_, 1, v_entry_1439_);
v___x_1452_ = 1;
if (v_hasTrace_1450_ == 0)
{
lean_dec(v_hint_1395_);
lean_dec(v_mod_1393_);
v___y_1454_ = v___y_1399_;
v___y_1455_ = v___y_1401_;
goto v___jp_1453_;
}
else
{
lean_object* v_cls_1482_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v_cls_1482_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6));
v___x_1502_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
v___x_1503_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1449_, v_options_1448_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_dec(v_hint_1395_);
lean_dec(v_mod_1393_);
v___y_1454_ = v___y_1399_;
v___y_1455_ = v___y_1401_;
goto v___jp_1453_;
}
else
{
lean_object* v___x_1504_; lean_object* v___y_1506_; 
v___x_1504_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
if (v_isExporting_1438_ == 0)
{
lean_object* v___x_1513_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19));
v___y_1506_ = v___x_1513_;
goto v___jp_1505_;
}
else
{
lean_object* v___x_1514_; 
v___x_1514_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20));
v___y_1506_ = v___x_1514_;
goto v___jp_1505_;
}
v___jp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_inc_ref(v___y_1506_);
v___x_1507_ = l_Lean_stringToMessageData(v___y_1506_);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1504_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
if (v_isMeta_1394_ == 0)
{
lean_object* v___x_1511_; 
v___x_1511_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17));
v___y_1489_ = v___x_1510_;
v___y_1490_ = v___x_1511_;
goto v___jp_1488_;
}
else
{
lean_object* v___x_1512_; 
v___x_1512_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18));
v___y_1489_ = v___x_1510_;
v___y_1490_ = v___x_1512_;
goto v___jp_1488_;
}
}
}
v___jp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___y_1484_);
lean_ctor_set(v___x_1486_, 1, v___y_1485_);
v___x_1487_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_1482_, v___x_1486_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_dec_ref_known(v___x_1487_, 1);
v___y_1454_ = v___y_1399_;
v___y_1455_ = v___y_1401_;
goto v___jp_1453_;
}
else
{
lean_dec_ref(v___f_1451_);
return v___x_1487_;
}
}
v___jp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
lean_inc_ref(v___y_1490_);
v___x_1491_ = l_Lean_stringToMessageData(v___y_1490_);
v___x_1492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___y_1489_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
v___x_1493_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8);
v___x_1494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = l_Lean_MessageData_ofName(v_mod_1393_);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_Name_isAnonymous(v_hint_1395_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
v___x_1499_ = l_Lean_MessageData_ofName(v_hint_1395_);
v___x_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1498_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___y_1484_ = v___x_1496_;
v___y_1485_ = v___x_1500_;
goto v___jp_1483_;
}
else
{
lean_object* v___x_1501_; 
lean_dec(v_hint_1395_);
v___x_1501_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11);
v___y_1484_ = v___x_1496_;
v___y_1485_ = v___x_1501_;
goto v___jp_1483_;
}
}
}
v___jp_1453_:
{
lean_object* v___x_1456_; lean_object* v_toEnvExtension_1457_; uint8_t v_logWrites_1458_; 
v___x_1456_ = lean_st_ref_take(v___y_1455_);
v_toEnvExtension_1457_ = lean_ctor_get(v___x_1442_, 0);
v_logWrites_1458_ = lean_ctor_get_uint8(v_toEnvExtension_1457_, sizeof(void*)*6);
if (v_logWrites_1458_ == 0)
{
lean_object* v_env_1459_; lean_object* v_nextMacroScope_1460_; lean_object* v_ngen_1461_; lean_object* v_auxDeclNGen_1462_; lean_object* v_traceState_1463_; lean_object* v_recordedDeps_1464_; lean_object* v_messages_1465_; lean_object* v_infoState_1466_; lean_object* v_snapshotTasks_1467_; lean_object* v_asyncMode_1468_; lean_object* v___x_1469_; 
v_env_1459_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_ref(v_env_1459_);
v_nextMacroScope_1460_ = lean_ctor_get(v___x_1456_, 1);
lean_inc(v_nextMacroScope_1460_);
v_ngen_1461_ = lean_ctor_get(v___x_1456_, 2);
lean_inc_ref(v_ngen_1461_);
v_auxDeclNGen_1462_ = lean_ctor_get(v___x_1456_, 3);
lean_inc_ref(v_auxDeclNGen_1462_);
v_traceState_1463_ = lean_ctor_get(v___x_1456_, 4);
lean_inc_ref(v_traceState_1463_);
v_recordedDeps_1464_ = lean_ctor_get(v___x_1456_, 6);
lean_inc_ref(v_recordedDeps_1464_);
v_messages_1465_ = lean_ctor_get(v___x_1456_, 7);
lean_inc_ref(v_messages_1465_);
v_infoState_1466_ = lean_ctor_get(v___x_1456_, 8);
lean_inc_ref(v_infoState_1466_);
v_snapshotTasks_1467_ = lean_ctor_get(v___x_1456_, 9);
lean_inc_ref(v_snapshotTasks_1467_);
lean_dec(v___x_1456_);
v_asyncMode_1468_ = lean_ctor_get(v_toEnvExtension_1457_, 2);
lean_inc_ref(v_toEnvExtension_1457_);
v___x_1469_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1457_, v_env_1459_, v___f_1451_, v_asyncMode_1468_, v___x_1444_, v___x_1452_);
v___y_1404_ = v_ngen_1461_;
v___y_1405_ = v_auxDeclNGen_1462_;
v___y_1406_ = v_nextMacroScope_1460_;
v___y_1407_ = v_recordedDeps_1464_;
v___y_1408_ = v_infoState_1466_;
v___y_1409_ = v_snapshotTasks_1467_;
v___y_1410_ = v_traceState_1463_;
v___y_1411_ = v___y_1455_;
v___y_1412_ = v___y_1454_;
v___y_1413_ = v_messages_1465_;
v___y_1414_ = v___x_1469_;
goto v___jp_1403_;
}
else
{
lean_object* v_env_1470_; lean_object* v_nextMacroScope_1471_; lean_object* v_ngen_1472_; lean_object* v_auxDeclNGen_1473_; lean_object* v_traceState_1474_; lean_object* v_recordedDeps_1475_; lean_object* v_messages_1476_; lean_object* v_infoState_1477_; lean_object* v_snapshotTasks_1478_; lean_object* v_asyncMode_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_env_1470_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_ref(v_env_1470_);
v_nextMacroScope_1471_ = lean_ctor_get(v___x_1456_, 1);
lean_inc(v_nextMacroScope_1471_);
v_ngen_1472_ = lean_ctor_get(v___x_1456_, 2);
lean_inc_ref(v_ngen_1472_);
v_auxDeclNGen_1473_ = lean_ctor_get(v___x_1456_, 3);
lean_inc_ref(v_auxDeclNGen_1473_);
v_traceState_1474_ = lean_ctor_get(v___x_1456_, 4);
lean_inc_ref(v_traceState_1474_);
v_recordedDeps_1475_ = lean_ctor_get(v___x_1456_, 6);
lean_inc_ref(v_recordedDeps_1475_);
v_messages_1476_ = lean_ctor_get(v___x_1456_, 7);
lean_inc_ref(v_messages_1476_);
v_infoState_1477_ = lean_ctor_get(v___x_1456_, 8);
lean_inc_ref(v_infoState_1477_);
v_snapshotTasks_1478_ = lean_ctor_get(v___x_1456_, 9);
lean_inc_ref(v_snapshotTasks_1478_);
lean_dec(v___x_1456_);
v_asyncMode_1479_ = lean_ctor_get(v_toEnvExtension_1457_, 2);
lean_inc_ref_n(v_toEnvExtension_1457_, 2);
v___x_1480_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1457_, v_env_1470_);
lean_dec_ref(v_env_1470_);
v___x_1481_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1457_, v___x_1480_, v___f_1451_, v_asyncMode_1479_, v___x_1444_, v___x_1452_);
v___y_1404_ = v_ngen_1472_;
v___y_1405_ = v_auxDeclNGen_1473_;
v___y_1406_ = v_nextMacroScope_1471_;
v___y_1407_ = v_recordedDeps_1475_;
v___y_1408_ = v_infoState_1477_;
v___y_1409_ = v_snapshotTasks_1478_;
v___y_1410_ = v_traceState_1474_;
v___y_1411_ = v___y_1455_;
v___y_1412_ = v___y_1454_;
v___y_1413_ = v_messages_1476_;
v___y_1414_ = v___x_1481_;
goto v___jp_1403_;
}
}
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec_ref_known(v_entry_1439_, 1);
lean_dec(v_hint_1395_);
lean_dec(v_mod_1393_);
v___x_1515_ = lean_box(0);
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
v___jp_1403_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v_mctx_1419_; lean_object* v_zetaDeltaFVarIds_1420_; lean_object* v_postponed_1421_; lean_object* v_diag_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1433_; 
v___x_1415_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
v___x_1416_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1416_, 0, v___y_1414_);
lean_ctor_set(v___x_1416_, 1, v___y_1406_);
lean_ctor_set(v___x_1416_, 2, v___y_1404_);
lean_ctor_set(v___x_1416_, 3, v___y_1405_);
lean_ctor_set(v___x_1416_, 4, v___y_1410_);
lean_ctor_set(v___x_1416_, 5, v___x_1415_);
lean_ctor_set(v___x_1416_, 6, v___y_1407_);
lean_ctor_set(v___x_1416_, 7, v___y_1413_);
lean_ctor_set(v___x_1416_, 8, v___y_1408_);
lean_ctor_set(v___x_1416_, 9, v___y_1409_);
v___x_1417_ = lean_st_ref_put(v___y_1411_, v___x_1416_);
v___x_1418_ = lean_st_ref_take(v___y_1412_);
v_mctx_1419_ = lean_ctor_get(v___x_1418_, 0);
v_zetaDeltaFVarIds_1420_ = lean_ctor_get(v___x_1418_, 2);
v_postponed_1421_ = lean_ctor_get(v___x_1418_, 3);
v_diag_1422_ = lean_ctor_get(v___x_1418_, 4);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v___x_1418_, 1);
lean_dec(v_unused_1434_);
v___x_1424_ = v___x_1418_;
v_isShared_1425_ = v_isSharedCheck_1433_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_diag_1422_);
lean_inc(v_postponed_1421_);
lean_inc(v_zetaDeltaFVarIds_1420_);
lean_inc(v_mctx_1419_);
lean_dec(v___x_1418_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1433_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 1, v___x_1427_);
v___x_1429_ = v___x_1424_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_mctx_1419_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_zetaDeltaFVarIds_1420_);
lean_ctor_set(v_reuseFailAlloc_1432_, 3, v_postponed_1421_);
lean_ctor_set(v_reuseFailAlloc_1432_, 4, v_diag_1422_);
v___x_1429_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_st_ref_put(v___y_1412_, v___x_1429_);
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1426_);
return v___x_1431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___boxed(lean_object* v_mod_1517_, lean_object* v_isMeta_1518_, lean_object* v_hint_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
uint8_t v_isMeta_boxed_1527_; lean_object* v_res_1528_; 
v_isMeta_boxed_1527_ = lean_unbox(v_isMeta_1518_);
v_res_1528_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_mod_1517_, v_isMeta_boxed_1527_, v_hint_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(lean_object* v___x_1529_, lean_object* v_declName_1530_, lean_object* v_as_1531_, size_t v_sz_1532_, size_t v_i_1533_, lean_object* v_b_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_usize_dec_lt(v_i_1533_, v_sz_1532_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
lean_dec(v_declName_1530_);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_b_1534_);
return v___x_1543_;
}
else
{
lean_object* v___x_1544_; lean_object* v_modules_1545_; lean_object* v___x_1546_; lean_object* v_a_1547_; lean_object* v___x_1548_; lean_object* v_toImport_1549_; lean_object* v_module_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; 
v___x_1544_ = l_Lean_Environment_header(v___x_1529_);
v_modules_1545_ = lean_ctor_get(v___x_1544_, 3);
lean_inc_ref(v_modules_1545_);
lean_dec_ref(v___x_1544_);
v___x_1546_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1547_ = lean_array_uget_borrowed(v_as_1531_, v_i_1533_);
v___x_1548_ = lean_array_get(v___x_1546_, v_modules_1545_, v_a_1547_);
lean_dec_ref(v_modules_1545_);
v_toImport_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc_ref(v_toImport_1549_);
lean_dec(v___x_1548_);
v_module_1550_ = lean_ctor_get(v_toImport_1549_, 0);
lean_inc(v_module_1550_);
lean_dec_ref(v_toImport_1549_);
v___x_1551_ = lean_box(0);
v___x_1552_ = 0;
lean_inc(v_declName_1530_);
v___x_1553_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_1550_, v___x_1552_, v_declName_1530_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
if (lean_obj_tag(v___x_1553_) == 0)
{
size_t v___x_1554_; size_t v___x_1555_; 
lean_dec_ref_known(v___x_1553_, 1);
v___x_1554_ = ((size_t)1ULL);
v___x_1555_ = lean_usize_add(v_i_1533_, v___x_1554_);
v_i_1533_ = v___x_1555_;
v_b_1534_ = v___x_1551_;
goto _start;
}
else
{
lean_dec(v_declName_1530_);
return v___x_1553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5___boxed(lean_object* v___x_1557_, lean_object* v_declName_1558_, lean_object* v_as_1559_, lean_object* v_sz_1560_, lean_object* v_i_1561_, lean_object* v_b_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
size_t v_sz_boxed_1570_; size_t v_i_boxed_1571_; lean_object* v_res_1572_; 
v_sz_boxed_1570_ = lean_unbox_usize(v_sz_1560_);
lean_dec(v_sz_1560_);
v_i_boxed_1571_ = lean_unbox_usize(v_i_1561_);
lean_dec(v_i_1561_);
v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v___x_1557_, v_declName_1558_, v_as_1559_, v_sz_boxed_1570_, v_i_boxed_1571_, v_b_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec_ref(v_as_1559_);
lean_dec_ref(v___x_1557_);
return v_res_1572_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(lean_object* v_declName_1576_, uint8_t v_isMeta_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v_env_1590_; lean_object* v___y_1592_; lean_object* v___x_1605_; 
v___x_1585_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0);
v___x_1586_ = lean_st_ref_get(v___y_1583_);
v_env_1590_ = lean_ctor_get(v___x_1586_, 0);
lean_inc_ref(v_env_1590_);
lean_dec(v___x_1586_);
v___x_1605_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1590_, v_declName_1576_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_dec_ref(v_env_1590_);
lean_dec(v_declName_1576_);
goto v___jp_1587_;
}
else
{
lean_object* v_val_1606_; lean_object* v___x_1607_; lean_object* v_modules_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v_val_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_val_1606_);
lean_dec_ref_known(v___x_1605_, 1);
v___x_1607_ = l_Lean_Environment_header(v_env_1590_);
v_modules_1608_ = lean_ctor_get(v___x_1607_, 3);
lean_inc_ref(v_modules_1608_);
lean_dec_ref(v___x_1607_);
v___x_1609_ = lean_array_get_size(v_modules_1608_);
v___x_1610_ = lean_nat_dec_lt(v_val_1606_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_dec_ref(v_modules_1608_);
lean_dec(v_val_1606_);
lean_dec_ref(v_env_1590_);
lean_dec(v_declName_1576_);
goto v___jp_1587_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___y_1614_; 
v___x_1611_ = lean_array_fget(v_modules_1608_, v_val_1606_);
lean_dec(v_val_1606_);
lean_dec_ref(v_modules_1608_);
v___x_1612_ = lean_st_ref_get(v___y_1583_);
if (v_isMeta_1577_ == 0)
{
lean_dec(v___x_1612_);
v___y_1614_ = v_isMeta_1577_;
goto v___jp_1613_;
}
else
{
lean_object* v_env_1625_; uint8_t v___x_1626_; 
v_env_1625_ = lean_ctor_get(v___x_1612_, 0);
lean_inc_ref(v_env_1625_);
lean_dec(v___x_1612_);
lean_inc(v_declName_1576_);
v___x_1626_ = l_Lean_isMarkedMeta(v_env_1625_, v_declName_1576_);
if (v___x_1626_ == 0)
{
v___y_1614_ = v_isMeta_1577_;
goto v___jp_1613_;
}
else
{
uint8_t v___x_1627_; 
v___x_1627_ = 0;
v___y_1614_ = v___x_1627_;
goto v___jp_1613_;
}
}
v___jp_1613_:
{
lean_object* v_toImport_1615_; lean_object* v_module_1616_; lean_object* v___x_1617_; 
v_toImport_1615_ = lean_ctor_get(v___x_1611_, 0);
lean_inc_ref(v_toImport_1615_);
lean_dec(v___x_1611_);
v_module_1616_ = lean_ctor_get(v_toImport_1615_, 0);
lean_inc(v_module_1616_);
lean_dec_ref(v_toImport_1615_);
lean_inc(v_declName_1576_);
v___x_1617_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_1616_, v___y_1614_, v_declName_1576_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref_known(v___x_1617_, 1);
v___x_1618_ = l_Lean_indirectModUseExt;
v___x_1619_ = lean_box(1);
v___x_1620_ = lean_box(0);
lean_inc_ref(v_env_1590_);
v___x_1621_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1585_, v___x_1618_, v_env_1590_, v___x_1619_, v___x_1620_);
v___x_1622_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_1621_, v_declName_1576_);
lean_dec(v___x_1621_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v___x_1623_; 
v___x_1623_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1));
v___y_1592_ = v___x_1623_;
goto v___jp_1591_;
}
else
{
lean_object* v_val_1624_; 
v_val_1624_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v___x_1622_, 1);
v___y_1592_ = v_val_1624_;
goto v___jp_1591_;
}
}
else
{
lean_dec_ref(v_env_1590_);
lean_dec(v_declName_1576_);
return v___x_1617_;
}
}
}
}
v___jp_1587_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_box(0);
v___x_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
return v___x_1589_;
}
v___jp_1591_:
{
lean_object* v___x_1593_; size_t v_sz_1594_; size_t v___x_1595_; lean_object* v___x_1596_; 
v___x_1593_ = lean_box(0);
v_sz_1594_ = lean_array_size(v___y_1592_);
v___x_1595_ = ((size_t)0ULL);
v___x_1596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v_env_1590_, v_declName_1576_, v___y_1592_, v_sz_1594_, v___x_1595_, v___x_1593_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec_ref(v___y_1592_);
lean_dec_ref(v_env_1590_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; 
v_unused_1604_ = lean_ctor_get(v___x_1596_, 0);
lean_dec(v_unused_1604_);
v___x_1598_ = v___x_1596_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_dec(v___x_1596_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1593_);
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1593_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
else
{
return v___x_1596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___boxed(lean_object* v_declName_1628_, lean_object* v_isMeta_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
uint8_t v_isMeta_boxed_1637_; lean_object* v_res_1638_; 
v_isMeta_boxed_1637_ = lean_unbox(v_isMeta_1629_);
v_res_1638_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_declName_1628_, v_isMeta_boxed_1637_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(lean_object* v_as_x27_1639_, lean_object* v_b_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
if (lean_obj_tag(v_as_x27_1639_) == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v_b_1640_);
return v___x_1648_;
}
else
{
lean_object* v_head_1649_; lean_object* v_tail_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; lean_object* v___x_1653_; 
v_head_1649_ = lean_ctor_get(v_as_x27_1639_, 0);
v_tail_1650_ = lean_ctor_get(v_as_x27_1639_, 1);
v___x_1651_ = lean_box(0);
v___x_1652_ = 1;
lean_inc(v_head_1649_);
v___x_1653_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_head_1649_, v___x_1652_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_dec_ref_known(v___x_1653_, 1);
v_as_x27_1639_ = v_tail_1650_;
v_b_1640_ = v___x_1651_;
goto _start;
}
else
{
return v___x_1653_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1655_, lean_object* v_b_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_1655_, v_b_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v_as_x27_1655_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(lean_object* v_currNamespace_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1668_, 0, v_currNamespace_1665_);
lean_ctor_set(v___x_1668_, 1, v___y_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(v_currNamespace_1669_, v___y_1670_, v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1672_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_box(1);
v___x_1674_ = l_Lean_MessageData_ofFormat(v___x_1673_);
return v___x_1674_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2));
v___x_1679_ = l_Lean_MessageData_ofFormat(v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(lean_object* v_x_1680_, lean_object* v_x_1681_){
_start:
{
if (lean_obj_tag(v_x_1681_) == 0)
{
return v_x_1680_;
}
else
{
lean_object* v_head_1682_; lean_object* v_tail_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1705_; 
v_head_1682_ = lean_ctor_get(v_x_1681_, 0);
v_tail_1683_ = lean_ctor_get(v_x_1681_, 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_x_1681_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1685_ = v_x_1681_;
v_isShared_1686_ = v_isSharedCheck_1705_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_tail_1683_);
lean_inc(v_head_1682_);
lean_dec(v_x_1681_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1705_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v_before_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1703_; 
v_before_1687_ = lean_ctor_get(v_head_1682_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_head_1682_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; 
v_unused_1704_ = lean_ctor_get(v_head_1682_, 1);
lean_dec(v_unused_1704_);
v___x_1689_ = v_head_1682_;
v_isShared_1690_ = v_isSharedCheck_1703_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_before_1687_);
lean_dec(v_head_1682_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1703_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1691_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_1690_ == 0)
{
lean_ctor_set_tag(v___x_1689_, 7);
lean_ctor_set(v___x_1689_, 1, v___x_1691_);
lean_ctor_set(v___x_1689_, 0, v_x_1680_);
v___x_1693_ = v___x_1689_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_x_1680_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3);
if (v_isShared_1686_ == 0)
{
lean_ctor_set_tag(v___x_1685_, 7);
lean_ctor_set(v___x_1685_, 1, v___x_1694_);
lean_ctor_set(v___x_1685_, 0, v___x_1693_);
v___x_1696_ = v___x_1685_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = l_Lean_MessageData_ofSyntax(v_before_1687_);
v___x_1698_ = l_Lean_indentD(v___x_1697_);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1696_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v_x_1680_ = v___x_1699_;
v_x_1681_ = v_tail_1683_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(lean_object* v_opts_1706_, lean_object* v_opt_1707_){
_start:
{
lean_object* v_name_1708_; lean_object* v_defValue_1709_; lean_object* v_map_1710_; lean_object* v___x_1711_; 
v_name_1708_ = lean_ctor_get(v_opt_1707_, 0);
v_defValue_1709_ = lean_ctor_get(v_opt_1707_, 1);
v_map_1710_ = lean_ctor_get(v_opts_1706_, 0);
v___x_1711_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1710_, v_name_1708_);
if (lean_obj_tag(v___x_1711_) == 0)
{
uint8_t v___x_1712_; 
v___x_1712_ = lean_unbox(v_defValue_1709_);
return v___x_1712_;
}
else
{
lean_object* v_val_1713_; 
v_val_1713_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_val_1713_);
lean_dec_ref_known(v___x_1711_, 1);
if (lean_obj_tag(v_val_1713_) == 1)
{
uint8_t v_v_1714_; 
v_v_1714_ = lean_ctor_get_uint8(v_val_1713_, 0);
lean_dec_ref_known(v_val_1713_, 0);
return v_v_1714_;
}
else
{
uint8_t v___x_1715_; 
lean_dec(v_val_1713_);
v___x_1715_ = lean_unbox(v_defValue_1709_);
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16___boxed(lean_object* v_opts_1716_, lean_object* v_opt_1717_){
_start:
{
uint8_t v_res_1718_; lean_object* v_r_1719_; 
v_res_1718_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_1716_, v_opt_1717_);
lean_dec_ref(v_opt_1717_);
lean_dec_ref(v_opts_1716_);
v_r_1719_ = lean_box(v_res_1718_);
return v_r_1719_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1));
v___x_1724_ = l_Lean_MessageData_ofFormat(v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(lean_object* v_msgData_1725_, lean_object* v_macroStack_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1729_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1727_);
v___x_1730_ = l_Lean_Elab_pp_macroStack;
v___x_1731_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v___x_1729_, v___x_1730_);
lean_dec_ref(v___x_1729_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
lean_dec(v_macroStack_1726_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_msgData_1725_);
return v___x_1732_;
}
else
{
if (lean_obj_tag(v_macroStack_1726_) == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_msgData_1725_);
return v___x_1733_;
}
else
{
lean_object* v_head_1734_; lean_object* v_after_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1750_; 
v_head_1734_ = lean_ctor_get(v_macroStack_1726_, 0);
lean_inc(v_head_1734_);
v_after_1735_ = lean_ctor_get(v_head_1734_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_head_1734_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v_head_1734_, 0);
lean_dec(v_unused_1751_);
v___x_1737_ = v_head_1734_;
v_isShared_1738_ = v_isSharedCheck_1750_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_after_1735_);
lean_dec(v_head_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1750_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 7);
lean_ctor_set(v___x_1737_, 1, v___x_1739_);
lean_ctor_set(v___x_1737_, 0, v_msgData_1725_);
v___x_1741_ = v___x_1737_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_msgData_1725_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v_msgData_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1742_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1741_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = l_Lean_MessageData_ofSyntax(v_after_1735_);
v___x_1745_ = l_Lean_indentD(v___x_1744_);
v_msgData_1746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1746_, 0, v___x_1743_);
lean_ctor_set(v_msgData_1746_, 1, v___x_1745_);
v___x_1747_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_1746_, v_macroStack_1726_);
v___x_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
return v___x_1748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___boxed(lean_object* v_msgData_1752_, lean_object* v_macroStack_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_1752_, v_macroStack_1753_, v___y_1754_);
lean_dec_ref(v___y_1754_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(lean_object* v_msg_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_ref_1765_; lean_object* v_macroStack_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1779_; 
v_ref_1765_ = lean_ctor_get(v___y_1762_, 2);
v_macroStack_1766_ = lean_ctor_get(v___y_1758_, 1);
v___x_1767_ = l_Lean_Elab_getBetterRef(v_ref_1765_, v_macroStack_1766_);
v___x_1768_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_1757_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
lean_inc(v_macroStack_1766_);
v___x_1770_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_a_1769_, v_macroStack_1766_, v___y_1762_);
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1767_);
lean_ctor_set(v___x_1775_, 1, v_a_1771_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set_tag(v___x_1773_, 1);
lean_ctor_set(v___x_1773_, 0, v___x_1775_);
v___x_1777_ = v___x_1773_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg___boxed(lean_object* v_msg_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(lean_object* v_ref_1789_, lean_object* v_msg_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_toCold_1798_; lean_object* v_currRecDepth_1799_; lean_object* v_ref_1800_; uint16_t v_optionFlags_1801_; uint8_t v_suppressElabErrors_1802_; uint8_t v_isRecordingDeps_1803_; lean_object* v_ref_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_toCold_1798_ = lean_ctor_get(v___y_1795_, 0);
v_currRecDepth_1799_ = lean_ctor_get(v___y_1795_, 1);
v_ref_1800_ = lean_ctor_get(v___y_1795_, 2);
v_optionFlags_1801_ = lean_ctor_get_uint16(v___y_1795_, sizeof(void*)*3);
v_suppressElabErrors_1802_ = lean_ctor_get_uint8(v___y_1795_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1803_ = lean_ctor_get_uint8(v___y_1795_, sizeof(void*)*3 + 3);
v_ref_1804_ = l_Lean_replaceRef(v_ref_1789_, v_ref_1800_);
lean_inc(v_currRecDepth_1799_);
lean_inc_ref(v_toCold_1798_);
v___x_1805_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1805_, 0, v_toCold_1798_);
lean_ctor_set(v___x_1805_, 1, v_currRecDepth_1799_);
lean_ctor_set(v___x_1805_, 2, v_ref_1804_);
lean_ctor_set_uint16(v___x_1805_, sizeof(void*)*3, v_optionFlags_1801_);
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*3 + 2, v_suppressElabErrors_1802_);
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*3 + 3, v_isRecordingDeps_1803_);
v___x_1806_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___x_1805_, v___y_1796_);
lean_dec_ref_known(v___x_1805_, 3);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1807_, lean_object* v_msg_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_1807_, v_msg_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v_ref_1807_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(lean_object* v_x_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; lean_object* v_toCold_1827_; lean_object* v_env_1828_; lean_object* v_currRecDepth_1829_; lean_object* v_ref_1830_; lean_object* v_maxRecDepth_1831_; lean_object* v_currNamespace_1832_; lean_object* v_openDecls_1833_; lean_object* v_quotContext_1834_; lean_object* v_currMacroScope_1835_; lean_object* v___f_1836_; lean_object* v___f_1837_; lean_object* v___x_1838_; lean_object* v___f_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v_methods_1842_; lean_object* v___x_1843_; lean_object* v_nextMacroScope_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1826_ = lean_st_ref_get(v___y_1824_);
v_toCold_1827_ = lean_ctor_get(v___y_1823_, 0);
v_env_1828_ = lean_ctor_get(v___x_1826_, 0);
lean_inc_ref_n(v_env_1828_, 4);
lean_dec(v___x_1826_);
v_currRecDepth_1829_ = lean_ctor_get(v___y_1823_, 1);
v_ref_1830_ = lean_ctor_get(v___y_1823_, 2);
v_maxRecDepth_1831_ = lean_ctor_get(v_toCold_1827_, 3);
v_currNamespace_1832_ = lean_ctor_get(v_toCold_1827_, 4);
v_openDecls_1833_ = lean_ctor_get(v_toCold_1827_, 5);
v_quotContext_1834_ = lean_ctor_get(v_toCold_1827_, 8);
v_currMacroScope_1835_ = lean_ctor_get(v_toCold_1827_, 9);
v___f_1836_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1836_, 0, v_env_1828_);
v___f_1837_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1837_, 0, v_env_1828_);
v___x_1838_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1823_);
lean_inc_n(v_currNamespace_1832_, 3);
v___f_1839_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1839_, 0, v_currNamespace_1832_);
lean_inc_n(v_openDecls_1833_, 2);
v___f_1840_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1840_, 0, v_env_1828_);
lean_closure_set(v___f_1840_, 1, v___x_1838_);
lean_closure_set(v___f_1840_, 2, v_currNamespace_1832_);
lean_closure_set(v___f_1840_, 3, v_openDecls_1833_);
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1841_, 0, v_env_1828_);
lean_closure_set(v___f_1841_, 1, v_currNamespace_1832_);
lean_closure_set(v___f_1841_, 2, v_openDecls_1833_);
v_methods_1842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1842_, 0, v___f_1837_);
lean_ctor_set(v_methods_1842_, 1, v___f_1839_);
lean_ctor_set(v_methods_1842_, 2, v___f_1836_);
lean_ctor_set(v_methods_1842_, 3, v___f_1841_);
lean_ctor_set(v_methods_1842_, 4, v___f_1840_);
v___x_1843_ = lean_st_ref_get(v___y_1824_);
v_nextMacroScope_1844_ = lean_ctor_get(v___x_1843_, 1);
lean_inc(v_nextMacroScope_1844_);
lean_dec(v___x_1843_);
lean_inc(v_ref_1830_);
lean_inc(v_maxRecDepth_1831_);
lean_inc(v_currRecDepth_1829_);
lean_inc(v_currMacroScope_1835_);
lean_inc(v_quotContext_1834_);
v___x_1845_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1845_, 0, v_methods_1842_);
lean_ctor_set(v___x_1845_, 1, v_quotContext_1834_);
lean_ctor_set(v___x_1845_, 2, v_currMacroScope_1835_);
lean_ctor_set(v___x_1845_, 3, v_currRecDepth_1829_);
lean_ctor_set(v___x_1845_, 4, v_maxRecDepth_1831_);
lean_ctor_set(v___x_1845_, 5, v_ref_1830_);
v___x_1846_ = lean_box(0);
v___x_1847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1847_, 0, v_nextMacroScope_1844_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
lean_ctor_set(v___x_1847_, 2, v___x_1846_);
v___x_1848_ = lean_apply_2(v_x_1818_, v___x_1845_, v___x_1847_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v_a_1850_; lean_object* v_macroScope_1851_; lean_object* v_traceMsgs_1852_; lean_object* v_expandedMacroDecls_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 1);
lean_inc(v_a_1849_);
v_a_1850_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1848_, 2);
v_macroScope_1851_ = lean_ctor_get(v_a_1849_, 0);
lean_inc(v_macroScope_1851_);
v_traceMsgs_1852_ = lean_ctor_get(v_a_1849_, 1);
lean_inc(v_traceMsgs_1852_);
v_expandedMacroDecls_1853_ = lean_ctor_get(v_a_1849_, 2);
lean_inc(v_expandedMacroDecls_1853_);
lean_dec(v_a_1849_);
v___x_1854_ = lean_box(0);
v___x_1855_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_expandedMacroDecls_1853_, v___x_1854_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v_expandedMacroDecls_1853_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v___x_1856_; lean_object* v_env_1857_; lean_object* v_ngen_1858_; lean_object* v_auxDeclNGen_1859_; lean_object* v_traceState_1860_; lean_object* v_cache_1861_; lean_object* v_recordedDeps_1862_; lean_object* v_messages_1863_; lean_object* v_infoState_1864_; lean_object* v_snapshotTasks_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref_known(v___x_1855_, 1);
v___x_1856_ = lean_st_ref_take(v___y_1824_);
v_env_1857_ = lean_ctor_get(v___x_1856_, 0);
v_ngen_1858_ = lean_ctor_get(v___x_1856_, 2);
v_auxDeclNGen_1859_ = lean_ctor_get(v___x_1856_, 3);
v_traceState_1860_ = lean_ctor_get(v___x_1856_, 4);
v_cache_1861_ = lean_ctor_get(v___x_1856_, 5);
v_recordedDeps_1862_ = lean_ctor_get(v___x_1856_, 6);
v_messages_1863_ = lean_ctor_get(v___x_1856_, 7);
v_infoState_1864_ = lean_ctor_get(v___x_1856_, 8);
v_snapshotTasks_1865_ = lean_ctor_get(v___x_1856_, 9);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1891_ == 0)
{
lean_object* v_unused_1892_; 
v_unused_1892_ = lean_ctor_get(v___x_1856_, 1);
lean_dec(v_unused_1892_);
v___x_1867_ = v___x_1856_;
v_isShared_1868_ = v_isSharedCheck_1891_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_snapshotTasks_1865_);
lean_inc(v_infoState_1864_);
lean_inc(v_messages_1863_);
lean_inc(v_recordedDeps_1862_);
lean_inc(v_cache_1861_);
lean_inc(v_traceState_1860_);
lean_inc(v_auxDeclNGen_1859_);
lean_inc(v_ngen_1858_);
lean_inc(v_env_1857_);
lean_dec(v___x_1856_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1891_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v_macroScope_1851_);
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_env_1857_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_macroScope_1851_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_ngen_1858_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_auxDeclNGen_1859_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v_traceState_1860_);
lean_ctor_set(v_reuseFailAlloc_1890_, 5, v_cache_1861_);
lean_ctor_set(v_reuseFailAlloc_1890_, 6, v_recordedDeps_1862_);
lean_ctor_set(v_reuseFailAlloc_1890_, 7, v_messages_1863_);
lean_ctor_set(v_reuseFailAlloc_1890_, 8, v_infoState_1864_);
lean_ctor_set(v_reuseFailAlloc_1890_, 9, v_snapshotTasks_1865_);
v___x_1870_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = lean_st_ref_put(v___y_1824_, v___x_1870_);
v___x_1872_ = l_List_reverse___redArg(v_traceMsgs_1852_);
v___x_1873_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v___x_1872_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v___x_1873_, 0);
lean_dec(v_unused_1881_);
v___x_1875_ = v___x_1873_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_dec(v___x_1873_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v_a_1850_);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1850_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_a_1850_);
v_a_1882_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1873_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1873_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v_traceMsgs_1852_);
lean_dec(v_macroScope_1851_);
lean_dec(v_a_1850_);
v_a_1893_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1855_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1855_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v_a_1901_; 
v_a_1901_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1848_, 2);
if (lean_obj_tag(v_a_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v_a_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v_a_1902_ = lean_ctor_get(v_a_1901_, 0);
lean_inc(v_a_1902_);
v_a_1903_ = lean_ctor_get(v_a_1901_, 1);
lean_inc_ref(v_a_1903_);
lean_dec_ref_known(v_a_1901_, 2);
v___x_1904_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0));
v___x_1905_ = lean_string_dec_eq(v_a_1903_, v___x_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_a_1903_);
v___x_1907_ = l_Lean_MessageData_ofFormat(v___x_1906_);
v___x_1908_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_a_1902_, v___x_1907_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v_a_1902_);
return v___x_1908_;
}
else
{
lean_object* v___x_1909_; 
lean_dec_ref(v_a_1903_);
v___x_1909_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_a_1902_);
return v___x_1909_;
}
}
else
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v___x_1910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___boxed(lean_object* v_x_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(lean_object* v_t_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; lean_object* v_infoState_1924_; uint8_t v_enabled_1925_; 
v___x_1923_ = lean_st_ref_get(v___y_1921_);
v_infoState_1924_ = lean_ctor_get(v___x_1923_, 8);
lean_inc_ref(v_infoState_1924_);
lean_dec(v___x_1923_);
v_enabled_1925_ = lean_ctor_get_uint8(v_infoState_1924_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1924_);
if (v_enabled_1925_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_dec_ref(v_t_1920_);
v___x_1926_ = lean_box(0);
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; lean_object* v_infoState_1929_; lean_object* v_env_1930_; lean_object* v_nextMacroScope_1931_; lean_object* v_ngen_1932_; lean_object* v_auxDeclNGen_1933_; lean_object* v_traceState_1934_; lean_object* v_cache_1935_; lean_object* v_recordedDeps_1936_; lean_object* v_messages_1937_; lean_object* v_snapshotTasks_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1960_; 
v___x_1928_ = lean_st_ref_take(v___y_1921_);
v_infoState_1929_ = lean_ctor_get(v___x_1928_, 8);
v_env_1930_ = lean_ctor_get(v___x_1928_, 0);
v_nextMacroScope_1931_ = lean_ctor_get(v___x_1928_, 1);
v_ngen_1932_ = lean_ctor_get(v___x_1928_, 2);
v_auxDeclNGen_1933_ = lean_ctor_get(v___x_1928_, 3);
v_traceState_1934_ = lean_ctor_get(v___x_1928_, 4);
v_cache_1935_ = lean_ctor_get(v___x_1928_, 5);
v_recordedDeps_1936_ = lean_ctor_get(v___x_1928_, 6);
v_messages_1937_ = lean_ctor_get(v___x_1928_, 7);
v_snapshotTasks_1938_ = lean_ctor_get(v___x_1928_, 9);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1940_ = v___x_1928_;
v_isShared_1941_ = v_isSharedCheck_1960_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_snapshotTasks_1938_);
lean_inc(v_infoState_1929_);
lean_inc(v_messages_1937_);
lean_inc(v_recordedDeps_1936_);
lean_inc(v_cache_1935_);
lean_inc(v_traceState_1934_);
lean_inc(v_auxDeclNGen_1933_);
lean_inc(v_ngen_1932_);
lean_inc(v_nextMacroScope_1931_);
lean_inc(v_env_1930_);
lean_dec(v___x_1928_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1960_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
uint8_t v_enabled_1942_; lean_object* v_assignment_1943_; lean_object* v_lazyAssignment_1944_; lean_object* v_trees_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1959_; 
v_enabled_1942_ = lean_ctor_get_uint8(v_infoState_1929_, sizeof(void*)*3);
v_assignment_1943_ = lean_ctor_get(v_infoState_1929_, 0);
v_lazyAssignment_1944_ = lean_ctor_get(v_infoState_1929_, 1);
v_trees_1945_ = lean_ctor_get(v_infoState_1929_, 2);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_infoState_1929_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1947_ = v_infoState_1929_;
v_isShared_1948_ = v_isSharedCheck_1959_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_trees_1945_);
lean_inc(v_lazyAssignment_1944_);
lean_inc(v_assignment_1943_);
lean_dec(v_infoState_1929_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1959_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1949_ = lean_box(0);
v___x_1950_ = l_Lean_PersistentArray_push___redArg(v_trees_1945_, v_t_1920_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 2, v___x_1950_);
v___x_1952_ = v___x_1947_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_assignment_1943_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_lazyAssignment_1944_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v___x_1950_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*3, v_enabled_1942_);
v___x_1952_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 8, v___x_1952_);
v___x_1954_ = v___x_1940_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_env_1930_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_nextMacroScope_1931_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_ngen_1932_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v_auxDeclNGen_1933_);
lean_ctor_set(v_reuseFailAlloc_1957_, 4, v_traceState_1934_);
lean_ctor_set(v_reuseFailAlloc_1957_, 5, v_cache_1935_);
lean_ctor_set(v_reuseFailAlloc_1957_, 6, v_recordedDeps_1936_);
lean_ctor_set(v_reuseFailAlloc_1957_, 7, v_messages_1937_);
lean_ctor_set(v_reuseFailAlloc_1957_, 8, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1957_, 9, v_snapshotTasks_1938_);
v___x_1954_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_st_ref_put(v___y_1921_, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1949_);
return v___x_1956_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg___boxed(lean_object* v_t_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_1961_, v___y_1962_);
lean_dec(v___y_1962_);
return v_res_1964_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1965_ = lean_unsigned_to_nat(32u);
v___x_1966_ = lean_mk_empty_array_with_capacity(v___x_1965_);
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1(void){
_start:
{
size_t v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1968_ = ((size_t)5ULL);
v___x_1969_ = lean_unsigned_to_nat(0u);
v___x_1970_ = lean_unsigned_to_nat(32u);
v___x_1971_ = lean_mk_empty_array_with_capacity(v___x_1970_);
v___x_1972_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0);
v___x_1973_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
lean_ctor_set(v___x_1973_, 1, v___x_1971_);
lean_ctor_set(v___x_1973_, 2, v___x_1969_);
lean_ctor_set(v___x_1973_, 3, v___x_1969_);
lean_ctor_set_usize(v___x_1973_, 4, v___x_1968_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(lean_object* v_t_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; lean_object* v_infoState_1983_; uint8_t v_enabled_1984_; 
v___x_1982_ = lean_st_ref_get(v___y_1980_);
v_infoState_1983_ = lean_ctor_get(v___x_1982_, 8);
lean_inc_ref(v_infoState_1983_);
lean_dec(v___x_1982_);
v_enabled_1984_ = lean_ctor_get_uint8(v_infoState_1983_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1983_);
if (v_enabled_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_dec_ref(v_t_1974_);
v___x_1985_ = lean_box(0);
v___x_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
return v___x_1986_;
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1);
v___x_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1988_, 0, v_t_1974_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v___x_1988_, v___y_1980_);
return v___x_1989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___boxed(lean_object* v_t_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v_t_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(lean_object* v_info_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_2007_, 0, v_info_1999_);
v___x_2008_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_2007_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1___boxed(lean_object* v_info_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v_info_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
return v_res_2017_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(uint8_t v_suppressElabErrors_2025_, lean_object* v_x_2026_){
_start:
{
if (lean_obj_tag(v_x_2026_) == 1)
{
lean_object* v_pre_2027_; 
v_pre_2027_ = lean_ctor_get(v_x_2026_, 0);
switch(lean_obj_tag(v_pre_2027_))
{
case 1:
{
lean_object* v_pre_2028_; 
v_pre_2028_ = lean_ctor_get(v_pre_2027_, 0);
switch(lean_obj_tag(v_pre_2028_))
{
case 0:
{
lean_object* v_str_2029_; lean_object* v_str_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v_str_2029_ = lean_ctor_get(v_x_2026_, 1);
v_str_2030_ = lean_ctor_get(v_pre_2027_, 1);
v___x_2031_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0));
v___x_2032_ = lean_string_dec_eq(v_str_2030_, v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1));
v___x_2034_ = lean_string_dec_eq(v_str_2030_, v___x_2033_);
if (v___x_2034_ == 0)
{
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2));
v___x_2036_ = lean_string_dec_eq(v_str_2029_, v___x_2035_);
if (v___x_2036_ == 0)
{
return v___x_2036_;
}
else
{
return v_suppressElabErrors_2025_;
}
}
}
else
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3));
v___x_2038_ = lean_string_dec_eq(v_str_2029_, v___x_2037_);
if (v___x_2038_ == 0)
{
return v___x_2038_;
}
else
{
return v_suppressElabErrors_2025_;
}
}
}
case 1:
{
lean_object* v_pre_2039_; 
v_pre_2039_ = lean_ctor_get(v_pre_2028_, 0);
if (lean_obj_tag(v_pre_2039_) == 0)
{
lean_object* v_str_2040_; lean_object* v_str_2041_; lean_object* v_str_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v_str_2040_ = lean_ctor_get(v_x_2026_, 1);
v_str_2041_ = lean_ctor_get(v_pre_2027_, 1);
v_str_2042_ = lean_ctor_get(v_pre_2028_, 1);
v___x_2043_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4));
v___x_2044_ = lean_string_dec_eq(v_str_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
return v___x_2044_;
}
else
{
lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5));
v___x_2046_ = lean_string_dec_eq(v_str_2041_, v___x_2045_);
if (v___x_2046_ == 0)
{
return v___x_2046_;
}
else
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6));
v___x_2048_ = lean_string_dec_eq(v_str_2040_, v___x_2047_);
if (v___x_2048_ == 0)
{
return v___x_2048_;
}
else
{
return v_suppressElabErrors_2025_;
}
}
}
}
else
{
uint8_t v___x_2049_; 
v___x_2049_ = 0;
return v___x_2049_;
}
}
default: 
{
uint8_t v___x_2050_; 
v___x_2050_ = 0;
return v___x_2050_;
}
}
}
case 0:
{
lean_object* v_str_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_str_2051_ = lean_ctor_get(v_x_2026_, 1);
v___x_2052_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0));
v___x_2053_ = lean_string_dec_eq(v_str_2051_, v___x_2052_);
if (v___x_2053_ == 0)
{
return v___x_2053_;
}
else
{
return v_suppressElabErrors_2025_;
}
}
default: 
{
uint8_t v___x_2054_; 
v___x_2054_ = 0;
return v___x_2054_;
}
}
}
else
{
uint8_t v___x_2055_; 
v___x_2055_ = 0;
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_2056_, lean_object* v_x_2057_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2058_; uint8_t v_res_2059_; lean_object* v_r_2060_; 
v_suppressElabErrors_boxed_2058_ = lean_unbox(v_suppressElabErrors_2056_);
v_res_2059_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(v_suppressElabErrors_boxed_2058_, v_x_2057_);
lean_dec(v_x_2057_);
v_r_2060_ = lean_box(v_res_2059_);
return v_r_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(lean_object* v_ref_2061_, lean_object* v_msgData_2062_, uint8_t v_severity_2063_, uint8_t v_isSilent_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
uint8_t v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; uint8_t v___y_2077_; lean_object* v_toCold_2078_; lean_object* v___y_2079_; lean_object* v___y_2108_; lean_object* v___y_2109_; uint8_t v___y_2110_; lean_object* v___y_2111_; uint8_t v___y_2112_; uint8_t v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2135_; uint8_t v___y_2136_; lean_object* v___y_2137_; uint8_t v___y_2138_; lean_object* v___y_2139_; uint8_t v___y_2140_; lean_object* v___y_2141_; uint8_t v___y_2145_; uint8_t v___y_2146_; uint8_t v___x_2156_; uint8_t v___y_2158_; uint8_t v___x_2164_; 
v___x_2156_ = 2;
v___x_2164_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2063_, v___x_2156_);
if (v___x_2164_ == 0)
{
v___y_2158_ = v___x_2164_;
goto v___jp_2157_;
}
else
{
uint8_t v___x_2165_; 
lean_inc_ref(v_msgData_2062_);
v___x_2165_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2062_);
if (v___x_2165_ == 0)
{
v___y_2158_ = v___x_2165_;
goto v___jp_2157_;
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_dec_ref(v_msgData_2062_);
v___x_2166_ = lean_box(0);
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
return v___x_2167_;
}
}
v___jp_2070_:
{
lean_object* v_currNamespace_2080_; lean_object* v_openDecls_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v_env_2086_; lean_object* v_nextMacroScope_2087_; lean_object* v_ngen_2088_; lean_object* v_auxDeclNGen_2089_; lean_object* v_traceState_2090_; lean_object* v_cache_2091_; lean_object* v_recordedDeps_2092_; lean_object* v_messages_2093_; lean_object* v_infoState_2094_; lean_object* v_snapshotTasks_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2106_; 
v_currNamespace_2080_ = lean_ctor_get(v_toCold_2078_, 4);
v_openDecls_2081_ = lean_ctor_get(v_toCold_2078_, 5);
lean_inc(v_openDecls_2081_);
lean_inc(v_currNamespace_2080_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v_currNamespace_2080_);
lean_ctor_set(v___x_2082_, 1, v_openDecls_2081_);
v___x_2083_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___y_2072_);
lean_inc_ref(v___y_2073_);
lean_inc_ref(v___y_2075_);
v___x_2084_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2084_, 0, v___y_2075_);
lean_ctor_set(v___x_2084_, 1, v___y_2074_);
lean_ctor_set(v___x_2084_, 2, v___y_2076_);
lean_ctor_set(v___x_2084_, 3, v___y_2073_);
lean_ctor_set(v___x_2084_, 4, v___x_2083_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*5, v___y_2071_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*5 + 1, v___y_2077_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*5 + 2, v_isSilent_2064_);
v___x_2085_ = lean_st_ref_take(v___y_2079_);
v_env_2086_ = lean_ctor_get(v___x_2085_, 0);
v_nextMacroScope_2087_ = lean_ctor_get(v___x_2085_, 1);
v_ngen_2088_ = lean_ctor_get(v___x_2085_, 2);
v_auxDeclNGen_2089_ = lean_ctor_get(v___x_2085_, 3);
v_traceState_2090_ = lean_ctor_get(v___x_2085_, 4);
v_cache_2091_ = lean_ctor_get(v___x_2085_, 5);
v_recordedDeps_2092_ = lean_ctor_get(v___x_2085_, 6);
v_messages_2093_ = lean_ctor_get(v___x_2085_, 7);
v_infoState_2094_ = lean_ctor_get(v___x_2085_, 8);
v_snapshotTasks_2095_ = lean_ctor_get(v___x_2085_, 9);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2097_ = v___x_2085_;
v_isShared_2098_ = v_isSharedCheck_2106_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_snapshotTasks_2095_);
lean_inc(v_infoState_2094_);
lean_inc(v_messages_2093_);
lean_inc(v_recordedDeps_2092_);
lean_inc(v_cache_2091_);
lean_inc(v_traceState_2090_);
lean_inc(v_auxDeclNGen_2089_);
lean_inc(v_ngen_2088_);
lean_inc(v_nextMacroScope_2087_);
lean_inc(v_env_2086_);
lean_dec(v___x_2085_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2106_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2099_ = lean_box(0);
v___x_2100_ = l_Lean_MessageLog_add(v___x_2084_, v_messages_2093_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 7, v___x_2100_);
v___x_2102_ = v___x_2097_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_env_2086_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_nextMacroScope_2087_);
lean_ctor_set(v_reuseFailAlloc_2105_, 2, v_ngen_2088_);
lean_ctor_set(v_reuseFailAlloc_2105_, 3, v_auxDeclNGen_2089_);
lean_ctor_set(v_reuseFailAlloc_2105_, 4, v_traceState_2090_);
lean_ctor_set(v_reuseFailAlloc_2105_, 5, v_cache_2091_);
lean_ctor_set(v_reuseFailAlloc_2105_, 6, v_recordedDeps_2092_);
lean_ctor_set(v_reuseFailAlloc_2105_, 7, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2105_, 8, v_infoState_2094_);
lean_ctor_set(v_reuseFailAlloc_2105_, 9, v_snapshotTasks_2095_);
v___x_2102_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = lean_st_ref_put(v___y_2079_, v___x_2102_);
v___x_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2099_);
return v___x_2104_;
}
}
}
v___jp_2107_:
{
lean_object* v_fileName_2116_; lean_object* v_fileMap_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2133_; 
v_fileName_2116_ = lean_ctor_get(v___y_2114_, 0);
v_fileMap_2117_ = lean_ctor_get(v___y_2114_, 1);
v___x_2118_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2062_);
v___x_2119_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v___x_2118_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2133_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2133_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
lean_inc_ref_n(v_fileMap_2117_, 2);
v___x_2124_ = l_Lean_FileMap_toPosition(v_fileMap_2117_, v___y_2111_);
lean_dec(v___y_2111_);
v___x_2125_ = l_Lean_FileMap_toPosition(v_fileMap_2117_, v___y_2115_);
lean_dec(v___y_2115_);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
v___x_2127_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
if (v___y_2112_ == 0)
{
lean_del_object(v___x_2122_);
lean_dec_ref(v___y_2108_);
v___y_2071_ = v___y_2110_;
v___y_2072_ = v_a_2120_;
v___y_2073_ = v___x_2127_;
v___y_2074_ = v___x_2124_;
v___y_2075_ = v_fileName_2116_;
v___y_2076_ = v___x_2126_;
v___y_2077_ = v___y_2113_;
v_toCold_2078_ = v___y_2109_;
v___y_2079_ = v___y_2068_;
goto v___jp_2070_;
}
else
{
uint8_t v___x_2128_; 
lean_inc(v_a_2120_);
v___x_2128_ = l_Lean_MessageData_hasTag(v___y_2108_, v_a_2120_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
lean_dec_ref_known(v___x_2126_, 1);
lean_dec_ref(v___x_2124_);
lean_dec(v_a_2120_);
v___x_2129_ = lean_box(0);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2129_);
v___x_2131_ = v___x_2122_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
else
{
lean_del_object(v___x_2122_);
v___y_2071_ = v___y_2110_;
v___y_2072_ = v_a_2120_;
v___y_2073_ = v___x_2127_;
v___y_2074_ = v___x_2124_;
v___y_2075_ = v_fileName_2116_;
v___y_2076_ = v___x_2126_;
v___y_2077_ = v___y_2113_;
v_toCold_2078_ = v___y_2109_;
v___y_2079_ = v___y_2068_;
goto v___jp_2070_;
}
}
}
}
v___jp_2134_:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_Syntax_getTailPos_x3f(v___y_2139_, v___y_2138_);
lean_dec(v___y_2139_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_inc(v___y_2141_);
v___y_2108_ = v___y_2135_;
v___y_2109_ = v___y_2137_;
v___y_2110_ = v___y_2138_;
v___y_2111_ = v___y_2141_;
v___y_2112_ = v___y_2136_;
v___y_2113_ = v___y_2140_;
v___y_2114_ = v___y_2137_;
v___y_2115_ = v___y_2141_;
goto v___jp_2107_;
}
else
{
lean_object* v_val_2143_; 
v_val_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v___y_2108_ = v___y_2135_;
v___y_2109_ = v___y_2137_;
v___y_2110_ = v___y_2138_;
v___y_2111_ = v___y_2141_;
v___y_2112_ = v___y_2136_;
v___y_2113_ = v___y_2140_;
v___y_2114_ = v___y_2137_;
v___y_2115_ = v_val_2143_;
goto v___jp_2107_;
}
}
v___jp_2144_:
{
lean_object* v_toCold_2147_; lean_object* v_ref_2148_; uint8_t v_suppressElabErrors_2149_; lean_object* v___x_2150_; lean_object* v___f_2151_; lean_object* v_ref_2152_; lean_object* v___x_2153_; 
v_toCold_2147_ = lean_ctor_get(v___y_2067_, 0);
v_ref_2148_ = lean_ctor_get(v___y_2067_, 2);
v_suppressElabErrors_2149_ = lean_ctor_get_uint8(v___y_2067_, sizeof(void*)*3 + 2);
v___x_2150_ = lean_box(v_suppressElabErrors_2149_);
v___f_2151_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2151_, 0, v___x_2150_);
v_ref_2152_ = l_Lean_replaceRef(v_ref_2061_, v_ref_2148_);
v___x_2153_ = l_Lean_Syntax_getPos_x3f(v_ref_2152_, v___y_2145_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_unsigned_to_nat(0u);
v___y_2135_ = v___f_2151_;
v___y_2136_ = v_suppressElabErrors_2149_;
v___y_2137_ = v_toCold_2147_;
v___y_2138_ = v___y_2145_;
v___y_2139_ = v_ref_2152_;
v___y_2140_ = v___y_2146_;
v___y_2141_ = v___x_2154_;
goto v___jp_2134_;
}
else
{
lean_object* v_val_2155_; 
v_val_2155_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_val_2155_);
lean_dec_ref_known(v___x_2153_, 1);
v___y_2135_ = v___f_2151_;
v___y_2136_ = v_suppressElabErrors_2149_;
v___y_2137_ = v_toCold_2147_;
v___y_2138_ = v___y_2145_;
v___y_2139_ = v_ref_2152_;
v___y_2140_ = v___y_2146_;
v___y_2141_ = v_val_2155_;
goto v___jp_2134_;
}
}
v___jp_2157_:
{
uint8_t v___x_2159_; uint8_t v___x_2160_; 
v___x_2159_ = 1;
v___x_2160_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2063_, v___x_2159_);
if (v___x_2160_ == 0)
{
v___y_2145_ = v___y_2158_;
v___y_2146_ = v_severity_2063_;
goto v___jp_2144_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2161_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2067_);
v___x_2162_ = l_Lean_warningAsError;
v___x_2163_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v___x_2161_, v___x_2162_);
lean_dec_ref(v___x_2161_);
if (v___x_2163_ == 0)
{
v___y_2145_ = v___y_2158_;
v___y_2146_ = v_severity_2063_;
goto v___jp_2144_;
}
else
{
v___y_2145_ = v___y_2158_;
v___y_2146_ = v___x_2156_;
goto v___jp_2144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___boxed(lean_object* v_ref_2168_, lean_object* v_msgData_2169_, lean_object* v_severity_2170_, lean_object* v_isSilent_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
uint8_t v_severity_boxed_2177_; uint8_t v_isSilent_boxed_2178_; lean_object* v_res_2179_; 
v_severity_boxed_2177_ = lean_unbox(v_severity_2170_);
v_isSilent_boxed_2178_ = lean_unbox(v_isSilent_2171_);
v_res_2179_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2168_, v_msgData_2169_, v_severity_boxed_2177_, v_isSilent_boxed_2178_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v_ref_2168_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(lean_object* v_ref_2180_, lean_object* v_msgData_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
uint8_t v___x_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = 2;
v___x_2190_ = 0;
v___x_2191_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2180_, v_msgData_2181_, v___x_2189_, v___x_2190_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5___boxed(lean_object* v_ref_2192_, lean_object* v_msgData_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v_ref_2192_, v_msgData_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v_ref_2192_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(lean_object* v_ref_2202_, lean_object* v_msgData_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
uint8_t v___x_2211_; uint8_t v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = 1;
v___x_2212_ = 0;
v___x_2213_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2202_, v_msgData_2203_, v___x_2211_, v___x_2212_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4___boxed(lean_object* v_ref_2214_, lean_object* v_msgData_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v_ref_2214_, v_msgData_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v_ref_2214_);
return v_res_2223_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0));
v___x_2226_ = l_Lean_stringToMessageData(v___x_2225_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2));
v___x_2229_ = l_Lean_stringToMessageData(v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4));
v___x_2232_ = l_Lean_stringToMessageData(v___x_2231_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8));
v___x_2238_ = l_Lean_stringToMessageData(v___x_2237_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10));
v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
return v___x_2241_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12));
v___x_2244_ = l_Lean_stringToMessageData(v___x_2243_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15(void){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14));
v___x_2247_ = l_Lean_stringToMessageData(v___x_2246_);
return v___x_2247_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16));
v___x_2250_ = l_Lean_stringToMessageData(v___x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(lean_object* v_stx_2251_, lean_object* v_expType_x3f_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
uint8_t v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; uint8_t v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v_fst_2353_; lean_object* v_snd_2354_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
lean_inc(v_stx_2251_);
v___x_2392_ = l_Lean_Syntax_getKind(v_stx_2251_);
v___x_2393_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_2391_, v___x_2392_);
lean_dec(v___x_2392_);
if (lean_obj_tag(v___x_2393_) == 1)
{
lean_object* v_val_2394_; lean_object* v_fst_2395_; lean_object* v_snd_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2427_; 
v_val_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_val_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v_fst_2395_ = lean_ctor_get(v_val_2394_, 0);
v_snd_2396_ = lean_ctor_get(v_val_2394_, 1);
v_isSharedCheck_2427_ = !lean_is_exclusive(v_val_2394_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2398_ = v_val_2394_;
v_isShared_2399_ = v_isSharedCheck_2427_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_snd_2396_);
lean_inc(v_fst_2395_);
lean_dec(v_val_2394_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2427_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; lean_object* v_env_2401_; uint8_t v___x_2402_; uint8_t v___x_2403_; 
v___x_2400_ = lean_st_ref_get(v_a_2258_);
v_env_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc_ref(v_env_2401_);
lean_dec(v___x_2400_);
v___x_2402_ = 1;
lean_inc(v_snd_2396_);
v___x_2403_ = l_Lean_Environment_contains(v_env_2401_, v_snd_2396_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
lean_dec(v_expType_x3f_2252_);
lean_dec(v_stx_2251_);
v___x_2404_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11);
v___x_2405_ = l_Lean_MessageData_ofName(v_snd_2396_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set_tag(v___x_2398_, 7);
lean_ctor_set(v___x_2398_, 1, v___x_2405_);
lean_ctor_set(v___x_2398_, 0, v___x_2404_);
v___x_2407_ = v___x_2398_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2404_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
v___x_2408_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15);
v___x_2411_ = l_Lean_MessageData_ofName(v_fst_2395_);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = l_Lean_MessageData_hint_x27(v___x_2414_);
v___x_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2409_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v___x_2416_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
else
{
lean_del_object(v___x_2398_);
lean_dec(v_snd_2396_);
lean_dec(v_fst_2395_);
v___y_2376_ = v_a_2253_;
v___y_2377_ = v_a_2254_;
v___y_2378_ = v_a_2255_;
v___y_2379_ = v_a_2256_;
v___y_2380_ = v_a_2257_;
v___y_2381_ = v_a_2258_;
goto v___jp_2375_;
}
}
}
else
{
lean_dec(v___x_2393_);
v___y_2376_ = v_a_2253_;
v___y_2377_ = v_a_2254_;
v___y_2378_ = v_a_2255_;
v___y_2379_ = v_a_2256_;
v___y_2380_ = v_a_2257_;
v___y_2381_ = v_a_2258_;
goto v___jp_2375_;
}
v___jp_2260_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___boxed), 3, 1);
lean_closure_set(v___x_2268_, 0, v_stx_2251_);
v___x_2269_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v___x_2268_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2271_ = l_Lean_Elab_Term_elabTerm(v_a_2270_, v_expType_x3f_2252_, v___y_2261_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v___x_2271_;
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_expType_x3f_2252_);
v_a_2272_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2269_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2269_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
v___jp_2280_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v_partialId_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2344_; 
v___x_2290_ = l_Lean_Syntax_getNumArgs(v___y_2289_);
v___x_2291_ = lean_unsigned_to_nat(2u);
v___x_2292_ = lean_nat_sub(v___x_2290_, v___x_2291_);
lean_dec(v___x_2290_);
v_partialId_2293_ = l_Lean_Syntax_getArg(v___y_2289_, v___x_2292_);
lean_dec(v___x_2292_);
v___x_2294_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___y_2289_);
lean_ctor_set(v___x_2294_, 1, v_partialId_2293_);
v___x_2295_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v___x_2294_, v___y_2286_, v___y_2282_, v___y_2288_, v___y_2283_, v___y_2281_, v___y_2287_);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2344_ == 0)
{
lean_object* v_unused_2345_; 
v_unused_2345_ = lean_ctor_get(v___x_2295_, 0);
lean_dec(v_unused_2345_);
v___x_2297_ = v___x_2295_;
v_isShared_2298_ = v_isSharedCheck_2344_;
goto v_resetjp_2296_;
}
else
{
lean_dec(v___x_2295_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2344_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2299_ = l_Lean_Syntax_getId(v___y_2285_);
v___x_2300_ = l_Lean_Name_eraseMacroScopes(v___x_2299_);
lean_dec(v___x_2299_);
lean_inc(v___x_2300_);
lean_inc(v___y_2285_);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___y_2285_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set_tag(v___x_2297_, 6);
lean_ctor_set(v___x_2297_, 0, v___x_2301_);
v___x_2303_ = v___x_2297_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v_a_2306_; 
v___x_2304_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_2303_, v___y_2286_, v___y_2282_, v___y_2288_, v___y_2283_, v___y_2281_, v___y_2287_);
lean_dec_ref(v___x_2304_);
v___x_2305_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v___x_2300_, v___y_2287_);
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref(v___x_2305_);
if (lean_obj_tag(v_a_2306_) == 1)
{
lean_object* v_val_2307_; lean_object* v_metadata_2308_; lean_object* v_removedVersion_x3f_2309_; 
v_val_2307_ = lean_ctor_get(v_a_2306_, 0);
lean_inc(v_val_2307_);
lean_dec_ref_known(v_a_2306_, 1);
v_metadata_2308_ = lean_ctor_get(v_val_2307_, 1);
lean_inc_ref(v_metadata_2308_);
lean_dec(v_val_2307_);
v_removedVersion_x3f_2309_ = lean_ctor_get(v_metadata_2308_, 2);
lean_inc(v_removedVersion_x3f_2309_);
lean_dec_ref(v_metadata_2308_);
if (lean_obj_tag(v_removedVersion_x3f_2309_) == 1)
{
lean_object* v_val_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_val_2310_ = lean_ctor_get(v_removedVersion_x3f_2309_, 0);
lean_inc(v_val_2310_);
lean_dec_ref_known(v_removedVersion_x3f_2309_, 1);
v___x_2311_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1);
v___x_2312_ = l_Lean_MessageData_ofName(v___x_2300_);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = l_Lean_stringToMessageData(v_val_2310_);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v___y_2285_, v___x_2319_, v___y_2286_, v___y_2282_, v___y_2288_, v___y_2283_, v___y_2281_, v___y_2287_);
lean_dec(v___y_2285_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_dec_ref_known(v___x_2320_, 1);
v___y_2261_ = v___y_2284_;
v___y_2262_ = v___y_2286_;
v___y_2263_ = v___y_2282_;
v___y_2264_ = v___y_2288_;
v___y_2265_ = v___y_2283_;
v___y_2266_ = v___y_2281_;
v___y_2267_ = v___y_2287_;
goto v___jp_2260_;
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_expType_x3f_2252_);
lean_dec(v_stx_2251_);
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_dec(v_removedVersion_x3f_2309_);
lean_dec(v___x_2300_);
lean_dec(v___y_2285_);
v___y_2261_ = v___y_2284_;
v___y_2262_ = v___y_2286_;
v___y_2263_ = v___y_2282_;
v___y_2264_ = v___y_2288_;
v___y_2265_ = v___y_2283_;
v___y_2266_ = v___y_2281_;
v___y_2267_ = v___y_2287_;
goto v___jp_2260_;
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec(v_a_2306_);
v___x_2329_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7);
v___x_2330_ = l_Lean_MessageData_ofName(v___x_2300_);
v___x_2331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9);
v___x_2333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v___y_2285_, v___x_2333_, v___y_2286_, v___y_2282_, v___y_2288_, v___y_2283_, v___y_2281_, v___y_2287_);
lean_dec(v___y_2285_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_dec_ref_known(v___x_2334_, 1);
v___y_2261_ = v___y_2284_;
v___y_2262_ = v___y_2286_;
v___y_2263_ = v___y_2282_;
v___y_2264_ = v___y_2288_;
v___y_2265_ = v___y_2283_;
v___y_2266_ = v___y_2281_;
v___y_2267_ = v___y_2287_;
goto v___jp_2260_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_expType_x3f_2252_);
lean_dec(v_stx_2251_);
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
}
}
v___jp_2346_:
{
lean_object* v___x_2355_; uint8_t v___x_2356_; uint8_t v___x_2357_; 
v___x_2355_ = l_Lean_Syntax_getNumArgs(v_stx_2251_);
v___x_2356_ = lean_nat_dec_eq(v___x_2355_, v_snd_2354_);
v___x_2357_ = 1;
if (v___x_2356_ == 0)
{
lean_dec(v___x_2355_);
lean_inc(v_stx_2251_);
v___y_2281_ = v___y_2347_;
v___y_2282_ = v___y_2348_;
v___y_2283_ = v___y_2349_;
v___y_2284_ = v___x_2357_;
v___y_2285_ = v_fst_2353_;
v___y_2286_ = v___y_2350_;
v___y_2287_ = v___y_2351_;
v___y_2288_ = v___y_2352_;
v___y_2289_ = v_stx_2251_;
goto v___jp_2280_;
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2358_ = l_Lean_Syntax_getArgs(v_stx_2251_);
v___x_2359_ = lean_unsigned_to_nat(1u);
v___x_2360_ = lean_nat_sub(v___x_2355_, v___x_2359_);
lean_dec(v___x_2355_);
v___x_2361_ = lean_unsigned_to_nat(0u);
v___x_2362_ = l_Array_toSubarray___redArg(v___x_2358_, v___x_2361_, v___x_2360_);
v___x_2363_ = l_Subarray_copy___redArg(v___x_2362_);
lean_inc(v_stx_2251_);
v___x_2364_ = l_Lean_Syntax_setArgs(v_stx_2251_, v___x_2363_);
v___y_2281_ = v___y_2347_;
v___y_2282_ = v___y_2348_;
v___y_2283_ = v___y_2349_;
v___y_2284_ = v___x_2357_;
v___y_2285_ = v_fst_2353_;
v___y_2286_ = v___y_2350_;
v___y_2287_ = v___y_2351_;
v___y_2288_ = v___y_2352_;
v___y_2289_ = v___x_2364_;
goto v___jp_2280_;
}
}
v___jp_2365_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2372_ = lean_unsigned_to_nat(2u);
v___x_2373_ = l_Lean_Syntax_getArg(v_stx_2251_, v___x_2372_);
v___x_2374_ = lean_unsigned_to_nat(5u);
v___y_2347_ = v___y_2366_;
v___y_2348_ = v___y_2367_;
v___y_2349_ = v___y_2368_;
v___y_2350_ = v___y_2369_;
v___y_2351_ = v___y_2370_;
v___y_2352_ = v___y_2371_;
v_fst_2353_ = v___x_2373_;
v_snd_2354_ = v___x_2374_;
goto v___jp_2346_;
}
v___jp_2375_:
{
lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
lean_inc(v_stx_2251_);
v___x_2383_ = l_Lean_Syntax_isOfKind(v_stx_2251_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
lean_inc(v_stx_2251_);
v___x_2385_ = l_Lean_Syntax_isOfKind(v_stx_2251_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2386_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
lean_inc(v_stx_2251_);
v___x_2387_ = l_Lean_Syntax_isOfKind(v_stx_2251_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = lean_unsigned_to_nat(1u);
v___x_2389_ = l_Lean_Syntax_getArg(v_stx_2251_, v___x_2388_);
v___x_2390_ = lean_unsigned_to_nat(4u);
v___y_2347_ = v___y_2380_;
v___y_2348_ = v___y_2377_;
v___y_2349_ = v___y_2379_;
v___y_2350_ = v___y_2376_;
v___y_2351_ = v___y_2381_;
v___y_2352_ = v___y_2378_;
v_fst_2353_ = v___x_2389_;
v_snd_2354_ = v___x_2390_;
goto v___jp_2346_;
}
else
{
v___y_2366_ = v___y_2380_;
v___y_2367_ = v___y_2377_;
v___y_2368_ = v___y_2379_;
v___y_2369_ = v___y_2376_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v___y_2378_;
goto v___jp_2365_;
}
}
else
{
v___y_2366_ = v___y_2380_;
v___y_2367_ = v___y_2377_;
v___y_2368_ = v___y_2379_;
v___y_2369_ = v___y_2376_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v___y_2378_;
goto v___jp_2365_;
}
}
else
{
v___y_2366_ = v___y_2380_;
v___y_2367_ = v___y_2377_;
v___y_2368_ = v___y_2379_;
v___y_2369_ = v___y_2376_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v___y_2378_;
goto v___jp_2365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed(lean_object* v_stx_2428_, lean_object* v_expType_x3f_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(v_stx_2428_, v_expType_x3f_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(lean_object* v_00_u03b1_2438_, lean_object* v_x_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_2439_, v___y_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2443_, lean_object* v_x_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(v_00_u03b1_2443_, v_x_2444_, v___y_2445_, v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec_ref(v_x_2444_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(lean_object* v_00_u03b1_2448_, lean_object* v_ref_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_2449_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___boxed(lean_object* v_00_u03b1_2458_, lean_object* v_ref_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(v_00_u03b1_2458_, v_ref_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(lean_object* v_00_u03b1_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(v_00_u03b1_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(lean_object* v_00_u03b1_2486_, lean_object* v_x_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___boxed(lean_object* v_00_u03b1_2496_, lean_object* v_x_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(v_00_u03b1_2496_, v_x_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(lean_object* v_t_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_2506_, v___y_2512_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___boxed(lean_object* v_t_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(v_t_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(lean_object* v_00_u03b2_2524_, lean_object* v_m_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_2525_, v_a_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___boxed(lean_object* v_00_u03b2_2528_, lean_object* v_m_2529_, lean_object* v_a_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(v_00_u03b2_2528_, v_m_2529_, v_a_2530_);
lean_dec(v_a_2530_);
lean_dec_ref(v_m_2529_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(lean_object* v_00_u03b1_2532_, lean_object* v_msg_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___boxed(lean_object* v_00_u03b1_2542_, lean_object* v_msg_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(v_00_u03b1_2542_, v_msg_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(lean_object* v_cls_2552_, lean_object* v_msg_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_2552_, v_msg_2553_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___boxed(lean_object* v_cls_2562_, lean_object* v_msg_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(v_cls_2562_, v_msg_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(lean_object* v_as_2572_, lean_object* v_as_x27_2573_, lean_object* v_b_2574_, lean_object* v_a_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_2573_, v_b_2574_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___boxed(lean_object* v_as_2584_, lean_object* v_as_x27_2585_, lean_object* v_b_2586_, lean_object* v_a_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(v_as_2584_, v_as_x27_2585_, v_b_2586_, v_a_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v_as_x27_2585_);
lean_dec(v_as_2584_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(lean_object* v_00_u03b1_2596_, lean_object* v_ref_2597_, lean_object* v_msg_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_2597_, v_msg_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2607_, lean_object* v_ref_2608_, lean_object* v_msg_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(v_00_u03b1_2607_, v_ref_2608_, v_msg_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v_ref_2608_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(lean_object* v_ref_2618_, lean_object* v_msgData_2619_, uint8_t v_severity_2620_, uint8_t v_isSilent_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2618_, v_msgData_2619_, v_severity_2620_, v_isSilent_2621_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___boxed(lean_object* v_ref_2630_, lean_object* v_msgData_2631_, lean_object* v_severity_2632_, lean_object* v_isSilent_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
uint8_t v_severity_boxed_2641_; uint8_t v_isSilent_boxed_2642_; lean_object* v_res_2643_; 
v_severity_boxed_2641_ = lean_unbox(v_severity_2632_);
v_isSilent_boxed_2642_ = lean_unbox(v_isSilent_2633_);
v_res_2643_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(v_ref_2630_, v_msgData_2631_, v_severity_boxed_2641_, v_isSilent_boxed_2642_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v_ref_2630_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(lean_object* v_00_u03b2_2644_, lean_object* v_a_2645_, lean_object* v_x_2646_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_2645_, v_x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___boxed(lean_object* v_00_u03b2_2648_, lean_object* v_a_2649_, lean_object* v_x_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(v_00_u03b2_2648_, v_a_2649_, v_x_2650_);
lean_dec(v_x_2650_);
lean_dec(v_a_2649_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(lean_object* v_msgData_2652_, lean_object* v_macroStack_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_2652_, v_macroStack_2653_, v___y_2658_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___boxed(lean_object* v_msgData_2662_, lean_object* v_macroStack_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(v_msgData_2662_, v_macroStack_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
return v_res_2671_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(lean_object* v_00_u03b2_2672_, lean_object* v_x_2673_, lean_object* v_x_2674_){
_start:
{
uint8_t v___x_2675_; 
v___x_2675_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_2673_, v_x_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___boxed(lean_object* v_00_u03b2_2676_, lean_object* v_x_2677_, lean_object* v_x_2678_){
_start:
{
uint8_t v_res_2679_; lean_object* v_r_2680_; 
v_res_2679_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(v_00_u03b2_2676_, v_x_2677_, v_x_2678_);
lean_dec_ref(v_x_2678_);
lean_dec_ref(v_x_2677_);
v_r_2680_ = lean_box(v_res_2679_);
return v_r_2680_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(lean_object* v_00_u03b2_2681_, lean_object* v_x_2682_, size_t v_x_2683_, lean_object* v_x_2684_){
_start:
{
uint8_t v___x_2685_; 
v___x_2685_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_2682_, v_x_2683_, v_x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___boxed(lean_object* v_00_u03b2_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_, lean_object* v_x_2689_){
_start:
{
size_t v_x_22871__boxed_2690_; uint8_t v_res_2691_; lean_object* v_r_2692_; 
v_x_22871__boxed_2690_ = lean_unbox_usize(v_x_2688_);
lean_dec(v_x_2688_);
v_res_2691_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(v_00_u03b2_2686_, v_x_2687_, v_x_22871__boxed_2690_, v_x_2689_);
lean_dec_ref(v_x_2689_);
lean_dec_ref(v_x_2687_);
v_r_2692_ = lean_box(v_res_2691_);
return v_r_2692_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(lean_object* v_00_u03b2_2693_, lean_object* v_keys_2694_, lean_object* v_vals_2695_, lean_object* v_heq_2696_, lean_object* v_i_2697_, lean_object* v_k_2698_){
_start:
{
uint8_t v___x_2699_; 
v___x_2699_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_2694_, v_i_2697_, v_k_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___boxed(lean_object* v_00_u03b2_2700_, lean_object* v_keys_2701_, lean_object* v_vals_2702_, lean_object* v_heq_2703_, lean_object* v_i_2704_, lean_object* v_k_2705_){
_start:
{
uint8_t v_res_2706_; lean_object* v_r_2707_; 
v_res_2706_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(v_00_u03b2_2700_, v_keys_2701_, v_vals_2702_, v_heq_2703_, v_i_2704_, v_k_2705_);
lean_dec_ref(v_k_2705_);
lean_dec_ref(v_vals_2702_);
lean_dec_ref(v_keys_2701_);
v_r_2707_ = lean_box(v_res_2706_);
return v_r_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1(){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2716_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2717_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3));
v___x_2718_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2719_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2720_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2716_, v___x_2717_, v___x_2718_, v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___boxed(lean_object* v_a_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3(){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2724_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2725_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
v___x_2726_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2727_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2728_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2724_, v___x_2725_, v___x_2726_, v___x_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3___boxed(lean_object* v_a_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5(){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2732_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2733_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7));
v___x_2734_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2735_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2736_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2732_, v___x_2733_, v___x_2734_, v___x_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5___boxed(lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7(){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2740_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2741_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
v___x_2742_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2743_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2744_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2740_, v___x_2741_, v___x_2742_, v___x_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7___boxed(lean_object* v_a_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9(){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2748_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2749_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11));
v___x_2750_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2751_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2752_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2748_, v___x_2749_, v___x_2750_, v___x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9___boxed(lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11(){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2756_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2757_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
v___x_2758_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2759_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2760_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2756_, v___x_2757_, v___x_2758_, v___x_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11___boxed(lean_object* v_a_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
return v_res_2762_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0(void){
_start:
{
lean_object* v___x_2763_; lean_object* v___f_2764_; 
v___x_2763_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2764_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2764_, 0, v___x_2763_);
return v___f_2764_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___f_2766_; 
v___x_2765_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_2766_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2766_, 0, v___x_2765_);
return v___f_2766_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2(void){
_start:
{
lean_object* v___f_2767_; lean_object* v___f_2768_; lean_object* v___x_2769_; 
v___f_2767_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__1);
v___f_2768_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__0);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___f_2768_);
lean_ctor_set(v___x_2769_, 1, v___f_2767_);
return v___x_2769_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3(void){
_start:
{
lean_object* v___x_2770_; lean_object* v___f_2771_; 
v___x_2770_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2);
v___f_2771_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2771_, 0, v___x_2770_);
return v___f_2771_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4(void){
_start:
{
lean_object* v___x_2772_; lean_object* v___f_2773_; 
v___x_2772_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__2);
v___f_2773_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2773_, 0, v___x_2772_);
return v___f_2773_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5(void){
_start:
{
lean_object* v___f_2774_; lean_object* v___f_2775_; lean_object* v___x_2776_; 
v___f_2774_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__4);
v___f_2775_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__3);
v___x_2776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___f_2775_);
lean_ctor_set(v___x_2776_, 1, v___f_2774_);
return v___x_2776_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6(void){
_start:
{
lean_object* v___x_2777_; lean_object* v___f_2778_; 
v___x_2777_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5);
v___f_2778_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2778_, 0, v___x_2777_);
return v___f_2778_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___f_2780_; 
v___x_2779_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__5);
v___f_2780_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2780_, 0, v___x_2779_);
return v___f_2780_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8(void){
_start:
{
lean_object* v___f_2781_; lean_object* v___f_2782_; lean_object* v___x_2783_; 
v___f_2781_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__7);
v___f_2782_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__6);
v___x_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___f_2782_);
lean_ctor_set(v___x_2783_, 1, v___f_2781_);
return v___x_2783_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___f_2785_; 
v___x_2784_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8);
v___f_2785_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2785_, 0, v___x_2784_);
return v___f_2785_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___f_2787_; 
v___x_2786_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__8);
v___f_2787_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2787_, 0, v___x_2786_);
return v___f_2787_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11(void){
_start:
{
lean_object* v___f_2788_; lean_object* v___f_2789_; lean_object* v___x_2790_; 
v___f_2788_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__10);
v___f_2789_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__9);
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___f_2789_);
lean_ctor_set(v___x_2790_, 1, v___f_2788_);
return v___x_2790_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__11);
v___x_2792_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(lean_object* v_t_2793_, lean_object* v_tp_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2802_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___closed__12);
lean_inc_ref(v_tp_2794_);
v___x_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2803_, 0, v_tp_2794_);
v___x_2804_ = 1;
v___x_2805_ = lean_box(0);
v___x_2806_ = l_Lean_Elab_Term_elabTermEnsuringType(v_t_2793_, v___x_2803_, v___x_2804_, v___x_2804_, v___x_2805_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; uint8_t v___x_2815_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v___x_2815_ = l_Lean_Expr_hasSyntheticSorry(v_a_2807_);
if (v___x_2815_ == 0)
{
v___y_2809_ = v_a_2797_;
v___y_2810_ = v_a_2798_;
v___y_2811_ = v_a_2799_;
v___y_2812_ = v_a_2800_;
goto v___jp_2808_;
}
else
{
lean_object* v___x_250__overap_2816_; lean_object* v___x_2817_; 
v___x_250__overap_2816_ = l_Lean_Elab_throwAbortTerm___redArg(v___x_2802_);
lean_inc(v_a_2800_);
lean_inc_ref(v_a_2799_);
lean_inc(v_a_2798_);
lean_inc_ref(v_a_2797_);
lean_inc(v_a_2796_);
lean_inc_ref(v_a_2795_);
v___x_2817_ = lean_apply_7(v___x_250__overap_2816_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, lean_box(0));
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_dec_ref_known(v___x_2817_, 1);
v___y_2809_ = v_a_2797_;
v___y_2810_ = v_a_2798_;
v___y_2811_ = v_a_2799_;
v___y_2812_ = v_a_2800_;
goto v___jp_2808_;
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v_a_2807_);
lean_dec_ref(v_tp_2794_);
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
v___jp_2808_:
{
uint8_t v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = 1;
v___x_2814_ = l_Lean_Meta_evalExpr___redArg(v_tp_2794_, v_a_2807_, v___x_2813_, v___x_2804_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
return v___x_2814_;
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec_ref(v_tp_2794_);
v_a_2826_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2806_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2806_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___boxed(lean_object* v_t_2834_, lean_object* v_tp_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_2834_, v_tp_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg(){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
v___x_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg___boxed(lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(lean_object* v_00_u03b1_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___boxed(lean_object* v_00_u03b1_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(v_00_u03b1_2854_, v___y_2855_, v___y_2856_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
return v_res_2858_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = lean_box(0);
v___x_2860_ = l_Lean_Elab_abortTermExceptionId;
v___x_2861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
lean_ctor_set(v___x_2861_, 1, v___x_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___closed__0);
v___x_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___boxed(lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg();
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(lean_object* v_00_u03b1_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg();
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___boxed(lean_object* v_00_u03b1_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(v_00_u03b1_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(lean_object* v___y_2885_){
_start:
{
lean_object* v___x_2887_; lean_object* v_env_2888_; lean_object* v___x_2889_; lean_object* v_mainModule_2890_; lean_object* v___x_2891_; 
v___x_2887_ = lean_st_ref_get(v___y_2885_);
v_env_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc_ref(v_env_2888_);
lean_dec(v___x_2887_);
v___x_2889_ = l_Lean_Environment_header(v_env_2888_);
lean_dec_ref(v_env_2888_);
v_mainModule_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_mainModule_2890_);
lean_dec_ref(v___x_2889_);
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v_mainModule_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg___boxed(lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v___y_2892_);
lean_dec(v___y_2892_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v___y_2896_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___boxed(lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(v___y_2899_, v___y_2900_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(lean_object* v_addEntryFn_2903_, lean_object* v___x_2904_, lean_object* v_s_2905_){
_start:
{
lean_object* v_importedEntries_2906_; lean_object* v_state_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2915_; 
v_importedEntries_2906_ = lean_ctor_get(v_s_2905_, 0);
v_state_2907_ = lean_ctor_get(v_s_2905_, 1);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_s_2905_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2909_ = v_s_2905_;
v_isShared_2910_ = v_isSharedCheck_2915_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_state_2907_);
lean_inc(v_importedEntries_2906_);
lean_dec(v_s_2905_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2915_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v_state_2911_; lean_object* v___x_2913_; 
v_state_2911_ = lean_apply_2(v_addEntryFn_2903_, v_state_2907_, v___x_2904_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v_state_2911_);
v___x_2913_ = v___x_2909_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_importedEntries_2906_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_state_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__1(lean_object* v___x_2916_, lean_object* v___x_2917_, uint8_t v___x_2918_, lean_object* v_x_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
lean_inc_ref(v___x_2916_);
v___x_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2916_);
v___x_2928_ = lean_box(0);
v___x_2929_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_2917_, v___x_2927_, v___x_2918_, v___x_2918_, v___x_2928_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; uint8_t v___x_2938_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref_known(v___x_2929_, 1);
v___x_2938_ = l_Lean_Expr_hasSyntheticSorry(v_a_2930_);
if (v___x_2938_ == 0)
{
v___y_2932_ = v___y_2922_;
v___y_2933_ = v___y_2923_;
v___y_2934_ = v___y_2924_;
v___y_2935_ = v___y_2925_;
goto v___jp_2931_;
}
else
{
lean_object* v___x_2939_; lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec(v_a_2930_);
lean_dec_ref(v___x_2916_);
v___x_2939_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg();
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
v___jp_2931_:
{
uint8_t v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = 1;
v___x_2937_ = l_Lean_Meta_evalExpr___redArg(v___x_2916_, v_a_2930_, v___x_2936_, v___x_2918_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
return v___x_2937_;
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec_ref(v___x_2916_);
v_a_2948_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2929_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2929_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__1___boxed(lean_object* v___x_2956_, lean_object* v___x_2957_, lean_object* v___x_2958_, lean_object* v_x_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
uint8_t v___x_9373__boxed_2967_; lean_object* v_res_2968_; 
v___x_9373__boxed_2967_ = lean_unbox(v___x_2958_);
v_res_2968_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__1(v___x_2956_, v___x_2957_, v___x_9373__boxed_2967_, v_x_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v_x_2959_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg(lean_object* v_msgData_2969_, lean_object* v_macroStack_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v_scopes_2975_; lean_object* v___x_2976_; lean_object* v_opts_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2973_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2974_ = lean_st_ref_get(v___y_2971_);
v_scopes_2975_ = lean_ctor_get(v___x_2974_, 2);
lean_inc(v_scopes_2975_);
lean_dec(v___x_2974_);
v___x_2976_ = l_List_head_x21___redArg(v___x_2973_, v_scopes_2975_);
lean_dec(v_scopes_2975_);
v_opts_2977_ = lean_ctor_get(v___x_2976_, 1);
lean_inc_ref(v_opts_2977_);
lean_dec(v___x_2976_);
v___x_2978_ = l_Lean_Elab_pp_macroStack;
v___x_2979_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_2977_, v___x_2978_);
lean_dec_ref(v_opts_2977_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; 
lean_dec(v_macroStack_2970_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_msgData_2969_);
return v___x_2980_;
}
else
{
if (lean_obj_tag(v_macroStack_2970_) == 0)
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_msgData_2969_);
return v___x_2981_;
}
else
{
lean_object* v_head_2982_; lean_object* v_after_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2998_; 
v_head_2982_ = lean_ctor_get(v_macroStack_2970_, 0);
lean_inc(v_head_2982_);
v_after_2983_ = lean_ctor_get(v_head_2982_, 1);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_head_2982_);
if (v_isSharedCheck_2998_ == 0)
{
lean_object* v_unused_2999_; 
v_unused_2999_ = lean_ctor_get(v_head_2982_, 0);
lean_dec(v_unused_2999_);
v___x_2985_ = v_head_2982_;
v_isShared_2986_ = v_isSharedCheck_2998_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_after_2983_);
lean_dec(v_head_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2998_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2987_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_2986_ == 0)
{
lean_ctor_set_tag(v___x_2985_, 7);
lean_ctor_set(v___x_2985_, 1, v___x_2987_);
lean_ctor_set(v___x_2985_, 0, v_msgData_2969_);
v___x_2989_ = v___x_2985_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_msgData_2969_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v_msgData_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2990_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
v___x_2991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2989_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
v___x_2992_ = l_Lean_MessageData_ofSyntax(v_after_2983_);
v___x_2993_ = l_Lean_indentD(v___x_2992_);
v_msgData_2994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2994_, 0, v___x_2991_);
lean_ctor_set(v_msgData_2994_, 1, v___x_2993_);
v___x_2995_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_2994_, v_macroStack_2970_);
v___x_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
return v___x_2996_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg___boxed(lean_object* v_msgData_3000_, lean_object* v_macroStack_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg(v_msgData_3000_, v_macroStack_3001_, v___y_3002_);
lean_dec(v___y_3002_);
return v_res_3004_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0);
v___x_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
return v___x_3006_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3007_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3008_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0);
v___x_3009_ = lean_unsigned_to_nat(0u);
v___x_3010_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
lean_ctor_set(v___x_3010_, 2, v___x_3009_);
lean_ctor_set(v___x_3010_, 3, v___x_3009_);
lean_ctor_set(v___x_3010_, 4, v___x_3008_);
lean_ctor_set(v___x_3010_, 5, v___x_3008_);
lean_ctor_set(v___x_3010_, 6, v___x_3008_);
lean_ctor_set(v___x_3010_, 7, v___x_3008_);
lean_ctor_set(v___x_3010_, 8, v___x_3008_);
lean_ctor_set(v___x_3010_, 9, v___x_3008_);
lean_ctor_set(v___x_3010_, 10, v___x_3008_);
lean_ctor_set(v___x_3010_, 11, v___x_3007_);
return v___x_3010_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = lean_unsigned_to_nat(32u);
v___x_3012_ = lean_mk_empty_array_with_capacity(v___x_3011_);
v___x_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
return v___x_3013_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3(void){
_start:
{
size_t v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3014_ = ((size_t)5ULL);
v___x_3015_ = lean_unsigned_to_nat(0u);
v___x_3016_ = lean_unsigned_to_nat(32u);
v___x_3017_ = lean_mk_empty_array_with_capacity(v___x_3016_);
v___x_3018_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__2);
v___x_3019_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v___x_3017_);
lean_ctor_set(v___x_3019_, 2, v___x_3015_);
lean_ctor_set(v___x_3019_, 3, v___x_3015_);
lean_ctor_set_usize(v___x_3019_, 4, v___x_3014_);
return v___x_3019_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3020_ = lean_box(1);
v___x_3021_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__3);
v___x_3022_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__0);
v___x_3023_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
lean_ctor_set(v___x_3023_, 1, v___x_3021_);
lean_ctor_set(v___x_3023_, 2, v___x_3020_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg(lean_object* v_msgData_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v___x_3027_; lean_object* v_env_3028_; uint8_t v___x_3029_; lean_object* v_env_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v_scopes_3033_; lean_object* v___x_3034_; lean_object* v_opts_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3027_ = lean_st_ref_get(v___y_3025_);
v_env_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc_ref(v_env_3028_);
lean_dec(v___x_3027_);
v___x_3029_ = 0;
v_env_3030_ = l_Lean_Environment_setRecordingDeps(v_env_3028_, v___x_3029_);
v___x_3031_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3032_ = lean_st_ref_get(v___y_3025_);
v_scopes_3033_ = lean_ctor_get(v___x_3032_, 2);
lean_inc(v_scopes_3033_);
lean_dec(v___x_3032_);
v___x_3034_ = l_List_head_x21___redArg(v___x_3031_, v_scopes_3033_);
lean_dec(v_scopes_3033_);
v_opts_3035_ = lean_ctor_get(v___x_3034_, 1);
lean_inc_ref(v_opts_3035_);
lean_dec(v___x_3034_);
v___x_3036_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__1);
v___x_3037_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___closed__4);
v___x_3038_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3038_, 0, v_env_3030_);
lean_ctor_set(v___x_3038_, 1, v___x_3036_);
lean_ctor_set(v___x_3038_, 2, v___x_3037_);
lean_ctor_set(v___x_3038_, 3, v_opts_3035_);
v___x_3039_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v_msgData_3024_);
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg___boxed(lean_object* v_msgData_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg(v_msgData_3041_, v___y_3042_);
lean_dec(v___y_3042_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg(lean_object* v_msg_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_Elab_Command_getRef___redArg(v___y_3046_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v_macroStack_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v_a_3054_; lean_object* v___x_3055_; lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3064_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref_known(v___x_3049_, 1);
v_macroStack_3051_ = lean_ctor_get(v___y_3046_, 4);
v___x_3052_ = l_Lean_Elab_getBetterRef(v_a_3050_, v_macroStack_3051_);
lean_dec(v_a_3050_);
v___x_3053_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg(v_msg_3045_, v___y_3047_);
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref(v___x_3053_);
lean_inc(v_macroStack_3051_);
v___x_3055_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg(v_a_3054_, v_macroStack_3051_, v___y_3047_);
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3058_ = v___x_3055_;
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3052_);
lean_ctor_set(v___x_3060_, 1, v_a_3056_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set_tag(v___x_3058_, 1);
lean_ctor_set(v___x_3058_, 0, v___x_3060_);
v___x_3062_ = v___x_3058_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec_ref(v_msg_3045_);
v_a_3065_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3049_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3049_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg___boxed(lean_object* v_msg_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg(v_msg_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(lean_object* v_ref_3078_, lean_object* v_msg_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_Elab_Command_getRef___redArg(v___y_3080_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v_fileName_3085_; lean_object* v_fileMap_3086_; lean_object* v_currRecDepth_3087_; lean_object* v_cmdPos_3088_; lean_object* v_macroStack_3089_; lean_object* v_quotContext_x3f_3090_; lean_object* v_currMacroScope_3091_; lean_object* v_snap_x3f_3092_; lean_object* v_cancelTk_x3f_3093_; uint8_t v_suppressElabErrors_3094_; lean_object* v_ref_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
v_fileName_3085_ = lean_ctor_get(v___y_3080_, 0);
v_fileMap_3086_ = lean_ctor_get(v___y_3080_, 1);
v_currRecDepth_3087_ = lean_ctor_get(v___y_3080_, 2);
v_cmdPos_3088_ = lean_ctor_get(v___y_3080_, 3);
v_macroStack_3089_ = lean_ctor_get(v___y_3080_, 4);
v_quotContext_x3f_3090_ = lean_ctor_get(v___y_3080_, 5);
v_currMacroScope_3091_ = lean_ctor_get(v___y_3080_, 6);
v_snap_x3f_3092_ = lean_ctor_get(v___y_3080_, 8);
v_cancelTk_x3f_3093_ = lean_ctor_get(v___y_3080_, 9);
v_suppressElabErrors_3094_ = lean_ctor_get_uint8(v___y_3080_, sizeof(void*)*10);
v_ref_3095_ = l_Lean_replaceRef(v_ref_3078_, v_a_3084_);
lean_dec(v_a_3084_);
lean_inc(v_cancelTk_x3f_3093_);
lean_inc(v_snap_x3f_3092_);
lean_inc(v_currMacroScope_3091_);
lean_inc(v_quotContext_x3f_3090_);
lean_inc(v_macroStack_3089_);
lean_inc(v_cmdPos_3088_);
lean_inc(v_currRecDepth_3087_);
lean_inc_ref(v_fileMap_3086_);
lean_inc_ref(v_fileName_3085_);
v___x_3096_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3096_, 0, v_fileName_3085_);
lean_ctor_set(v___x_3096_, 1, v_fileMap_3086_);
lean_ctor_set(v___x_3096_, 2, v_currRecDepth_3087_);
lean_ctor_set(v___x_3096_, 3, v_cmdPos_3088_);
lean_ctor_set(v___x_3096_, 4, v_macroStack_3089_);
lean_ctor_set(v___x_3096_, 5, v_quotContext_x3f_3090_);
lean_ctor_set(v___x_3096_, 6, v_currMacroScope_3091_);
lean_ctor_set(v___x_3096_, 7, v_ref_3095_);
lean_ctor_set(v___x_3096_, 8, v_snap_x3f_3092_);
lean_ctor_set(v___x_3096_, 9, v_cancelTk_x3f_3093_);
lean_ctor_set_uint8(v___x_3096_, sizeof(void*)*10, v_suppressElabErrors_3094_);
v___x_3097_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg(v_msg_3079_, v___x_3096_, v___y_3081_);
lean_dec_ref_known(v___x_3096_, 10);
return v___x_3097_;
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec_ref(v_msg_3079_);
v_a_3098_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3083_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3083_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg___boxed(lean_object* v_ref_3106_, lean_object* v_msg_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_ref_3106_, v_msg_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v_ref_3106_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4(lean_object* v_cls_3112_, lean_object* v_msg_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_Elab_Command_getRef___redArg(v___y_3114_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3119_; lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3168_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
v___x_3119_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg(v_msg_3113_, v___y_3115_);
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3122_ = v___x_3119_;
v_isShared_3123_ = v_isSharedCheck_3168_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3119_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3168_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v_traceState_3125_; lean_object* v_env_3126_; lean_object* v_messages_3127_; lean_object* v_scopes_3128_; lean_object* v_usedQuotCtxts_3129_; lean_object* v_nextMacroScope_3130_; lean_object* v_maxRecDepth_3131_; lean_object* v_ngen_3132_; lean_object* v_auxDeclNGen_3133_; lean_object* v_infoState_3134_; lean_object* v_snapshotTasks_3135_; lean_object* v_prevLinterStates_3136_; lean_object* v_codeQualityEntryTasks_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3167_; 
v___x_3124_ = lean_st_ref_take(v___y_3115_);
v_traceState_3125_ = lean_ctor_get(v___x_3124_, 9);
v_env_3126_ = lean_ctor_get(v___x_3124_, 0);
v_messages_3127_ = lean_ctor_get(v___x_3124_, 1);
v_scopes_3128_ = lean_ctor_get(v___x_3124_, 2);
v_usedQuotCtxts_3129_ = lean_ctor_get(v___x_3124_, 3);
v_nextMacroScope_3130_ = lean_ctor_get(v___x_3124_, 4);
v_maxRecDepth_3131_ = lean_ctor_get(v___x_3124_, 5);
v_ngen_3132_ = lean_ctor_get(v___x_3124_, 6);
v_auxDeclNGen_3133_ = lean_ctor_get(v___x_3124_, 7);
v_infoState_3134_ = lean_ctor_get(v___x_3124_, 8);
v_snapshotTasks_3135_ = lean_ctor_get(v___x_3124_, 10);
v_prevLinterStates_3136_ = lean_ctor_get(v___x_3124_, 11);
v_codeQualityEntryTasks_3137_ = lean_ctor_get(v___x_3124_, 12);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3139_ = v___x_3124_;
v_isShared_3140_ = v_isSharedCheck_3167_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_codeQualityEntryTasks_3137_);
lean_inc(v_prevLinterStates_3136_);
lean_inc(v_snapshotTasks_3135_);
lean_inc(v_traceState_3125_);
lean_inc(v_infoState_3134_);
lean_inc(v_auxDeclNGen_3133_);
lean_inc(v_ngen_3132_);
lean_inc(v_maxRecDepth_3131_);
lean_inc(v_nextMacroScope_3130_);
lean_inc(v_usedQuotCtxts_3129_);
lean_inc(v_scopes_3128_);
lean_inc(v_messages_3127_);
lean_inc(v_env_3126_);
lean_dec(v___x_3124_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3167_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
uint64_t v_tid_3141_; lean_object* v_traces_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3166_; 
v_tid_3141_ = lean_ctor_get_uint64(v_traceState_3125_, sizeof(void*)*1);
v_traces_3142_ = lean_ctor_get(v_traceState_3125_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_traceState_3125_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3144_ = v_traceState_3125_;
v_isShared_3145_ = v_isSharedCheck_3166_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_traces_3142_);
lean_dec(v_traceState_3125_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3166_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; double v___x_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_box(0);
v___x_3148_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
v___x_3149_ = 0;
v___x_3150_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_3151_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3151_, 0, v_cls_3112_);
lean_ctor_set(v___x_3151_, 1, v___x_3147_);
lean_ctor_set(v___x_3151_, 2, v___x_3150_);
lean_ctor_set_float(v___x_3151_, sizeof(void*)*3, v___x_3148_);
lean_ctor_set_float(v___x_3151_, sizeof(void*)*3 + 8, v___x_3148_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*3 + 16, v___x_3149_);
v___x_3152_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2));
v___x_3153_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3151_);
lean_ctor_set(v___x_3153_, 1, v_a_3120_);
lean_ctor_set(v___x_3153_, 2, v___x_3152_);
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v_a_3118_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = l_Lean_PersistentArray_push___redArg(v_traces_3142_, v___x_3154_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3155_);
v___x_3157_ = v___x_3144_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3155_);
lean_ctor_set_uint64(v_reuseFailAlloc_3165_, sizeof(void*)*1, v_tid_3141_);
v___x_3157_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3159_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 9, v___x_3157_);
v___x_3159_ = v___x_3139_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_env_3126_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_messages_3127_);
lean_ctor_set(v_reuseFailAlloc_3164_, 2, v_scopes_3128_);
lean_ctor_set(v_reuseFailAlloc_3164_, 3, v_usedQuotCtxts_3129_);
lean_ctor_set(v_reuseFailAlloc_3164_, 4, v_nextMacroScope_3130_);
lean_ctor_set(v_reuseFailAlloc_3164_, 5, v_maxRecDepth_3131_);
lean_ctor_set(v_reuseFailAlloc_3164_, 6, v_ngen_3132_);
lean_ctor_set(v_reuseFailAlloc_3164_, 7, v_auxDeclNGen_3133_);
lean_ctor_set(v_reuseFailAlloc_3164_, 8, v_infoState_3134_);
lean_ctor_set(v_reuseFailAlloc_3164_, 9, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3164_, 10, v_snapshotTasks_3135_);
lean_ctor_set(v_reuseFailAlloc_3164_, 11, v_prevLinterStates_3136_);
lean_ctor_set(v_reuseFailAlloc_3164_, 12, v_codeQualityEntryTasks_3137_);
v___x_3159_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3160_ = lean_st_ref_put(v___y_3115_, v___x_3159_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3146_);
v___x_3162_ = v___x_3122_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3146_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec_ref(v_msg_3113_);
lean_dec(v_cls_3112_);
v_a_3169_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3117_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3117_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4___boxed(lean_object* v_cls_3177_, lean_object* v_msg_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4(v_cls_3177_, v_msg_3178_, v___y_3179_, v___y_3180_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(lean_object* v_mod_3183_, uint8_t v_isMeta_3184_, lean_object* v_hint_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v_env_3210_; uint8_t v_isExporting_3211_; lean_object* v_entry_3212_; lean_object* v___x_3213_; lean_object* v_env_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v___x_3208_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
v___x_3209_ = lean_st_ref_get(v___y_3187_);
v_env_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc_ref(v_env_3210_);
lean_dec(v___x_3209_);
v_isExporting_3211_ = lean_ctor_get_uint8(v_env_3210_, sizeof(void*)*13);
lean_dec_ref(v_env_3210_);
lean_inc(v_mod_3183_);
v_entry_3212_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3212_, 0, v_mod_3183_);
lean_ctor_set_uint8(v_entry_3212_, sizeof(void*)*1, v_isExporting_3211_);
lean_ctor_set_uint8(v_entry_3212_, sizeof(void*)*1 + 1, v_isMeta_3184_);
v___x_3213_ = lean_st_ref_get(v___y_3187_);
v_env_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc_ref(v_env_3214_);
lean_dec(v___x_3213_);
v___x_3215_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3216_ = lean_box(1);
v___x_3217_ = lean_box(0);
v___x_3218_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3208_, v___x_3215_, v_env_3214_, v___x_3216_, v___x_3217_);
v___x_3219_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_3218_, v_entry_3212_);
lean_dec(v___x_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___f_3220_; uint8_t v___x_3221_; lean_object* v___y_3223_; lean_object* v_cls_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v_scopes_3269_; lean_object* v___x_3270_; lean_object* v_opts_3271_; uint8_t v_hasTrace_3272_; 
v___f_3220_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___lam__0), 3, 2);
lean_closure_set(v___f_3220_, 0, v___x_3215_);
lean_closure_set(v___f_3220_, 1, v_entry_3212_);
v___x_3221_ = 1;
v_cls_3245_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6));
v___x_3246_ = l_Lean_inheritedTraceOptions;
v___x_3247_ = lean_st_ref_get(v___x_3246_);
v___x_3248_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3249_ = lean_st_ref_get(v___y_3187_);
v_scopes_3269_ = lean_ctor_get(v___x_3249_, 2);
lean_inc(v_scopes_3269_);
lean_dec(v___x_3249_);
v___x_3270_ = l_List_head_x21___redArg(v___x_3248_, v_scopes_3269_);
lean_dec(v_scopes_3269_);
v_opts_3271_ = lean_ctor_get(v___x_3270_, 1);
lean_inc_ref(v_opts_3271_);
lean_dec(v___x_3270_);
v_hasTrace_3272_ = lean_ctor_get_uint8(v_opts_3271_, sizeof(void*)*1);
if (v_hasTrace_3272_ == 0)
{
lean_dec_ref(v_opts_3271_);
lean_dec(v___x_3247_);
lean_dec(v_hint_3185_);
lean_dec(v_mod_3183_);
v___y_3223_ = v___y_3187_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
v___x_3274_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3247_, v_opts_3271_, v___x_3273_);
lean_dec_ref(v_opts_3271_);
lean_dec(v___x_3247_);
if (v___x_3274_ == 0)
{
lean_dec(v_hint_3185_);
lean_dec(v_mod_3183_);
v___y_3223_ = v___y_3187_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3275_; lean_object* v___y_3277_; 
v___x_3275_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
if (v_isExporting_3211_ == 0)
{
lean_object* v___x_3284_; 
v___x_3284_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19));
v___y_3277_ = v___x_3284_;
goto v___jp_3276_;
}
else
{
lean_object* v___x_3285_; 
v___x_3285_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20));
v___y_3277_ = v___x_3285_;
goto v___jp_3276_;
}
v___jp_3276_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_inc_ref(v___y_3277_);
v___x_3278_ = l_Lean_stringToMessageData(v___y_3277_);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3275_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
if (v_isMeta_3184_ == 0)
{
lean_object* v___x_3282_; 
v___x_3282_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17));
v___y_3256_ = v___x_3281_;
v___y_3257_ = v___x_3282_;
goto v___jp_3255_;
}
else
{
lean_object* v___x_3283_; 
v___x_3283_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18));
v___y_3256_ = v___x_3281_;
v___y_3257_ = v___x_3283_;
goto v___jp_3255_;
}
}
}
}
v___jp_3222_:
{
lean_object* v___x_3224_; lean_object* v_toEnvExtension_3225_; lean_object* v_env_3226_; lean_object* v_messages_3227_; lean_object* v_scopes_3228_; lean_object* v_usedQuotCtxts_3229_; lean_object* v_nextMacroScope_3230_; lean_object* v_maxRecDepth_3231_; lean_object* v_ngen_3232_; lean_object* v_auxDeclNGen_3233_; lean_object* v_infoState_3234_; lean_object* v_traceState_3235_; lean_object* v_snapshotTasks_3236_; lean_object* v_prevLinterStates_3237_; lean_object* v_codeQualityEntryTasks_3238_; lean_object* v_asyncMode_3239_; uint8_t v_logWrites_3240_; lean_object* v___x_3241_; 
v___x_3224_ = lean_st_ref_take(v___y_3223_);
v_toEnvExtension_3225_ = lean_ctor_get(v___x_3215_, 0);
v_env_3226_ = lean_ctor_get(v___x_3224_, 0);
lean_inc_ref(v_env_3226_);
v_messages_3227_ = lean_ctor_get(v___x_3224_, 1);
lean_inc_ref(v_messages_3227_);
v_scopes_3228_ = lean_ctor_get(v___x_3224_, 2);
lean_inc(v_scopes_3228_);
v_usedQuotCtxts_3229_ = lean_ctor_get(v___x_3224_, 3);
lean_inc(v_usedQuotCtxts_3229_);
v_nextMacroScope_3230_ = lean_ctor_get(v___x_3224_, 4);
lean_inc(v_nextMacroScope_3230_);
v_maxRecDepth_3231_ = lean_ctor_get(v___x_3224_, 5);
lean_inc(v_maxRecDepth_3231_);
v_ngen_3232_ = lean_ctor_get(v___x_3224_, 6);
lean_inc_ref(v_ngen_3232_);
v_auxDeclNGen_3233_ = lean_ctor_get(v___x_3224_, 7);
lean_inc_ref(v_auxDeclNGen_3233_);
v_infoState_3234_ = lean_ctor_get(v___x_3224_, 8);
lean_inc_ref(v_infoState_3234_);
v_traceState_3235_ = lean_ctor_get(v___x_3224_, 9);
lean_inc_ref(v_traceState_3235_);
v_snapshotTasks_3236_ = lean_ctor_get(v___x_3224_, 10);
lean_inc_ref(v_snapshotTasks_3236_);
v_prevLinterStates_3237_ = lean_ctor_get(v___x_3224_, 11);
lean_inc(v_prevLinterStates_3237_);
v_codeQualityEntryTasks_3238_ = lean_ctor_get(v___x_3224_, 12);
lean_inc_ref(v_codeQualityEntryTasks_3238_);
lean_dec(v___x_3224_);
v_asyncMode_3239_ = lean_ctor_get(v_toEnvExtension_3225_, 2);
v_logWrites_3240_ = lean_ctor_get_uint8(v_toEnvExtension_3225_, sizeof(void*)*6);
v___x_3241_ = lean_box(0);
if (v_logWrites_3240_ == 0)
{
lean_object* v___x_3242_; 
lean_inc_ref(v_toEnvExtension_3225_);
v___x_3242_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3225_, v_env_3226_, v___f_3220_, v_asyncMode_3239_, v___x_3217_, v___x_3221_);
v___y_3190_ = v_codeQualityEntryTasks_3238_;
v___y_3191_ = v_infoState_3234_;
v___y_3192_ = v_scopes_3228_;
v___y_3193_ = v_nextMacroScope_3230_;
v___y_3194_ = v___x_3241_;
v___y_3195_ = v_messages_3227_;
v___y_3196_ = v___y_3223_;
v___y_3197_ = v_usedQuotCtxts_3229_;
v___y_3198_ = v_prevLinterStates_3237_;
v___y_3199_ = v_traceState_3235_;
v___y_3200_ = v_auxDeclNGen_3233_;
v___y_3201_ = v_ngen_3232_;
v___y_3202_ = v_maxRecDepth_3231_;
v___y_3203_ = v_snapshotTasks_3236_;
v___y_3204_ = v___x_3242_;
goto v___jp_3189_;
}
else
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
lean_inc_ref_n(v_toEnvExtension_3225_, 2);
v___x_3243_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3225_, v_env_3226_);
lean_dec_ref(v_env_3226_);
v___x_3244_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3225_, v___x_3243_, v___f_3220_, v_asyncMode_3239_, v___x_3217_, v___x_3221_);
v___y_3190_ = v_codeQualityEntryTasks_3238_;
v___y_3191_ = v_infoState_3234_;
v___y_3192_ = v_scopes_3228_;
v___y_3193_ = v_nextMacroScope_3230_;
v___y_3194_ = v___x_3241_;
v___y_3195_ = v_messages_3227_;
v___y_3196_ = v___y_3223_;
v___y_3197_ = v_usedQuotCtxts_3229_;
v___y_3198_ = v_prevLinterStates_3237_;
v___y_3199_ = v_traceState_3235_;
v___y_3200_ = v_auxDeclNGen_3233_;
v___y_3201_ = v_ngen_3232_;
v___y_3202_ = v_maxRecDepth_3231_;
v___y_3203_ = v_snapshotTasks_3236_;
v___y_3204_ = v___x_3244_;
goto v___jp_3189_;
}
}
v___jp_3250_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___y_3251_);
lean_ctor_set(v___x_3253_, 1, v___y_3252_);
v___x_3254_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__4(v_cls_3245_, v___x_3253_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_dec_ref_known(v___x_3254_, 1);
v___y_3223_ = v___y_3187_;
goto v___jp_3222_;
}
else
{
lean_dec_ref(v___f_3220_);
return v___x_3254_;
}
}
v___jp_3255_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
lean_inc_ref(v___y_3257_);
v___x_3258_ = l_Lean_stringToMessageData(v___y_3257_);
v___x_3259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___y_3256_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8);
v___x_3261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3259_);
lean_ctor_set(v___x_3261_, 1, v___x_3260_);
v___x_3262_ = l_Lean_MessageData_ofName(v_mod_3183_);
v___x_3263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3261_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = l_Lean_Name_isAnonymous(v_hint_3185_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
v___x_3266_ = l_Lean_MessageData_ofName(v_hint_3185_);
v___x_3267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3265_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___y_3251_ = v___x_3263_;
v___y_3252_ = v___x_3267_;
goto v___jp_3250_;
}
else
{
lean_object* v___x_3268_; 
lean_dec(v_hint_3185_);
v___x_3268_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11);
v___y_3251_ = v___x_3263_;
v___y_3252_ = v___x_3268_;
goto v___jp_3250_;
}
}
}
else
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
lean_dec_ref_known(v_entry_3212_, 1);
lean_dec(v_hint_3185_);
lean_dec(v_mod_3183_);
v___x_3286_ = lean_box(0);
v___x_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
return v___x_3287_;
}
v___jp_3189_:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_3205_, 0, v___y_3204_);
lean_ctor_set(v___x_3205_, 1, v___y_3195_);
lean_ctor_set(v___x_3205_, 2, v___y_3192_);
lean_ctor_set(v___x_3205_, 3, v___y_3197_);
lean_ctor_set(v___x_3205_, 4, v___y_3193_);
lean_ctor_set(v___x_3205_, 5, v___y_3202_);
lean_ctor_set(v___x_3205_, 6, v___y_3201_);
lean_ctor_set(v___x_3205_, 7, v___y_3200_);
lean_ctor_set(v___x_3205_, 8, v___y_3191_);
lean_ctor_set(v___x_3205_, 9, v___y_3199_);
lean_ctor_set(v___x_3205_, 10, v___y_3203_);
lean_ctor_set(v___x_3205_, 11, v___y_3198_);
lean_ctor_set(v___x_3205_, 12, v___y_3190_);
v___x_3206_ = lean_st_ref_put(v___y_3196_, v___x_3205_);
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___y_3194_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1___boxed(lean_object* v_mod_3288_, lean_object* v_isMeta_3289_, lean_object* v_hint_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
uint8_t v_isMeta_boxed_3294_; lean_object* v_res_3295_; 
v_isMeta_boxed_3294_ = lean_unbox(v_isMeta_3289_);
v_res_3295_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_mod_3288_, v_isMeta_boxed_3294_, v_hint_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(lean_object* v___x_3296_, lean_object* v_declName_3297_, lean_object* v_as_3298_, size_t v_sz_3299_, size_t v_i_3300_, lean_object* v_b_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
uint8_t v___x_3305_; 
v___x_3305_ = lean_usize_dec_lt(v_i_3300_, v_sz_3299_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; 
lean_dec(v_declName_3297_);
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v_b_3301_);
return v___x_3306_;
}
else
{
lean_object* v___x_3307_; lean_object* v_modules_3308_; lean_object* v___x_3309_; lean_object* v_a_3310_; lean_object* v___x_3311_; lean_object* v_toImport_3312_; lean_object* v_module_3313_; lean_object* v___x_3314_; uint8_t v___x_3315_; lean_object* v___x_3316_; 
v___x_3307_ = l_Lean_Environment_header(v___x_3296_);
v_modules_3308_ = lean_ctor_get(v___x_3307_, 3);
lean_inc_ref(v_modules_3308_);
lean_dec_ref(v___x_3307_);
v___x_3309_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3310_ = lean_array_uget_borrowed(v_as_3298_, v_i_3300_);
v___x_3311_ = lean_array_get(v___x_3309_, v_modules_3308_, v_a_3310_);
lean_dec_ref(v_modules_3308_);
v_toImport_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc_ref(v_toImport_3312_);
lean_dec(v___x_3311_);
v_module_3313_ = lean_ctor_get(v_toImport_3312_, 0);
lean_inc(v_module_3313_);
lean_dec_ref(v_toImport_3312_);
v___x_3314_ = lean_box(0);
v___x_3315_ = 0;
lean_inc(v_declName_3297_);
v___x_3316_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_3313_, v___x_3315_, v_declName_3297_, v___y_3302_, v___y_3303_);
if (lean_obj_tag(v___x_3316_) == 0)
{
size_t v___x_3317_; size_t v___x_3318_; 
lean_dec_ref_known(v___x_3316_, 1);
v___x_3317_ = ((size_t)1ULL);
v___x_3318_ = lean_usize_add(v_i_3300_, v___x_3317_);
v_i_3300_ = v___x_3318_;
v_b_3301_ = v___x_3314_;
goto _start;
}
else
{
lean_dec(v_declName_3297_);
return v___x_3316_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2___boxed(lean_object* v___x_3320_, lean_object* v_declName_3321_, lean_object* v_as_3322_, lean_object* v_sz_3323_, lean_object* v_i_3324_, lean_object* v_b_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
size_t v_sz_boxed_3329_; size_t v_i_boxed_3330_; lean_object* v_res_3331_; 
v_sz_boxed_3329_ = lean_unbox_usize(v_sz_3323_);
lean_dec(v_sz_3323_);
v_i_boxed_3330_ = lean_unbox_usize(v_i_3324_);
lean_dec(v_i_3324_);
v_res_3331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v___x_3320_, v_declName_3321_, v_as_3322_, v_sz_boxed_3329_, v_i_boxed_3330_, v_b_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec_ref(v_as_3322_);
lean_dec_ref(v___x_3320_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(lean_object* v_declName_3332_, uint8_t v_isMeta_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v_env_3342_; lean_object* v___y_3344_; lean_object* v___x_3357_; 
v___x_3337_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0);
v___x_3338_ = lean_st_ref_get(v___y_3335_);
v_env_3342_ = lean_ctor_get(v___x_3338_, 0);
lean_inc_ref(v_env_3342_);
lean_dec(v___x_3338_);
v___x_3357_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3342_, v_declName_3332_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_dec_ref(v_env_3342_);
lean_dec(v_declName_3332_);
goto v___jp_3339_;
}
else
{
lean_object* v_val_3358_; lean_object* v___x_3359_; lean_object* v_modules_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v_val_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_val_3358_);
lean_dec_ref_known(v___x_3357_, 1);
v___x_3359_ = l_Lean_Environment_header(v_env_3342_);
v_modules_3360_ = lean_ctor_get(v___x_3359_, 3);
lean_inc_ref(v_modules_3360_);
lean_dec_ref(v___x_3359_);
v___x_3361_ = lean_array_get_size(v_modules_3360_);
v___x_3362_ = lean_nat_dec_lt(v_val_3358_, v___x_3361_);
if (v___x_3362_ == 0)
{
lean_dec_ref(v_modules_3360_);
lean_dec(v_val_3358_);
lean_dec_ref(v_env_3342_);
lean_dec(v_declName_3332_);
goto v___jp_3339_;
}
else
{
lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___y_3366_; 
v___x_3363_ = lean_array_fget(v_modules_3360_, v_val_3358_);
lean_dec(v_val_3358_);
lean_dec_ref(v_modules_3360_);
v___x_3364_ = lean_st_ref_get(v___y_3335_);
if (v_isMeta_3333_ == 0)
{
lean_dec(v___x_3364_);
v___y_3366_ = v_isMeta_3333_;
goto v___jp_3365_;
}
else
{
lean_object* v_env_3377_; uint8_t v___x_3378_; 
v_env_3377_ = lean_ctor_get(v___x_3364_, 0);
lean_inc_ref(v_env_3377_);
lean_dec(v___x_3364_);
lean_inc(v_declName_3332_);
v___x_3378_ = l_Lean_isMarkedMeta(v_env_3377_, v_declName_3332_);
if (v___x_3378_ == 0)
{
v___y_3366_ = v_isMeta_3333_;
goto v___jp_3365_;
}
else
{
uint8_t v___x_3379_; 
v___x_3379_ = 0;
v___y_3366_ = v___x_3379_;
goto v___jp_3365_;
}
}
v___jp_3365_:
{
lean_object* v_toImport_3367_; lean_object* v_module_3368_; lean_object* v___x_3369_; 
v_toImport_3367_ = lean_ctor_get(v___x_3363_, 0);
lean_inc_ref(v_toImport_3367_);
lean_dec(v___x_3363_);
v_module_3368_ = lean_ctor_get(v_toImport_3367_, 0);
lean_inc(v_module_3368_);
lean_dec_ref(v_toImport_3367_);
lean_inc(v_declName_3332_);
v___x_3369_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_3368_, v___y_3366_, v_declName_3332_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
lean_dec_ref_known(v___x_3369_, 1);
v___x_3370_ = l_Lean_indirectModUseExt;
v___x_3371_ = lean_box(1);
v___x_3372_ = lean_box(0);
lean_inc_ref(v_env_3342_);
v___x_3373_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3337_, v___x_3370_, v_env_3342_, v___x_3371_, v___x_3372_);
v___x_3374_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_3373_, v_declName_3332_);
lean_dec(v___x_3373_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v___x_3375_; 
v___x_3375_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1));
v___y_3344_ = v___x_3375_;
goto v___jp_3343_;
}
else
{
lean_object* v_val_3376_; 
v_val_3376_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_val_3376_);
lean_dec_ref_known(v___x_3374_, 1);
v___y_3344_ = v_val_3376_;
goto v___jp_3343_;
}
}
else
{
lean_dec_ref(v_env_3342_);
lean_dec(v_declName_3332_);
return v___x_3369_;
}
}
}
}
v___jp_3339_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
return v___x_3341_;
}
v___jp_3343_:
{
lean_object* v___x_3345_; size_t v_sz_3346_; size_t v___x_3347_; lean_object* v___x_3348_; 
v___x_3345_ = lean_box(0);
v_sz_3346_ = lean_array_size(v___y_3344_);
v___x_3347_ = ((size_t)0ULL);
v___x_3348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v_env_3342_, v_declName_3332_, v___y_3344_, v_sz_3346_, v___x_3347_, v___x_3345_, v___y_3334_, v___y_3335_);
lean_dec_ref(v___y_3344_);
lean_dec_ref(v_env_3342_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3355_ == 0)
{
lean_object* v_unused_3356_; 
v_unused_3356_ = lean_ctor_get(v___x_3348_, 0);
lean_dec(v_unused_3356_);
v___x_3350_ = v___x_3348_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_dec(v___x_3348_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v___x_3345_);
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3345_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
else
{
return v___x_3348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1___boxed(lean_object* v_declName_3380_, lean_object* v_isMeta_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
uint8_t v_isMeta_boxed_3385_; lean_object* v_res_3386_; 
v_isMeta_boxed_3385_ = lean_unbox(v_isMeta_3381_);
v_res_3386_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v_declName_3380_, v_isMeta_boxed_3385_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
return v_res_3386_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3));
v___x_3396_ = l_Lean_stringToMessageData(v___x_3395_);
return v___x_3396_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_3398_ = l_Lean_stringToMessageData(v___x_3397_);
return v___x_3398_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6));
v___x_3401_ = l_Lean_stringToMessageData(v___x_3400_);
return v___x_3401_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8));
v___x_3404_ = l_Lean_stringToMessageData(v___x_3403_);
return v___x_3404_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10));
v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
return v___x_3407_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11);
v___x_3409_ = l_Lean_MessageData_note(v___x_3408_);
return v___x_3409_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14(void){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13));
v___x_3412_ = l_Lean_stringToMessageData(v___x_3411_);
return v___x_3412_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = lean_box(0);
v___x_3419_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3420_ = l_Lean_mkConst(v___x_3419_, v___x_3418_);
return v___x_3420_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18));
v___x_3423_ = l_Lean_stringToMessageData(v___x_3422_);
return v___x_3423_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20));
v___x_3426_ = l_Lean_stringToMessageData(v___x_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(lean_object* v_x_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v_messages_3434_; lean_object* v_scopes_3435_; lean_object* v_usedQuotCtxts_3436_; lean_object* v_nextMacroScope_3437_; lean_object* v_maxRecDepth_3438_; lean_object* v_ngen_3439_; lean_object* v_auxDeclNGen_3440_; lean_object* v_infoState_3441_; lean_object* v_traceState_3442_; lean_object* v_snapshotTasks_3443_; lean_object* v_prevLinterStates_3444_; lean_object* v_codeQualityEntryTasks_3445_; lean_object* v___y_3446_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
v___x_3450_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2));
lean_inc(v_x_3427_);
v___x_3451_ = l_Lean_Syntax_isOfKind(v_x_3427_, v___x_3450_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
lean_dec(v_x_3427_);
v___x_3452_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3452_;
}
else
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; 
v___x_3453_ = lean_unsigned_to_nat(0u);
v___x_3454_ = l_Lean_Syntax_getArg(v_x_3427_, v___x_3453_);
v___x_3455_ = lean_unsigned_to_nat(1u);
v___x_3456_ = l_Lean_Syntax_matchesNull(v___x_3454_, v___x_3455_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3503_; 
lean_dec(v_x_3427_);
v___x_3503_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3503_;
}
else
{
lean_object* v___x_3504_; lean_object* v_id_3505_; lean_object* v___y_3507_; lean_object* v___y_3508_; uint8_t v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v___x_3504_ = lean_unsigned_to_nat(2u);
v_id_3505_ = l_Lean_Syntax_getArg(v_x_3427_, v___x_3504_);
v___x_3524_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58));
lean_inc(v_id_3505_);
v___x_3525_ = l_Lean_Syntax_isOfKind(v_id_3505_, v___x_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; 
lean_dec(v_id_3505_);
lean_dec(v_x_3427_);
v___x_3526_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3526_;
}
else
{
lean_object* v___x_3527_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v_cmd_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___x_3603_; 
v___x_3527_ = lean_box(1);
v_cmd_3574_ = l_Lean_Syntax_getArg(v_x_3427_, v___x_3455_);
v___x_3575_ = lean_unsigned_to_nat(3u);
v___x_3576_ = l_Lean_Syntax_getArg(v_x_3427_, v___x_3575_);
lean_dec(v_x_3427_);
v___x_3603_ = l_Lean_Elab_Command_getRef___redArg(v_a_3428_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v_fileName_3605_; lean_object* v_fileMap_3606_; lean_object* v_currRecDepth_3607_; lean_object* v_cmdPos_3608_; lean_object* v_macroStack_3609_; lean_object* v_quotContext_x3f_3610_; lean_object* v_currMacroScope_3611_; lean_object* v_snap_x3f_3612_; lean_object* v_cancelTk_x3f_3613_; uint8_t v_suppressElabErrors_3614_; lean_object* v_ref_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v_env_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3603_, 1);
v_fileName_3605_ = lean_ctor_get(v_a_3428_, 0);
v_fileMap_3606_ = lean_ctor_get(v_a_3428_, 1);
v_currRecDepth_3607_ = lean_ctor_get(v_a_3428_, 2);
v_cmdPos_3608_ = lean_ctor_get(v_a_3428_, 3);
v_macroStack_3609_ = lean_ctor_get(v_a_3428_, 4);
v_quotContext_x3f_3610_ = lean_ctor_get(v_a_3428_, 5);
v_currMacroScope_3611_ = lean_ctor_get(v_a_3428_, 6);
v_snap_x3f_3612_ = lean_ctor_get(v_a_3428_, 8);
v_cancelTk_x3f_3613_ = lean_ctor_get(v_a_3428_, 9);
v_suppressElabErrors_3614_ = lean_ctor_get_uint8(v_a_3428_, sizeof(void*)*10);
v_ref_3615_ = l_Lean_replaceRef(v_cmd_3574_, v_a_3604_);
lean_dec(v_a_3604_);
lean_dec(v_cmd_3574_);
lean_inc(v_cancelTk_x3f_3613_);
lean_inc(v_snap_x3f_3612_);
lean_inc(v_currMacroScope_3611_);
lean_inc(v_quotContext_x3f_3610_);
lean_inc(v_macroStack_3609_);
lean_inc(v_cmdPos_3608_);
lean_inc(v_currRecDepth_3607_);
lean_inc_ref(v_fileMap_3606_);
lean_inc_ref(v_fileName_3605_);
v___x_3616_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3616_, 0, v_fileName_3605_);
lean_ctor_set(v___x_3616_, 1, v_fileMap_3606_);
lean_ctor_set(v___x_3616_, 2, v_currRecDepth_3607_);
lean_ctor_set(v___x_3616_, 3, v_cmdPos_3608_);
lean_ctor_set(v___x_3616_, 4, v_macroStack_3609_);
lean_ctor_set(v___x_3616_, 5, v_quotContext_x3f_3610_);
lean_ctor_set(v___x_3616_, 6, v_currMacroScope_3611_);
lean_ctor_set(v___x_3616_, 7, v_ref_3615_);
lean_ctor_set(v___x_3616_, 8, v_snap_x3f_3612_);
lean_ctor_set(v___x_3616_, 9, v_cancelTk_x3f_3613_);
lean_ctor_set_uint8(v___x_3616_, sizeof(void*)*10, v_suppressElabErrors_3614_);
v___x_3617_ = lean_st_ref_get(v_a_3429_);
v_env_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc_ref(v_env_3618_);
lean_dec(v___x_3617_);
v___x_3619_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3620_ = l_Lean_Environment_contains(v_env_3618_, v___x_3619_, v___x_3525_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
lean_dec(v___x_3576_);
lean_dec(v_id_3505_);
v___x_3621_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21);
v___x_3622_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg(v___x_3621_, v___x_3616_, v_a_3429_);
lean_dec_ref_known(v___x_3616_, 10);
return v___x_3622_;
}
else
{
v___y_3578_ = v___x_3616_;
v___y_3579_ = v_a_3429_;
goto v___jp_3577_;
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v___x_3576_);
lean_dec(v_cmd_3574_);
lean_dec(v_id_3505_);
v_a_3623_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3603_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3603_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
v___jp_3528_:
{
lean_object* v___x_3533_; lean_object* v_env_3534_; lean_object* v___x_3535_; lean_object* v_toEnvExtension_3536_; lean_object* v_asyncMode_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v___x_3533_ = lean_st_ref_get(v___y_3532_);
v_env_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc_ref(v_env_3534_);
lean_dec(v___x_3533_);
v___x_3535_ = l_Lean_errorExplanationExt;
v_toEnvExtension_3536_ = lean_ctor_get(v___x_3535_, 0);
v_asyncMode_3537_ = lean_ctor_get(v_toEnvExtension_3536_, 2);
v___x_3538_ = lean_box(0);
v___x_3539_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3527_, v___x_3535_, v_env_3534_, v_asyncMode_3537_, v___x_3538_);
v___x_3540_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v___y_3530_, v___x_3539_);
lean_dec(v___x_3539_);
if (v___x_3540_ == 0)
{
v___y_3516_ = v___y_3529_;
v___y_3517_ = v___y_3530_;
v___y_3518_ = v___y_3531_;
v___y_3519_ = v___y_3532_;
goto v___jp_3515_;
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec_ref(v___y_3529_);
v___x_3541_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4);
v___x_3542_ = l_Lean_MessageData_ofName(v___y_3530_);
v___x_3543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3541_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
v___x_3544_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
v___x_3545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3543_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_id_3505_, v___x_3545_, v___y_3531_, v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v_id_3505_);
return v___x_3546_;
}
}
v___jp_3547_:
{
lean_object* v___x_3552_; uint8_t v___x_3553_; 
v___x_3552_ = l_Lean_Name_getNumParts(v___y_3549_);
v___x_3553_ = lean_nat_dec_eq(v___x_3552_, v___x_3504_);
lean_dec(v___x_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
lean_dec_ref(v___y_3548_);
v___x_3554_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
v___x_3555_ = l_Lean_MessageData_ofName(v___y_3549_);
v___x_3556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3554_);
lean_ctor_set(v___x_3556_, 1, v___x_3555_);
v___x_3557_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9);
v___x_3558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3556_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
v___x_3559_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12);
v___x_3560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3558_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_id_3505_, v___x_3560_, v___y_3550_, v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v_id_3505_);
return v___x_3561_;
}
else
{
v___y_3529_ = v___y_3548_;
v___y_3530_ = v___y_3549_;
v___y_3531_ = v___y_3550_;
v___y_3532_ = v___y_3551_;
goto v___jp_3528_;
}
}
v___jp_3562_:
{
uint8_t v___x_3567_; 
v___x_3567_ = l_Lean_Name_hasMacroScopes(v___y_3564_);
if (v___x_3567_ == 0)
{
v___y_3548_ = v___y_3563_;
v___y_3549_ = v___y_3564_;
v___y_3550_ = v___y_3565_;
v___y_3551_ = v___y_3566_;
goto v___jp_3547_;
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
v___x_3568_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
lean_inc(v_id_3505_);
v___x_3569_ = l_Lean_MessageData_ofSyntax(v_id_3505_);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14);
v___x_3572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3570_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_id_3505_, v___x_3572_, v___y_3565_, v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v_id_3505_);
return v___x_3573_;
}
}
v___jp_3577_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3581_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v___x_3580_, v___x_3525_, v___y_3578_, v___y_3579_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___f_3584_; lean_object* v___x_3585_; 
lean_dec_ref_known(v___x_3581_, 1);
v___x_3582_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17);
v___x_3583_ = lean_box(v___x_3525_);
v___f_3584_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3584_, 0, v___x_3582_);
lean_closure_set(v___f_3584_, 1, v___x_3576_);
lean_closure_set(v___f_3584_, 2, v___x_3583_);
v___x_3585_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_3584_, v___y_3578_, v___y_3579_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3587_; uint8_t v___x_3588_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3586_);
lean_dec_ref_known(v___x_3585_, 1);
v___x_3587_ = l_Lean_TSyntax_getId(v_id_3505_);
v___x_3588_ = l_Lean_Name_isAnonymous(v___x_3587_);
if (v___x_3588_ == 0)
{
v___y_3563_ = v_a_3586_;
v___y_3564_ = v___x_3587_;
v___y_3565_ = v___y_3578_;
v___y_3566_ = v___y_3579_;
goto v___jp_3562_;
}
else
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
lean_dec(v___x_3587_);
lean_dec(v_a_3586_);
v___x_3589_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19);
lean_inc(v_id_3505_);
v___x_3590_ = l_Lean_MessageData_ofSyntax(v_id_3505_);
v___x_3591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3589_);
lean_ctor_set(v___x_3591_, 1, v___x_3590_);
v___x_3592_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
v___x_3593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3591_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v___x_3594_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_id_3505_, v___x_3593_, v___y_3578_, v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v_id_3505_);
return v___x_3594_;
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec_ref(v___y_3578_);
lean_dec(v_id_3505_);
v_a_3595_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3585_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3585_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_dec_ref(v___y_3578_);
lean_dec(v___x_3576_);
lean_dec(v_id_3505_);
return v___x_3581_;
}
}
}
v___jp_3506_:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_Syntax_getTailPos_x3f(v_id_3505_, v___y_3509_);
lean_dec(v_id_3505_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_inc(v___y_3512_);
v___y_3458_ = v___y_3507_;
v___y_3459_ = v___y_3508_;
v___y_3460_ = v___y_3512_;
v___y_3461_ = v___y_3510_;
v___y_3462_ = v___y_3511_;
v___y_3463_ = v___y_3512_;
goto v___jp_3457_;
}
else
{
lean_object* v_val_3514_; 
v_val_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_val_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___y_3458_ = v___y_3507_;
v___y_3459_ = v___y_3508_;
v___y_3460_ = v___y_3512_;
v___y_3461_ = v___y_3510_;
v___y_3462_ = v___y_3511_;
v___y_3463_ = v_val_3514_;
goto v___jp_3457_;
}
}
v___jp_3515_:
{
lean_object* v_fileMap_3520_; uint8_t v___x_3521_; lean_object* v___x_3522_; 
v_fileMap_3520_ = lean_ctor_get(v___y_3518_, 1);
lean_inc_ref(v_fileMap_3520_);
lean_dec_ref(v___y_3518_);
v___x_3521_ = 0;
v___x_3522_ = l_Lean_Syntax_getPos_x3f(v_id_3505_, v___x_3521_);
if (lean_obj_tag(v___x_3522_) == 0)
{
v___y_3507_ = v___y_3519_;
v___y_3508_ = v_fileMap_3520_;
v___y_3509_ = v___x_3521_;
v___y_3510_ = v___y_3516_;
v___y_3511_ = v___y_3517_;
v___y_3512_ = v___x_3453_;
goto v___jp_3506_;
}
else
{
lean_object* v_val_3523_; 
v_val_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_val_3523_);
lean_dec_ref_known(v___x_3522_, 1);
v___y_3507_ = v___y_3519_;
v___y_3508_ = v_fileMap_3520_;
v___y_3509_ = v___x_3521_;
v___y_3510_ = v___y_3516_;
v___y_3511_ = v___y_3517_;
v___y_3512_ = v_val_3523_;
goto v___jp_3506_;
}
}
}
v___jp_3457_:
{
lean_object* v___x_3464_; lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3502_; 
v___x_3464_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v___y_3458_);
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3502_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3502_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3469_ = l_Lean_DeclarationRange_ofStringPositions(v___y_3459_, v___y_3460_, v___y_3463_);
lean_dec(v___y_3463_);
lean_dec(v___y_3460_);
v___x_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3470_, 0, v_a_3465_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set_tag(v___x_3467_, 1);
lean_ctor_set(v___x_3467_, 0, v___x_3470_);
v___x_3472_ = v___x_3467_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___x_3473_; lean_object* v_env_3474_; lean_object* v_messages_3475_; lean_object* v_scopes_3476_; lean_object* v_usedQuotCtxts_3477_; lean_object* v_nextMacroScope_3478_; lean_object* v_maxRecDepth_3479_; lean_object* v_ngen_3480_; lean_object* v_auxDeclNGen_3481_; lean_object* v_infoState_3482_; lean_object* v_traceState_3483_; lean_object* v_snapshotTasks_3484_; lean_object* v_prevLinterStates_3485_; lean_object* v_codeQualityEntryTasks_3486_; lean_object* v___x_3487_; lean_object* v_toEnvExtension_3488_; lean_object* v_addEntryFn_3489_; lean_object* v_asyncMode_3490_; uint8_t v_logWrites_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___f_3496_; lean_object* v___x_3497_; 
v___x_3473_ = lean_st_ref_take(v___y_3458_);
v_env_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc_ref(v_env_3474_);
v_messages_3475_ = lean_ctor_get(v___x_3473_, 1);
lean_inc_ref(v_messages_3475_);
v_scopes_3476_ = lean_ctor_get(v___x_3473_, 2);
lean_inc(v_scopes_3476_);
v_usedQuotCtxts_3477_ = lean_ctor_get(v___x_3473_, 3);
lean_inc(v_usedQuotCtxts_3477_);
v_nextMacroScope_3478_ = lean_ctor_get(v___x_3473_, 4);
lean_inc(v_nextMacroScope_3478_);
v_maxRecDepth_3479_ = lean_ctor_get(v___x_3473_, 5);
lean_inc(v_maxRecDepth_3479_);
v_ngen_3480_ = lean_ctor_get(v___x_3473_, 6);
lean_inc_ref(v_ngen_3480_);
v_auxDeclNGen_3481_ = lean_ctor_get(v___x_3473_, 7);
lean_inc_ref(v_auxDeclNGen_3481_);
v_infoState_3482_ = lean_ctor_get(v___x_3473_, 8);
lean_inc_ref(v_infoState_3482_);
v_traceState_3483_ = lean_ctor_get(v___x_3473_, 9);
lean_inc_ref(v_traceState_3483_);
v_snapshotTasks_3484_ = lean_ctor_get(v___x_3473_, 10);
lean_inc_ref(v_snapshotTasks_3484_);
v_prevLinterStates_3485_ = lean_ctor_get(v___x_3473_, 11);
lean_inc(v_prevLinterStates_3485_);
v_codeQualityEntryTasks_3486_ = lean_ctor_get(v___x_3473_, 12);
lean_inc_ref(v_codeQualityEntryTasks_3486_);
lean_dec(v___x_3473_);
v___x_3487_ = l_Lean_errorExplanationExt;
v_toEnvExtension_3488_ = lean_ctor_get(v___x_3487_, 0);
v_addEntryFn_3489_ = lean_ctor_get(v___x_3487_, 3);
v_asyncMode_3490_ = lean_ctor_get(v_toEnvExtension_3488_, 2);
v_logWrites_3491_ = lean_ctor_get_uint8(v_toEnvExtension_3488_, sizeof(void*)*6);
v___x_3492_ = lean_box(0);
v___x_3493_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_3494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v___y_3461_);
lean_ctor_set(v___x_3494_, 2, v___x_3472_);
v___x_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___y_3462_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
lean_inc(v_addEntryFn_3489_);
v___f_3496_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0), 3, 2);
lean_closure_set(v___f_3496_, 0, v_addEntryFn_3489_);
lean_closure_set(v___f_3496_, 1, v___x_3495_);
v___x_3497_ = lean_box(0);
if (v_logWrites_3491_ == 0)
{
lean_object* v___x_3498_; 
lean_inc_ref(v_toEnvExtension_3488_);
v___x_3498_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3488_, v_env_3474_, v___f_3496_, v_asyncMode_3490_, v___x_3497_, v___x_3456_);
v___y_3432_ = v___y_3458_;
v___y_3433_ = v___x_3492_;
v_messages_3434_ = v_messages_3475_;
v_scopes_3435_ = v_scopes_3476_;
v_usedQuotCtxts_3436_ = v_usedQuotCtxts_3477_;
v_nextMacroScope_3437_ = v_nextMacroScope_3478_;
v_maxRecDepth_3438_ = v_maxRecDepth_3479_;
v_ngen_3439_ = v_ngen_3480_;
v_auxDeclNGen_3440_ = v_auxDeclNGen_3481_;
v_infoState_3441_ = v_infoState_3482_;
v_traceState_3442_ = v_traceState_3483_;
v_snapshotTasks_3443_ = v_snapshotTasks_3484_;
v_prevLinterStates_3444_ = v_prevLinterStates_3485_;
v_codeQualityEntryTasks_3445_ = v_codeQualityEntryTasks_3486_;
v___y_3446_ = v___x_3498_;
goto v___jp_3431_;
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
lean_inc_ref_n(v_toEnvExtension_3488_, 2);
v___x_3499_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3488_, v_env_3474_);
lean_dec_ref(v_env_3474_);
v___x_3500_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3488_, v___x_3499_, v___f_3496_, v_asyncMode_3490_, v___x_3497_, v___x_3456_);
v___y_3432_ = v___y_3458_;
v___y_3433_ = v___x_3492_;
v_messages_3434_ = v_messages_3475_;
v_scopes_3435_ = v_scopes_3476_;
v_usedQuotCtxts_3436_ = v_usedQuotCtxts_3477_;
v_nextMacroScope_3437_ = v_nextMacroScope_3478_;
v_maxRecDepth_3438_ = v_maxRecDepth_3479_;
v_ngen_3439_ = v_ngen_3480_;
v_auxDeclNGen_3440_ = v_auxDeclNGen_3481_;
v_infoState_3441_ = v_infoState_3482_;
v_traceState_3442_ = v_traceState_3483_;
v_snapshotTasks_3443_ = v_snapshotTasks_3484_;
v_prevLinterStates_3444_ = v_prevLinterStates_3485_;
v_codeQualityEntryTasks_3445_ = v_codeQualityEntryTasks_3486_;
v___y_3446_ = v___x_3500_;
goto v___jp_3431_;
}
}
}
}
}
v___jp_3431_:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v___x_3447_, 0, v___y_3446_);
lean_ctor_set(v___x_3447_, 1, v_messages_3434_);
lean_ctor_set(v___x_3447_, 2, v_scopes_3435_);
lean_ctor_set(v___x_3447_, 3, v_usedQuotCtxts_3436_);
lean_ctor_set(v___x_3447_, 4, v_nextMacroScope_3437_);
lean_ctor_set(v___x_3447_, 5, v_maxRecDepth_3438_);
lean_ctor_set(v___x_3447_, 6, v_ngen_3439_);
lean_ctor_set(v___x_3447_, 7, v_auxDeclNGen_3440_);
lean_ctor_set(v___x_3447_, 8, v_infoState_3441_);
lean_ctor_set(v___x_3447_, 9, v_traceState_3442_);
lean_ctor_set(v___x_3447_, 10, v_snapshotTasks_3443_);
lean_ctor_set(v___x_3447_, 11, v_prevLinterStates_3444_);
lean_ctor_set(v___x_3447_, 12, v_codeQualityEntryTasks_3445_);
v___x_3448_ = lean_st_ref_put(v___y_3432_, v___x_3447_);
v___x_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3449_, 0, v___y_3433_);
return v___x_3449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed(lean_object* v_x_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(v_x_3631_, v_a_3632_, v_a_3633_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3632_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(lean_object* v_00_u03b1_3636_, lean_object* v_ref_3637_, lean_object* v_msg_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_ref_3637_, v_msg_3638_, v___y_3639_, v___y_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___boxed(lean_object* v_00_u03b1_3643_, lean_object* v_ref_3644_, lean_object* v_msg_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(v_00_u03b1_3643_, v_ref_3644_, v_msg_3645_, v___y_3646_, v___y_3647_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v_ref_3644_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7(lean_object* v_msgData_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___redArg(v_msgData_3650_, v___y_3652_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7___boxed(lean_object* v_msgData_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__7(v_msgData_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5(lean_object* v_00_u03b1_3660_, lean_object* v_msg_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___redArg(v_msg_3661_, v___y_3662_, v___y_3663_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5___boxed(lean_object* v_00_u03b1_3666_, lean_object* v_msg_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5(v_00_u03b1_3666_, v_msg_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8(lean_object* v_msgData_3672_, lean_object* v_macroStack_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___redArg(v_msgData_3672_, v_macroStack_3673_, v___y_3675_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8___boxed(lean_object* v_msgData_3678_, lean_object* v_macroStack_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__5_spec__8(v_msgData_3678_, v_macroStack_3679_, v___y_3680_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1(){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3691_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3692_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2));
v___x_3693_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1));
v___x_3694_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed), 4, 0);
v___x_3695_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3691_, v___x_3692_, v___x_3693_, v___x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___boxed(lean_object* v_a_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
return v_res_3697_;
}
}
lean_object* runtime_initialize_Lean_Widget_UserWidget(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ErrorExplanation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap);
res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Widget_UserWidget(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ErrorExplanation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Widget_UserWidget(uint8_t builtin);
lean_object* initialize_Lean_Widget_UserWidget(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ErrorExplanation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ErrorExplanation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ErrorExplanation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ErrorExplanation(builtin);
}
#ifdef __cplusplus
}
#endif
