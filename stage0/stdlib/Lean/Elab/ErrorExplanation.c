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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
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
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
extern lean_object* l_Lean_errorExplanationExt;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_abortTermExceptionId;
lean_object* l_Lean_MessageData_note(lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_188_ = l_Lean_SourceInfo_fromRef(v_ref_187_, v___x_184_);
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
lean_dec_ref(v___x_203_);
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
lean_dec_ref(v___x_238_);
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
v___x_265_ = l_Lean_SourceInfo_fromRef(v_ref_264_, v___x_261_);
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
lean_dec_ref(v___x_280_);
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
lean_dec_ref(v___x_315_);
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
v___x_344_ = l_Lean_SourceInfo_fromRef(v_ref_343_, v___x_340_);
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
lean_dec_ref(v___x_359_);
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
lean_dec_ref(v___x_394_);
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
v___x_421_ = l_Lean_SourceInfo_fromRef(v_ref_420_, v___x_417_);
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
lean_dec_ref(v___x_436_);
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
lean_dec_ref(v___x_471_);
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
v___x_500_ = l_Lean_SourceInfo_fromRef(v_ref_499_, v___x_496_);
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
lean_dec_ref(v___x_515_);
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
lean_dec_ref(v___x_550_);
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
lean_dec_ref(v___x_592_);
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
lean_dec_ref(v___x_631_);
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
lean_dec_ref(v___x_667_);
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
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_702_; uint64_t v___x_703_; 
v___x_702_ = lean_unsigned_to_nat(1723u);
v___x_703_ = lean_uint64_of_nat(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
if (lean_obj_tag(v_x_705_) == 0)
{
return v_x_704_;
}
else
{
lean_object* v_key_706_; lean_object* v_value_707_; lean_object* v_tail_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_734_; 
v_key_706_ = lean_ctor_get(v_x_705_, 0);
v_value_707_ = lean_ctor_get(v_x_705_, 1);
v_tail_708_ = lean_ctor_get(v_x_705_, 2);
v_isSharedCheck_734_ = !lean_is_exclusive(v_x_705_);
if (v_isSharedCheck_734_ == 0)
{
v___x_710_ = v_x_705_;
v_isShared_711_ = v_isSharedCheck_734_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_tail_708_);
lean_inc(v_value_707_);
lean_inc(v_key_706_);
lean_dec(v_x_705_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_734_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; uint64_t v___y_714_; 
v___x_712_ = lean_array_get_size(v_x_704_);
if (lean_obj_tag(v_key_706_) == 0)
{
uint64_t v___x_732_; 
v___x_732_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
v___y_714_ = v___x_732_;
goto v___jp_713_;
}
else
{
uint64_t v_hash_733_; 
v_hash_733_ = lean_ctor_get_uint64(v_key_706_, sizeof(void*)*2);
v___y_714_ = v_hash_733_;
goto v___jp_713_;
}
v___jp_713_:
{
uint64_t v___x_715_; uint64_t v___x_716_; uint64_t v_fold_717_; uint64_t v___x_718_; uint64_t v___x_719_; uint64_t v___x_720_; size_t v___x_721_; size_t v___x_722_; size_t v___x_723_; size_t v___x_724_; size_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_715_ = 32ULL;
v___x_716_ = lean_uint64_shift_right(v___y_714_, v___x_715_);
v_fold_717_ = lean_uint64_xor(v___y_714_, v___x_716_);
v___x_718_ = 16ULL;
v___x_719_ = lean_uint64_shift_right(v_fold_717_, v___x_718_);
v___x_720_ = lean_uint64_xor(v_fold_717_, v___x_719_);
v___x_721_ = lean_uint64_to_usize(v___x_720_);
v___x_722_ = lean_usize_of_nat(v___x_712_);
v___x_723_ = ((size_t)1ULL);
v___x_724_ = lean_usize_sub(v___x_722_, v___x_723_);
v___x_725_ = lean_usize_land(v___x_721_, v___x_724_);
v___x_726_ = lean_array_uget_borrowed(v_x_704_, v___x_725_);
lean_inc(v___x_726_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 2, v___x_726_);
v___x_728_ = v___x_710_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_key_706_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_value_707_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v___x_726_);
v___x_728_ = v_reuseFailAlloc_731_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; 
v___x_729_ = lean_array_uset(v_x_704_, v___x_725_, v___x_728_);
v_x_704_ = v___x_729_;
v_x_705_ = v_tail_708_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_735_, lean_object* v_source_736_, lean_object* v_target_737_){
_start:
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = lean_array_get_size(v_source_736_);
v___x_739_ = lean_nat_dec_lt(v_i_735_, v___x_738_);
if (v___x_739_ == 0)
{
lean_dec_ref(v_source_736_);
lean_dec(v_i_735_);
return v_target_737_;
}
else
{
lean_object* v_es_740_; lean_object* v___x_741_; lean_object* v_source_742_; lean_object* v_target_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_es_740_ = lean_array_fget(v_source_736_, v_i_735_);
v___x_741_ = lean_box(0);
v_source_742_ = lean_array_fset(v_source_736_, v_i_735_, v___x_741_);
v_target_743_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_737_, v_es_740_);
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_add(v_i_735_, v___x_744_);
lean_dec(v_i_735_);
v_i_735_ = v___x_745_;
v_source_736_ = v_source_742_;
v_target_737_ = v_target_743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(lean_object* v_data_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v_nbuckets_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_748_ = lean_array_get_size(v_data_747_);
v___x_749_ = lean_unsigned_to_nat(2u);
v_nbuckets_750_ = lean_nat_mul(v___x_748_, v___x_749_);
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = lean_box(0);
v___x_753_ = lean_mk_array(v_nbuckets_750_, v___x_752_);
v___x_754_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v___x_751_, v_data_747_, v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(lean_object* v_a_755_, lean_object* v_x_756_){
_start:
{
if (lean_obj_tag(v_x_756_) == 0)
{
uint8_t v___x_757_; 
v___x_757_ = 0;
return v___x_757_;
}
else
{
lean_object* v_key_758_; lean_object* v_tail_759_; uint8_t v___x_760_; 
v_key_758_ = lean_ctor_get(v_x_756_, 0);
v_tail_759_ = lean_ctor_get(v_x_756_, 2);
v___x_760_ = lean_name_eq(v_key_758_, v_a_755_);
if (v___x_760_ == 0)
{
v_x_756_ = v_tail_759_;
goto _start;
}
else
{
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_762_, lean_object* v_x_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_762_, v_x_763_);
lean_dec(v_x_763_);
lean_dec(v_a_762_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(lean_object* v_m_766_, lean_object* v_a_767_, lean_object* v_b_768_){
_start:
{
lean_object* v_size_769_; lean_object* v_buckets_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_816_; 
v_size_769_ = lean_ctor_get(v_m_766_, 0);
v_buckets_770_ = lean_ctor_get(v_m_766_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v_m_766_);
if (v_isSharedCheck_816_ == 0)
{
v___x_772_ = v_m_766_;
v_isShared_773_ = v_isSharedCheck_816_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_buckets_770_);
lean_inc(v_size_769_);
lean_dec(v_m_766_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_816_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; uint64_t v___y_776_; 
v___x_774_ = lean_array_get_size(v_buckets_770_);
if (lean_obj_tag(v_a_767_) == 0)
{
uint64_t v___x_814_; 
v___x_814_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
v___y_776_ = v___x_814_;
goto v___jp_775_;
}
else
{
uint64_t v_hash_815_; 
v_hash_815_ = lean_ctor_get_uint64(v_a_767_, sizeof(void*)*2);
v___y_776_ = v_hash_815_;
goto v___jp_775_;
}
v___jp_775_:
{
uint64_t v___x_777_; uint64_t v___x_778_; uint64_t v_fold_779_; uint64_t v___x_780_; uint64_t v___x_781_; uint64_t v___x_782_; size_t v___x_783_; size_t v___x_784_; size_t v___x_785_; size_t v___x_786_; size_t v___x_787_; lean_object* v_bkt_788_; uint8_t v___x_789_; 
v___x_777_ = 32ULL;
v___x_778_ = lean_uint64_shift_right(v___y_776_, v___x_777_);
v_fold_779_ = lean_uint64_xor(v___y_776_, v___x_778_);
v___x_780_ = 16ULL;
v___x_781_ = lean_uint64_shift_right(v_fold_779_, v___x_780_);
v___x_782_ = lean_uint64_xor(v_fold_779_, v___x_781_);
v___x_783_ = lean_uint64_to_usize(v___x_782_);
v___x_784_ = lean_usize_of_nat(v___x_774_);
v___x_785_ = ((size_t)1ULL);
v___x_786_ = lean_usize_sub(v___x_784_, v___x_785_);
v___x_787_ = lean_usize_land(v___x_783_, v___x_786_);
v_bkt_788_ = lean_array_uget_borrowed(v_buckets_770_, v___x_787_);
v___x_789_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_767_, v_bkt_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v_size_x27_791_; lean_object* v___x_792_; lean_object* v_buckets_x27_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_790_ = lean_unsigned_to_nat(1u);
v_size_x27_791_ = lean_nat_add(v_size_769_, v___x_790_);
lean_dec(v_size_769_);
lean_inc(v_bkt_788_);
v___x_792_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_792_, 0, v_a_767_);
lean_ctor_set(v___x_792_, 1, v_b_768_);
lean_ctor_set(v___x_792_, 2, v_bkt_788_);
v_buckets_x27_793_ = lean_array_uset(v_buckets_770_, v___x_787_, v___x_792_);
v___x_794_ = lean_unsigned_to_nat(4u);
v___x_795_ = lean_nat_mul(v_size_x27_791_, v___x_794_);
v___x_796_ = lean_unsigned_to_nat(3u);
v___x_797_ = lean_nat_div(v___x_795_, v___x_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_array_get_size(v_buckets_x27_793_);
v___x_799_ = lean_nat_dec_le(v___x_797_, v___x_798_);
lean_dec(v___x_797_);
if (v___x_799_ == 0)
{
lean_object* v_val_800_; lean_object* v___x_802_; 
v_val_800_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_buckets_x27_793_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v_val_800_);
lean_ctor_set(v___x_772_, 0, v_size_x27_791_);
v___x_802_ = v___x_772_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_size_x27_791_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_val_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
else
{
lean_object* v___x_805_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v_buckets_x27_793_);
lean_ctor_set(v___x_772_, 0, v_size_x27_791_);
v___x_805_ = v___x_772_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_size_x27_791_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_buckets_x27_793_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_object* v___x_807_; lean_object* v_buckets_x27_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
lean_inc(v_bkt_788_);
v___x_807_ = lean_box(0);
v_buckets_x27_808_ = lean_array_uset(v_buckets_770_, v___x_787_, v___x_807_);
v___x_809_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_767_, v_b_768_, v_bkt_788_);
v___x_810_ = lean_array_uset(v_buckets_x27_808_, v___x_787_, v___x_809_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___x_810_);
v___x_812_ = v___x_772_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_size_769_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(lean_object* v_as_x27_817_, lean_object* v_b_818_){
_start:
{
if (lean_obj_tag(v_as_x27_817_) == 0)
{
return v_b_818_;
}
else
{
lean_object* v_head_819_; lean_object* v_tail_820_; lean_object* v_fst_821_; lean_object* v_snd_822_; lean_object* v_r_823_; 
v_head_819_ = lean_ctor_get(v_as_x27_817_, 0);
lean_inc(v_head_819_);
v_tail_820_ = lean_ctor_get(v_as_x27_817_, 1);
lean_inc(v_tail_820_);
lean_dec_ref(v_as_x27_817_);
v_fst_821_ = lean_ctor_get(v_head_819_, 0);
lean_inc(v_fst_821_);
v_snd_822_ = lean_ctor_get(v_head_819_, 1);
lean_inc(v_snd_822_);
lean_dec(v_head_819_);
v_r_823_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_b_818_, v_fst_821_, v_snd_822_);
v_as_x27_817_ = v_tail_820_;
v_b_818_ = v_r_823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(lean_object* v_m_825_, lean_object* v_l_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_l_826_, v_m_825_);
return v___x_827_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_box(0);
v___x_891_ = lean_unsigned_to_nat(16u);
v___x_892_ = lean_mk_array(v___x_891_, v___x_890_);
return v___x_892_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23);
v___x_897_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21));
v___x_898_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v___x_897_, v___x_896_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap(void){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = lean_obj_once(&l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24, &l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24_once, _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0(lean_object* v_00_u03b2_900_, lean_object* v_m_901_, lean_object* v_a_902_, lean_object* v_b_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_m_901_, v_a_902_, v_b_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(lean_object* v_as_905_, lean_object* v_as_x27_906_, lean_object* v_b_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_906_, v_b_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___boxed(lean_object* v_as_910_, lean_object* v_as_x27_911_, lean_object* v_b_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(v_as_910_, v_as_x27_911_, v_b_912_, v_a_913_);
lean_dec(v_as_910_);
return v_res_914_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_915_, lean_object* v_a_916_, lean_object* v_x_917_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_916_, v_x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_919_, lean_object* v_a_920_, lean_object* v_x_921_){
_start:
{
uint8_t v_res_922_; lean_object* v_r_923_; 
v_res_922_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(v_00_u03b2_919_, v_a_920_, v_x_921_);
lean_dec(v_x_921_);
lean_dec(v_a_920_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_924_, lean_object* v_data_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_data_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_927_, lean_object* v_a_928_, lean_object* v_b_929_, lean_object* v_x_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_928_, v_b_929_, v_x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_932_, lean_object* v_i_933_, lean_object* v_source_934_, lean_object* v_target_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_933_, v_source_934_, v_target_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_938_, v_x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(lean_object* v_name_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; lean_object* v_env_945_; lean_object* v___x_946_; lean_object* v_toEnvExtension_947_; lean_object* v_asyncMode_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_944_ = lean_st_ref_get(v___y_942_);
v_env_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc_ref(v_env_945_);
lean_dec(v___x_944_);
v___x_946_ = l_Lean_errorExplanationExt;
v_toEnvExtension_947_ = lean_ctor_get(v___x_946_, 0);
v_asyncMode_948_ = lean_ctor_get(v_toEnvExtension_947_, 2);
v___x_949_ = lean_box(1);
v___x_950_ = lean_box(0);
v___x_951_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_949_, v___x_946_, v_env_945_, v_asyncMode_948_, v___x_950_);
v___x_952_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_951_, v_name_941_);
lean_dec(v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg___boxed(lean_object* v_name_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec(v_name_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(lean_object* v_name_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_958_, v___y_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___boxed(lean_object* v_name_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(v_name_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v_name_967_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(lean_object* v_msgData_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; lean_object* v_env_983_; lean_object* v___x_984_; lean_object* v_mctx_985_; lean_object* v_lctx_986_; lean_object* v_options_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_982_ = lean_st_ref_get(v___y_980_);
v_env_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_ref(v_env_983_);
lean_dec(v___x_982_);
v___x_984_ = lean_st_ref_get(v___y_978_);
v_mctx_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc_ref(v_mctx_985_);
lean_dec(v___x_984_);
v_lctx_986_ = lean_ctor_get(v___y_977_, 2);
v_options_987_ = lean_ctor_get(v___y_979_, 2);
lean_inc_ref(v_options_987_);
lean_inc_ref(v_lctx_986_);
v___x_988_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_988_, 0, v_env_983_);
lean_ctor_set(v___x_988_, 1, v_mctx_985_);
lean_ctor_set(v___x_988_, 2, v_lctx_986_);
lean_ctor_set(v___x_988_, 3, v_options_987_);
v___x_989_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v_msgData_976_);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18___boxed(lean_object* v_msgData_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msgData_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_997_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_998_; double v___x_999_; 
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = lean_float_of_nat(v___x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(lean_object* v_cls_1003_, lean_object* v_msg_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_ref_1010_; lean_object* v___x_1011_; lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1056_; 
v_ref_1010_ = lean_ctor_get(v___y_1007_, 5);
v___x_1011_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1056_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1056_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v_traceState_1017_; lean_object* v_env_1018_; lean_object* v_nextMacroScope_1019_; lean_object* v_ngen_1020_; lean_object* v_auxDeclNGen_1021_; lean_object* v_cache_1022_; lean_object* v_messages_1023_; lean_object* v_infoState_1024_; lean_object* v_snapshotTasks_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1055_; 
v___x_1016_ = lean_st_ref_take(v___y_1008_);
v_traceState_1017_ = lean_ctor_get(v___x_1016_, 4);
v_env_1018_ = lean_ctor_get(v___x_1016_, 0);
v_nextMacroScope_1019_ = lean_ctor_get(v___x_1016_, 1);
v_ngen_1020_ = lean_ctor_get(v___x_1016_, 2);
v_auxDeclNGen_1021_ = lean_ctor_get(v___x_1016_, 3);
v_cache_1022_ = lean_ctor_get(v___x_1016_, 5);
v_messages_1023_ = lean_ctor_get(v___x_1016_, 6);
v_infoState_1024_ = lean_ctor_get(v___x_1016_, 7);
v_snapshotTasks_1025_ = lean_ctor_get(v___x_1016_, 8);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1027_ = v___x_1016_;
v_isShared_1028_ = v_isSharedCheck_1055_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_snapshotTasks_1025_);
lean_inc(v_infoState_1024_);
lean_inc(v_messages_1023_);
lean_inc(v_cache_1022_);
lean_inc(v_traceState_1017_);
lean_inc(v_auxDeclNGen_1021_);
lean_inc(v_ngen_1020_);
lean_inc(v_nextMacroScope_1019_);
lean_inc(v_env_1018_);
lean_dec(v___x_1016_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1055_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
uint64_t v_tid_1029_; lean_object* v_traces_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1054_; 
v_tid_1029_ = lean_ctor_get_uint64(v_traceState_1017_, sizeof(void*)*1);
v_traces_1030_ = lean_ctor_get(v_traceState_1017_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_traceState_1017_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1032_ = v_traceState_1017_;
v_isShared_1033_ = v_isSharedCheck_1054_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_traces_1030_);
lean_dec(v_traceState_1017_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1054_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; double v___x_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
v___x_1036_ = 0;
v___x_1037_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_1038_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1038_, 0, v_cls_1003_);
lean_ctor_set(v___x_1038_, 1, v___x_1034_);
lean_ctor_set(v___x_1038_, 2, v___x_1037_);
lean_ctor_set_float(v___x_1038_, sizeof(void*)*3, v___x_1035_);
lean_ctor_set_float(v___x_1038_, sizeof(void*)*3 + 8, v___x_1035_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*3 + 16, v___x_1036_);
v___x_1039_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2));
v___x_1040_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v_a_1012_);
lean_ctor_set(v___x_1040_, 2, v___x_1039_);
lean_inc(v_ref_1010_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_ref_1010_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = l_Lean_PersistentArray_push___redArg(v_traces_1030_, v___x_1041_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1042_);
v___x_1044_ = v___x_1032_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1042_);
lean_ctor_set_uint64(v_reuseFailAlloc_1053_, sizeof(void*)*1, v_tid_1029_);
v___x_1044_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1046_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 4, v___x_1044_);
v___x_1046_ = v___x_1027_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_env_1018_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_nextMacroScope_1019_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_ngen_1020_);
lean_ctor_set(v_reuseFailAlloc_1052_, 3, v_auxDeclNGen_1021_);
lean_ctor_set(v_reuseFailAlloc_1052_, 4, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1052_, 5, v_cache_1022_);
lean_ctor_set(v_reuseFailAlloc_1052_, 6, v_messages_1023_);
lean_ctor_set(v_reuseFailAlloc_1052_, 7, v_infoState_1024_);
lean_ctor_set(v_reuseFailAlloc_1052_, 8, v_snapshotTasks_1025_);
v___x_1046_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1047_ = lean_st_ref_set(v___y_1008_, v___x_1046_);
v___x_1048_ = lean_box(0);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1048_);
v___x_1050_ = v___x_1014_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___boxed(lean_object* v_cls_1057_, lean_object* v_msg_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_1057_, v_msg_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(lean_object* v_as_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
if (lean_obj_tag(v_as_1068_) == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
else
{
lean_object* v_options_1078_; uint8_t v_hasTrace_1079_; 
v_options_1078_ = lean_ctor_get(v___y_1073_, 2);
v_hasTrace_1079_ = lean_ctor_get_uint8(v_options_1078_, sizeof(void*)*1);
if (v_hasTrace_1079_ == 0)
{
lean_object* v_tail_1080_; 
v_tail_1080_ = lean_ctor_get(v_as_1068_, 1);
lean_inc(v_tail_1080_);
lean_dec_ref(v_as_1068_);
v_as_1068_ = v_tail_1080_;
goto _start;
}
else
{
lean_object* v_head_1082_; lean_object* v_tail_1083_; lean_object* v_fst_1084_; lean_object* v_snd_1085_; lean_object* v_inheritedTraceOptions_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_head_1082_ = lean_ctor_get(v_as_1068_, 0);
lean_inc(v_head_1082_);
v_tail_1083_ = lean_ctor_get(v_as_1068_, 1);
lean_inc(v_tail_1083_);
lean_dec_ref(v_as_1068_);
v_fst_1084_ = lean_ctor_get(v_head_1082_, 0);
lean_inc_n(v_fst_1084_, 2);
v_snd_1085_ = lean_ctor_get(v_head_1082_, 1);
lean_inc(v_snd_1085_);
lean_dec(v_head_1082_);
v_inheritedTraceOptions_1086_ = lean_ctor_get(v___y_1073_, 13);
v___x_1087_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1));
v___x_1088_ = l_Lean_Name_append(v___x_1087_, v_fst_1084_);
v___x_1089_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1086_, v_options_1078_, v___x_1088_);
lean_dec(v___x_1088_);
if (v___x_1089_ == 0)
{
lean_dec(v_snd_1085_);
lean_dec(v_fst_1084_);
v_as_1068_ = v_tail_1083_;
goto _start;
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_snd_1085_);
v___x_1092_ = l_Lean_MessageData_ofFormat(v___x_1091_);
v___x_1093_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_fst_1084_, v___x_1092_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_dec_ref(v___x_1093_);
v_as_1068_ = v_tail_1083_;
goto _start;
}
else
{
lean_dec(v_tail_1083_);
return v___x_1093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___boxed(lean_object* v_as_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v_as_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1103_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = lean_box(0);
v___x_1105_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___x_1104_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg(){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
v___x_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___boxed(lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v_res_1111_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = l_Lean_maxRecDepthErrorMessage;
v___x_1118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3);
v___x_1120_ = l_Lean_MessageData_ofFormat(v___x_1119_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4);
v___x_1122_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2));
v___x_1123_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v___x_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(lean_object* v_ref_1124_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5);
v___x_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1127_, 0, v_ref_1124_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(lean_object* v_env_1132_, lean_object* v_declName_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
uint8_t v___x_1136_; lean_object* v_env_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1136_ = 0;
v_env_1137_ = l_Lean_Environment_setExporting(v_env_1132_, v___x_1136_);
lean_inc(v_declName_1133_);
v___x_1138_ = l_Lean_mkPrivateName(v_env_1137_, v_declName_1133_);
v___x_1139_ = 1;
lean_inc_ref(v_env_1137_);
v___x_1140_ = l_Lean_Environment_contains(v_env_1137_, v___x_1138_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1141_ = l_Lean_privateToUserName(v_declName_1133_);
v___x_1142_ = l_Lean_Environment_contains(v_env_1137_, v___x_1141_, v___x_1139_);
v___x_1143_ = lean_box(v___x_1142_);
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
lean_ctor_set(v___x_1144_, 1, v___y_1135_);
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec_ref(v_env_1137_);
lean_dec(v_declName_1133_);
v___x_1145_ = lean_box(v___x_1140_);
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v___y_1135_);
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed(lean_object* v_env_1147_, lean_object* v_declName_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(v_env_1147_, v_declName_1148_, v___y_1149_, v___y_1150_);
lean_dec_ref(v___y_1149_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(lean_object* v_x_1152_, lean_object* v___y_1153_){
_start:
{
if (lean_obj_tag(v_x_1152_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1155_; 
v_a_1154_ = lean_ctor_get(v_x_1152_, 0);
lean_inc(v_a_1154_);
v___x_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1155_, 0, v_a_1154_);
lean_ctor_set(v___x_1155_, 1, v___y_1153_);
return v___x_1155_;
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1157_; 
v_a_1156_ = lean_ctor_get(v_x_1152_, 0);
lean_inc(v_a_1156_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_a_1156_);
lean_ctor_set(v___x_1157_, 1, v___y_1153_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___boxed(lean_object* v_x_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_1158_, v___y_1159_);
lean_dec_ref(v_x_1158_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(lean_object* v_env_1161_, lean_object* v_stx_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1161_, v_stx_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
if (lean_obj_tag(v_a_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1175_; 
v_a_1167_ = lean_ctor_get(v___x_1165_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v___x_1165_, 0);
lean_dec(v_unused_1176_);
v___x_1169_ = v___x_1165_;
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1165_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1171_ = lean_box(0);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1171_);
v___x_1173_ = v___x_1169_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_a_1167_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
else
{
lean_object* v_val_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1205_; 
v_val_1177_ = lean_ctor_get(v_a_1166_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_a_1166_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1179_ = v_a_1166_;
v_isShared_1180_ = v_isSharedCheck_1205_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_val_1177_);
lean_dec(v_a_1166_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1205_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_snd_1181_; 
v_snd_1181_ = lean_ctor_get(v_val_1177_, 1);
lean_inc(v_snd_1181_);
lean_dec(v_val_1177_);
if (lean_obj_tag(v_snd_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
lean_del_object(v___x_1179_);
v_a_1182_ = lean_ctor_get(v___x_1165_, 1);
lean_inc(v_a_1182_);
lean_dec_ref(v___x_1165_);
v_a_1183_ = lean_ctor_get(v_snd_1181_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_snd_1181_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1185_ = v_snd_1181_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v_snd_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_1188_, v_a_1182_);
lean_dec_ref(v___x_1188_);
return v___x_1189_;
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1204_; 
v_a_1192_ = lean_ctor_get(v___x_1165_, 1);
lean_inc(v_a_1192_);
lean_dec_ref(v___x_1165_);
v_a_1193_ = lean_ctor_get(v_snd_1181_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_snd_1181_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1195_ = v_snd_1181_;
v_isShared_1196_ = v_isSharedCheck_1204_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v_snd_1181_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1204_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v_a_1193_);
v___x_1198_ = v___x_1179_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1198_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_1200_, v_a_1192_);
lean_dec_ref(v___x_1200_);
return v___x_1201_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
v_a_1206_ = lean_ctor_get(v___x_1165_, 0);
v_a_1207_ = lean_ctor_get(v___x_1165_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1165_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_inc(v_a_1206_);
lean_dec(v___x_1165_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1206_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_a_1207_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed(lean_object* v_env_1215_, lean_object* v_stx_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(v_env_1215_, v_stx_1216_, v___y_1217_, v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(lean_object* v_env_1220_, lean_object* v_options_1221_, lean_object* v_currNamespace_1222_, lean_object* v_openDecls_1223_, lean_object* v_n_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = l_Lean_ResolveName_resolveGlobalName(v_env_1220_, v_options_1221_, v_currNamespace_1222_, v_openDecls_1223_, v_n_1224_);
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
lean_ctor_set(v___x_1228_, 1, v___y_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed(lean_object* v_env_1229_, lean_object* v_options_1230_, lean_object* v_currNamespace_1231_, lean_object* v_openDecls_1232_, lean_object* v_n_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(v_env_1229_, v_options_1230_, v_currNamespace_1231_, v_openDecls_1232_, v_n_1233_, v___y_1234_, v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec_ref(v_options_1230_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(lean_object* v_currNamespace_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_currNamespace_1237_);
lean_ctor_set(v___x_1240_, 1, v___y_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(v_currNamespace_1241_, v___y_1242_, v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(lean_object* v_a_1245_, lean_object* v_x_1246_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_box(0);
return v___x_1247_;
}
else
{
lean_object* v_key_1248_; lean_object* v_value_1249_; lean_object* v_tail_1250_; uint8_t v___x_1251_; 
v_key_1248_ = lean_ctor_get(v_x_1246_, 0);
v_value_1249_ = lean_ctor_get(v_x_1246_, 1);
v_tail_1250_ = lean_ctor_get(v_x_1246_, 2);
v___x_1251_ = lean_name_eq(v_key_1248_, v_a_1245_);
if (v___x_1251_ == 0)
{
v_x_1246_ = v_tail_1250_;
goto _start;
}
else
{
lean_object* v___x_1253_; 
lean_inc(v_value_1249_);
v___x_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_value_1249_);
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg___boxed(lean_object* v_a_1254_, lean_object* v_x_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_1254_, v_x_1255_);
lean_dec(v_x_1255_);
lean_dec(v_a_1254_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(lean_object* v_m_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_buckets_1259_; lean_object* v___x_1260_; uint64_t v___y_1262_; 
v_buckets_1259_ = lean_ctor_get(v_m_1257_, 1);
v___x_1260_ = lean_array_get_size(v_buckets_1259_);
if (lean_obj_tag(v_a_1258_) == 0)
{
uint64_t v___x_1276_; 
v___x_1276_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
v___y_1262_ = v___x_1276_;
goto v___jp_1261_;
}
else
{
uint64_t v_hash_1277_; 
v_hash_1277_ = lean_ctor_get_uint64(v_a_1258_, sizeof(void*)*2);
v___y_1262_ = v_hash_1277_;
goto v___jp_1261_;
}
v___jp_1261_:
{
uint64_t v___x_1263_; uint64_t v___x_1264_; uint64_t v_fold_1265_; uint64_t v___x_1266_; uint64_t v___x_1267_; uint64_t v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1263_ = 32ULL;
v___x_1264_ = lean_uint64_shift_right(v___y_1262_, v___x_1263_);
v_fold_1265_ = lean_uint64_xor(v___y_1262_, v___x_1264_);
v___x_1266_ = 16ULL;
v___x_1267_ = lean_uint64_shift_right(v_fold_1265_, v___x_1266_);
v___x_1268_ = lean_uint64_xor(v_fold_1265_, v___x_1267_);
v___x_1269_ = lean_uint64_to_usize(v___x_1268_);
v___x_1270_ = lean_usize_of_nat(v___x_1260_);
v___x_1271_ = ((size_t)1ULL);
v___x_1272_ = lean_usize_sub(v___x_1270_, v___x_1271_);
v___x_1273_ = lean_usize_land(v___x_1269_, v___x_1272_);
v___x_1274_ = lean_array_uget_borrowed(v_buckets_1259_, v___x_1273_);
v___x_1275_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_1258_, v___x_1274_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg___boxed(lean_object* v_m_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec_ref(v_m_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(lean_object* v_keys_1281_, lean_object* v_i_1282_, lean_object* v_k_1283_){
_start:
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = lean_array_get_size(v_keys_1281_);
v___x_1285_ = lean_nat_dec_lt(v_i_1282_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_dec(v_i_1282_);
return v___x_1285_;
}
else
{
lean_object* v_k_x27_1286_; uint8_t v___x_1287_; 
v_k_x27_1286_ = lean_array_fget_borrowed(v_keys_1281_, v_i_1282_);
v___x_1287_ = l_Lean_instBEqExtraModUse_beq(v_k_1283_, v_k_x27_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_nat_add(v_i_1282_, v___x_1288_);
lean_dec(v_i_1282_);
v_i_1282_ = v___x_1289_;
goto _start;
}
else
{
lean_dec(v_i_1282_);
return v___x_1287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg___boxed(lean_object* v_keys_1291_, lean_object* v_i_1292_, lean_object* v_k_1293_){
_start:
{
uint8_t v_res_1294_; lean_object* v_r_1295_; 
v_res_1294_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_1291_, v_i_1292_, v_k_1293_);
lean_dec_ref(v_k_1293_);
lean_dec_ref(v_keys_1291_);
v_r_1295_ = lean_box(v_res_1294_);
return v_r_1295_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0(void){
_start:
{
size_t v___x_1296_; size_t v___x_1297_; size_t v___x_1298_; 
v___x_1296_ = ((size_t)5ULL);
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = lean_usize_shift_left(v___x_1297_, v___x_1296_);
return v___x_1298_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1(void){
_start:
{
size_t v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; 
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0);
v___x_1301_ = lean_usize_sub(v___x_1300_, v___x_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(lean_object* v_x_1302_, size_t v_x_1303_, lean_object* v_x_1304_){
_start:
{
if (lean_obj_tag(v_x_1302_) == 0)
{
lean_object* v_es_1305_; lean_object* v___x_1306_; size_t v___x_1307_; size_t v___x_1308_; size_t v___x_1309_; lean_object* v_j_1310_; lean_object* v___x_1311_; 
v_es_1305_ = lean_ctor_get(v_x_1302_, 0);
v___x_1306_ = lean_box(2);
v___x_1307_ = ((size_t)5ULL);
v___x_1308_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1);
v___x_1309_ = lean_usize_land(v_x_1303_, v___x_1308_);
v_j_1310_ = lean_usize_to_nat(v___x_1309_);
v___x_1311_ = lean_array_get_borrowed(v___x_1306_, v_es_1305_, v_j_1310_);
lean_dec(v_j_1310_);
switch(lean_obj_tag(v___x_1311_))
{
case 0:
{
lean_object* v_key_1312_; uint8_t v___x_1313_; 
v_key_1312_ = lean_ctor_get(v___x_1311_, 0);
v___x_1313_ = l_Lean_instBEqExtraModUse_beq(v_x_1304_, v_key_1312_);
return v___x_1313_;
}
case 1:
{
lean_object* v_node_1314_; size_t v___x_1315_; 
v_node_1314_ = lean_ctor_get(v___x_1311_, 0);
v___x_1315_ = lean_usize_shift_right(v_x_1303_, v___x_1307_);
v_x_1302_ = v_node_1314_;
v_x_1303_ = v___x_1315_;
goto _start;
}
default: 
{
uint8_t v___x_1317_; 
v___x_1317_ = 0;
return v___x_1317_;
}
}
}
else
{
lean_object* v_ks_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v_ks_1318_ = lean_ctor_get(v_x_1302_, 0);
v___x_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_ks_1318_, v___x_1319_, v_x_1304_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___boxed(lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_){
_start:
{
size_t v_x_20464__boxed_1324_; uint8_t v_res_1325_; lean_object* v_r_1326_; 
v_x_20464__boxed_1324_ = lean_unbox_usize(v_x_1322_);
lean_dec(v_x_1322_);
v_res_1325_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_1321_, v_x_20464__boxed_1324_, v_x_1323_);
lean_dec_ref(v_x_1323_);
lean_dec_ref(v_x_1321_);
v_r_1326_ = lean_box(v_res_1325_);
return v_r_1326_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(lean_object* v_x_1327_, lean_object* v_x_1328_){
_start:
{
uint64_t v___x_1329_; size_t v___x_1330_; uint8_t v___x_1331_; 
v___x_1329_ = l_Lean_instHashableExtraModUse_hash(v_x_1328_);
v___x_1330_ = lean_uint64_to_usize(v___x_1329_);
v___x_1331_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_1327_, v___x_1330_, v_x_1328_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg___boxed(lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
uint8_t v_res_1334_; lean_object* v_r_1335_; 
v_res_1334_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_1332_, v_x_1333_);
lean_dec_ref(v_x_1333_);
lean_dec_ref(v_x_1332_);
v_r_1335_ = lean_box(v_res_1334_);
return v_r_1335_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1));
v___x_1339_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0));
v___x_1340_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1339_, v___x_1338_);
return v___x_1340_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1341_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
return v___x_1343_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
return v___x_1345_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
v___x_1347_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
lean_ctor_set(v___x_1347_, 2, v___x_1346_);
lean_ctor_set(v___x_1347_, 3, v___x_1346_);
lean_ctor_set(v___x_1347_, 4, v___x_1346_);
lean_ctor_set(v___x_1347_, 5, v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9));
v___x_1353_ = l_Lean_stringToMessageData(v___x_1352_);
return v___x_1353_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11));
v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_1358_ = l_Lean_stringToMessageData(v___x_1357_);
return v___x_1358_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14(void){
_start:
{
lean_object* v_cls_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_cls_1359_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8));
v___x_1360_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1));
v___x_1361_ = l_Lean_Name_append(v___x_1360_, v_cls_1359_);
return v___x_1361_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15));
v___x_1364_ = l_Lean_stringToMessageData(v___x_1363_);
return v___x_1364_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17));
v___x_1367_ = l_Lean_stringToMessageData(v___x_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(lean_object* v_mod_1372_, uint8_t v_isMeta_1373_, lean_object* v_hint_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v_env_1383_; uint8_t v_isExporting_1384_; lean_object* v___x_1385_; lean_object* v_env_1386_; lean_object* v___x_1387_; lean_object* v_entry_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1382_ = lean_st_ref_get(v___y_1380_);
v_env_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc_ref(v_env_1383_);
lean_dec(v___x_1382_);
v_isExporting_1384_ = lean_ctor_get_uint8(v_env_1383_, sizeof(void*)*8);
lean_dec_ref(v_env_1383_);
v___x_1385_ = lean_st_ref_get(v___y_1380_);
v_env_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc_ref(v_env_1386_);
lean_dec(v___x_1385_);
v___x_1387_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
lean_inc(v_mod_1372_);
v_entry_1388_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1388_, 0, v_mod_1372_);
lean_ctor_set_uint8(v_entry_1388_, sizeof(void*)*1, v_isExporting_1384_);
lean_ctor_set_uint8(v_entry_1388_, sizeof(void*)*1 + 1, v_isMeta_1373_);
v___x_1389_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1390_ = lean_box(1);
v___x_1391_ = lean_box(0);
v___x_1434_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1387_, v___x_1389_, v_env_1386_, v___x_1390_, v___x_1391_);
v___x_1435_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_1434_, v_entry_1388_);
lean_dec(v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v_options_1436_; uint8_t v_hasTrace_1437_; 
v_options_1436_ = lean_ctor_get(v___y_1379_, 2);
v_hasTrace_1437_ = lean_ctor_get_uint8(v_options_1436_, sizeof(void*)*1);
if (v_hasTrace_1437_ == 0)
{
lean_dec(v_hint_1374_);
lean_dec(v_mod_1372_);
v___y_1393_ = v___y_1378_;
v___y_1394_ = v___y_1380_;
goto v___jp_1392_;
}
else
{
lean_object* v_inheritedTraceOptions_1438_; lean_object* v_cls_1439_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v_inheritedTraceOptions_1438_ = lean_ctor_get(v___y_1379_, 13);
v_cls_1439_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8));
v___x_1459_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
v___x_1460_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1438_, v_options_1436_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_dec(v_hint_1374_);
lean_dec(v_mod_1372_);
v___y_1393_ = v___y_1378_;
v___y_1394_ = v___y_1380_;
goto v___jp_1392_;
}
else
{
lean_object* v___x_1461_; lean_object* v___y_1463_; 
v___x_1461_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
if (v_isExporting_1384_ == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21));
v___y_1463_ = v___x_1470_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1471_; 
v___x_1471_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22));
v___y_1463_ = v___x_1471_;
goto v___jp_1462_;
}
v___jp_1462_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_inc_ref(v___y_1463_);
v___x_1464_ = l_Lean_stringToMessageData(v___y_1463_);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1461_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18);
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1465_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
if (v_isMeta_1373_ == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19));
v___y_1446_ = v___x_1467_;
v___y_1447_ = v___x_1468_;
goto v___jp_1445_;
}
else
{
lean_object* v___x_1469_; 
v___x_1469_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20));
v___y_1446_ = v___x_1467_;
v___y_1447_ = v___x_1469_;
goto v___jp_1445_;
}
}
}
v___jp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___y_1441_);
lean_ctor_set(v___x_1443_, 1, v___y_1442_);
v___x_1444_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_1439_, v___x_1443_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_dec_ref(v___x_1444_);
v___y_1393_ = v___y_1378_;
v___y_1394_ = v___y_1380_;
goto v___jp_1392_;
}
else
{
lean_dec_ref(v_entry_1388_);
return v___x_1444_;
}
}
v___jp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
lean_inc_ref(v___y_1447_);
v___x_1448_ = l_Lean_stringToMessageData(v___y_1447_);
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1446_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
v___x_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = l_Lean_MessageData_ofName(v_mod_1372_);
v___x_1453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1451_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = l_Lean_Name_isAnonymous(v_hint_1374_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
v___x_1456_ = l_Lean_MessageData_ofName(v_hint_1374_);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___y_1441_ = v___x_1453_;
v___y_1442_ = v___x_1457_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1458_; 
lean_dec(v_hint_1374_);
v___x_1458_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13);
v___y_1441_ = v___x_1453_;
v___y_1442_ = v___x_1458_;
goto v___jp_1440_;
}
}
}
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec_ref(v_entry_1388_);
lean_dec(v_hint_1374_);
lean_dec(v_mod_1372_);
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
v___jp_1392_:
{
lean_object* v___x_1395_; lean_object* v_toEnvExtension_1396_; lean_object* v_env_1397_; lean_object* v_nextMacroScope_1398_; lean_object* v_ngen_1399_; lean_object* v_auxDeclNGen_1400_; lean_object* v_traceState_1401_; lean_object* v_messages_1402_; lean_object* v_infoState_1403_; lean_object* v_snapshotTasks_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1432_; 
v___x_1395_ = lean_st_ref_take(v___y_1394_);
v_toEnvExtension_1396_ = lean_ctor_get(v___x_1389_, 0);
v_env_1397_ = lean_ctor_get(v___x_1395_, 0);
v_nextMacroScope_1398_ = lean_ctor_get(v___x_1395_, 1);
v_ngen_1399_ = lean_ctor_get(v___x_1395_, 2);
v_auxDeclNGen_1400_ = lean_ctor_get(v___x_1395_, 3);
v_traceState_1401_ = lean_ctor_get(v___x_1395_, 4);
v_messages_1402_ = lean_ctor_get(v___x_1395_, 6);
v_infoState_1403_ = lean_ctor_get(v___x_1395_, 7);
v_snapshotTasks_1404_ = lean_ctor_get(v___x_1395_, 8);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v___x_1395_, 5);
lean_dec(v_unused_1433_);
v___x_1406_ = v___x_1395_;
v_isShared_1407_ = v_isSharedCheck_1432_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snapshotTasks_1404_);
lean_inc(v_infoState_1403_);
lean_inc(v_messages_1402_);
lean_inc(v_traceState_1401_);
lean_inc(v_auxDeclNGen_1400_);
lean_inc(v_ngen_1399_);
lean_inc(v_nextMacroScope_1398_);
lean_inc(v_env_1397_);
lean_dec(v___x_1395_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1432_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_asyncMode_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v_asyncMode_1408_ = lean_ctor_get(v_toEnvExtension_1396_, 2);
v___x_1409_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1389_, v_env_1397_, v_entry_1388_, v_asyncMode_1408_, v___x_1391_);
v___x_1410_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 5, v___x_1410_);
lean_ctor_set(v___x_1406_, 0, v___x_1409_);
v___x_1412_ = v___x_1406_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_nextMacroScope_1398_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_ngen_1399_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v_auxDeclNGen_1400_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v_traceState_1401_);
lean_ctor_set(v_reuseFailAlloc_1431_, 5, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1431_, 6, v_messages_1402_);
lean_ctor_set(v_reuseFailAlloc_1431_, 7, v_infoState_1403_);
lean_ctor_set(v_reuseFailAlloc_1431_, 8, v_snapshotTasks_1404_);
v___x_1412_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v_mctx_1415_; lean_object* v_zetaDeltaFVarIds_1416_; lean_object* v_postponed_1417_; lean_object* v_diag_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1429_; 
v___x_1413_ = lean_st_ref_set(v___y_1394_, v___x_1412_);
v___x_1414_ = lean_st_ref_take(v___y_1393_);
v_mctx_1415_ = lean_ctor_get(v___x_1414_, 0);
v_zetaDeltaFVarIds_1416_ = lean_ctor_get(v___x_1414_, 2);
v_postponed_1417_ = lean_ctor_get(v___x_1414_, 3);
v_diag_1418_ = lean_ctor_get(v___x_1414_, 4);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1414_, 1);
lean_dec(v_unused_1430_);
v___x_1420_ = v___x_1414_;
v_isShared_1421_ = v_isSharedCheck_1429_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_diag_1418_);
lean_inc(v_postponed_1417_);
lean_inc(v_zetaDeltaFVarIds_1416_);
lean_inc(v_mctx_1415_);
lean_dec(v___x_1414_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1429_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v___x_1422_);
v___x_1424_ = v___x_1420_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_mctx_1415_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_zetaDeltaFVarIds_1416_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_postponed_1417_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v_diag_1418_);
v___x_1424_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_st_ref_set(v___y_1393_, v___x_1424_);
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___boxed(lean_object* v_mod_1474_, lean_object* v_isMeta_1475_, lean_object* v_hint_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v_isMeta_boxed_1484_; lean_object* v_res_1485_; 
v_isMeta_boxed_1484_ = lean_unbox(v_isMeta_1475_);
v_res_1485_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_mod_1474_, v_isMeta_boxed_1484_, v_hint_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(lean_object* v___x_1486_, lean_object* v_declName_1487_, lean_object* v_as_1488_, size_t v_sz_1489_, size_t v_i_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v___x_1499_; 
v___x_1499_ = lean_usize_dec_lt(v_i_1490_, v_sz_1489_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; 
lean_dec(v_declName_1487_);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_b_1491_);
return v___x_1500_;
}
else
{
lean_object* v___x_1501_; lean_object* v_modules_1502_; lean_object* v___x_1503_; lean_object* v_a_1504_; lean_object* v___x_1505_; lean_object* v_toImport_1506_; lean_object* v_module_1507_; uint8_t v___x_1508_; lean_object* v___x_1509_; 
v___x_1501_ = l_Lean_Environment_header(v___x_1486_);
v_modules_1502_ = lean_ctor_get(v___x_1501_, 3);
lean_inc_ref(v_modules_1502_);
lean_dec_ref(v___x_1501_);
v___x_1503_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1504_ = lean_array_uget_borrowed(v_as_1488_, v_i_1490_);
v___x_1505_ = lean_array_get(v___x_1503_, v_modules_1502_, v_a_1504_);
lean_dec_ref(v_modules_1502_);
v_toImport_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc_ref(v_toImport_1506_);
lean_dec(v___x_1505_);
v_module_1507_ = lean_ctor_get(v_toImport_1506_, 0);
lean_inc(v_module_1507_);
lean_dec_ref(v_toImport_1506_);
v___x_1508_ = 0;
lean_inc(v_declName_1487_);
v___x_1509_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_1507_, v___x_1508_, v_declName_1487_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v___x_1510_; size_t v___x_1511_; size_t v___x_1512_; 
lean_dec_ref(v___x_1509_);
v___x_1510_ = lean_box(0);
v___x_1511_ = ((size_t)1ULL);
v___x_1512_ = lean_usize_add(v_i_1490_, v___x_1511_);
v_i_1490_ = v___x_1512_;
v_b_1491_ = v___x_1510_;
goto _start;
}
else
{
lean_dec(v_declName_1487_);
return v___x_1509_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5___boxed(lean_object* v___x_1514_, lean_object* v_declName_1515_, lean_object* v_as_1516_, lean_object* v_sz_1517_, lean_object* v_i_1518_, lean_object* v_b_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
size_t v_sz_boxed_1527_; size_t v_i_boxed_1528_; lean_object* v_res_1529_; 
v_sz_boxed_1527_ = lean_unbox_usize(v_sz_1517_);
lean_dec(v_sz_1517_);
v_i_boxed_1528_ = lean_unbox_usize(v_i_1518_);
lean_dec(v_i_1518_);
v_res_1529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v___x_1514_, v_declName_1515_, v_as_1516_, v_sz_boxed_1527_, v_i_boxed_1528_, v_b_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec_ref(v_as_1516_);
lean_dec_ref(v___x_1514_);
return v_res_1529_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1532_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1));
v___x_1533_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0));
v___x_1534_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1533_, v___x_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(lean_object* v_declName_1537_, uint8_t v_isMeta_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; lean_object* v_env_1550_; lean_object* v___y_1552_; lean_object* v___x_1565_; 
v___x_1546_ = lean_st_ref_get(v___y_1544_);
v_env_1550_ = lean_ctor_get(v___x_1546_, 0);
lean_inc_ref(v_env_1550_);
lean_dec(v___x_1546_);
v___x_1565_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1550_, v_declName_1537_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_dec_ref(v_env_1550_);
lean_dec(v_declName_1537_);
goto v___jp_1547_;
}
else
{
lean_object* v_val_1566_; lean_object* v___x_1567_; lean_object* v_modules_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v_val_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_val_1566_);
lean_dec_ref(v___x_1565_);
v___x_1567_ = l_Lean_Environment_header(v_env_1550_);
v_modules_1568_ = lean_ctor_get(v___x_1567_, 3);
lean_inc_ref(v_modules_1568_);
lean_dec_ref(v___x_1567_);
v___x_1569_ = lean_array_get_size(v_modules_1568_);
v___x_1570_ = lean_nat_dec_lt(v_val_1566_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_dec_ref(v_modules_1568_);
lean_dec(v_val_1566_);
lean_dec_ref(v_env_1550_);
lean_dec(v_declName_1537_);
goto v___jp_1547_;
}
else
{
lean_object* v___x_1571_; lean_object* v_env_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___y_1576_; 
v___x_1571_ = lean_st_ref_get(v___y_1544_);
v_env_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc_ref(v_env_1572_);
lean_dec(v___x_1571_);
v___x_1573_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2);
v___x_1574_ = lean_array_fget(v_modules_1568_, v_val_1566_);
lean_dec(v_val_1566_);
lean_dec_ref(v_modules_1568_);
if (v_isMeta_1538_ == 0)
{
lean_dec_ref(v_env_1572_);
v___y_1576_ = v_isMeta_1538_;
goto v___jp_1575_;
}
else
{
uint8_t v___x_1587_; 
lean_inc(v_declName_1537_);
v___x_1587_ = l_Lean_isMarkedMeta(v_env_1572_, v_declName_1537_);
if (v___x_1587_ == 0)
{
v___y_1576_ = v_isMeta_1538_;
goto v___jp_1575_;
}
else
{
uint8_t v___x_1588_; 
v___x_1588_ = 0;
v___y_1576_ = v___x_1588_;
goto v___jp_1575_;
}
}
v___jp_1575_:
{
lean_object* v_toImport_1577_; lean_object* v_module_1578_; lean_object* v___x_1579_; 
v_toImport_1577_ = lean_ctor_get(v___x_1574_, 0);
lean_inc_ref(v_toImport_1577_);
lean_dec(v___x_1574_);
v_module_1578_ = lean_ctor_get(v_toImport_1577_, 0);
lean_inc(v_module_1578_);
lean_dec_ref(v_toImport_1577_);
lean_inc(v_declName_1537_);
v___x_1579_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_1578_, v___y_1576_, v_declName_1537_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec_ref(v___x_1579_);
v___x_1580_ = l_Lean_indirectModUseExt;
v___x_1581_ = lean_box(1);
v___x_1582_ = lean_box(0);
lean_inc_ref(v_env_1550_);
v___x_1583_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1573_, v___x_1580_, v_env_1550_, v___x_1581_, v___x_1582_);
v___x_1584_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_1583_, v_declName_1537_);
lean_dec(v___x_1583_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3));
v___y_1552_ = v___x_1585_;
goto v___jp_1551_;
}
else
{
lean_object* v_val_1586_; 
v_val_1586_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_val_1586_);
lean_dec_ref(v___x_1584_);
v___y_1552_ = v_val_1586_;
goto v___jp_1551_;
}
}
else
{
lean_dec_ref(v_env_1550_);
lean_dec(v_declName_1537_);
return v___x_1579_;
}
}
}
}
v___jp_1547_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
v___jp_1551_:
{
lean_object* v___x_1553_; size_t v_sz_1554_; size_t v___x_1555_; lean_object* v___x_1556_; 
v___x_1553_ = lean_box(0);
v_sz_1554_ = lean_array_size(v___y_1552_);
v___x_1555_ = ((size_t)0ULL);
v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v_env_1550_, v_declName_1537_, v___y_1552_, v_sz_1554_, v___x_1555_, v___x_1553_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec_ref(v___y_1552_);
lean_dec_ref(v_env_1550_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; 
v_unused_1564_ = lean_ctor_get(v___x_1556_, 0);
lean_dec(v_unused_1564_);
v___x_1558_ = v___x_1556_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_dec(v___x_1556_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v___x_1553_);
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1553_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
else
{
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___boxed(lean_object* v_declName_1589_, lean_object* v_isMeta_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
uint8_t v_isMeta_boxed_1598_; lean_object* v_res_1599_; 
v_isMeta_boxed_1598_ = lean_unbox(v_isMeta_1590_);
v_res_1599_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_declName_1589_, v_isMeta_boxed_1598_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(lean_object* v_as_x27_1600_, lean_object* v_b_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
if (lean_obj_tag(v_as_x27_1600_) == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_b_1601_);
return v___x_1609_;
}
else
{
lean_object* v_head_1610_; lean_object* v_tail_1611_; uint8_t v___x_1612_; lean_object* v___x_1613_; 
v_head_1610_ = lean_ctor_get(v_as_x27_1600_, 0);
lean_inc(v_head_1610_);
v_tail_1611_ = lean_ctor_get(v_as_x27_1600_, 1);
lean_inc(v_tail_1611_);
lean_dec_ref(v_as_x27_1600_);
v___x_1612_ = 1;
v___x_1613_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_head_1610_, v___x_1612_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v___x_1614_; 
lean_dec_ref(v___x_1613_);
v___x_1614_ = lean_box(0);
v_as_x27_1600_ = v_tail_1611_;
v_b_1601_ = v___x_1614_;
goto _start;
}
else
{
lean_dec(v_tail_1611_);
return v___x_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1616_, lean_object* v_b_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_1616_, v_b_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(lean_object* v_env_1626_, lean_object* v_currNamespace_1627_, lean_object* v_openDecls_1628_, lean_object* v_n_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = l_Lean_ResolveName_resolveNamespace(v_env_1626_, v_currNamespace_1627_, v_openDecls_1628_, v_n_1629_);
v___x_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_ctor_set(v___x_1633_, 1, v___y_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed(lean_object* v_env_1634_, lean_object* v_currNamespace_1635_, lean_object* v_openDecls_1636_, lean_object* v_n_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(v_env_1634_, v_currNamespace_1635_, v_openDecls_1636_, v_n_1637_, v___y_1638_, v___y_1639_);
lean_dec_ref(v___y_1638_);
return v_res_1640_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_box(1);
v___x_1642_ = l_Lean_MessageData_ofFormat(v___x_1641_);
return v___x_1642_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2));
v___x_1647_ = l_Lean_MessageData_ofFormat(v___x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(lean_object* v_x_1648_, lean_object* v_x_1649_){
_start:
{
if (lean_obj_tag(v_x_1649_) == 0)
{
return v_x_1648_;
}
else
{
lean_object* v_head_1650_; lean_object* v_tail_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1673_; 
v_head_1650_ = lean_ctor_get(v_x_1649_, 0);
v_tail_1651_ = lean_ctor_get(v_x_1649_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_x_1649_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1653_ = v_x_1649_;
v_isShared_1654_ = v_isSharedCheck_1673_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_tail_1651_);
lean_inc(v_head_1650_);
lean_dec(v_x_1649_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1673_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v_before_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1671_; 
v_before_1655_ = lean_ctor_get(v_head_1650_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_head_1650_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v_head_1650_, 1);
lean_dec(v_unused_1672_);
v___x_1657_ = v_head_1650_;
v_isShared_1658_ = v_isSharedCheck_1671_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_before_1655_);
lean_dec(v_head_1650_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1671_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_1658_ == 0)
{
lean_ctor_set_tag(v___x_1657_, 7);
lean_ctor_set(v___x_1657_, 1, v___x_1659_);
lean_ctor_set(v___x_1657_, 0, v_x_1648_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_x_1648_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3);
if (v_isShared_1654_ == 0)
{
lean_ctor_set_tag(v___x_1653_, 7);
lean_ctor_set(v___x_1653_, 1, v___x_1662_);
lean_ctor_set(v___x_1653_, 0, v___x_1661_);
v___x_1664_ = v___x_1653_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = l_Lean_MessageData_ofSyntax(v_before_1655_);
v___x_1666_ = l_Lean_indentD(v___x_1665_);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1664_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v_x_1648_ = v___x_1667_;
v_x_1649_ = v_tail_1651_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(lean_object* v_opts_1674_, lean_object* v_opt_1675_){
_start:
{
lean_object* v_name_1676_; lean_object* v_defValue_1677_; lean_object* v_map_1678_; lean_object* v___x_1679_; 
v_name_1676_ = lean_ctor_get(v_opt_1675_, 0);
v_defValue_1677_ = lean_ctor_get(v_opt_1675_, 1);
v_map_1678_ = lean_ctor_get(v_opts_1674_, 0);
v___x_1679_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1678_, v_name_1676_);
if (lean_obj_tag(v___x_1679_) == 0)
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_unbox(v_defValue_1677_);
return v___x_1680_;
}
else
{
lean_object* v_val_1681_; 
v_val_1681_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_val_1681_);
lean_dec_ref(v___x_1679_);
if (lean_obj_tag(v_val_1681_) == 1)
{
uint8_t v_v_1682_; 
v_v_1682_ = lean_ctor_get_uint8(v_val_1681_, 0);
lean_dec_ref(v_val_1681_);
return v_v_1682_;
}
else
{
uint8_t v___x_1683_; 
lean_dec(v_val_1681_);
v___x_1683_ = lean_unbox(v_defValue_1677_);
return v___x_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16___boxed(lean_object* v_opts_1684_, lean_object* v_opt_1685_){
_start:
{
uint8_t v_res_1686_; lean_object* v_r_1687_; 
v_res_1686_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_1684_, v_opt_1685_);
lean_dec_ref(v_opt_1685_);
lean_dec_ref(v_opts_1684_);
v_r_1687_ = lean_box(v_res_1686_);
return v_r_1687_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1));
v___x_1692_ = l_Lean_MessageData_ofFormat(v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(lean_object* v_msgData_1693_, lean_object* v_macroStack_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_options_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v_options_1697_ = lean_ctor_get(v___y_1695_, 2);
v___x_1698_ = l_Lean_Elab_pp_macroStack;
v___x_1699_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_options_1697_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
lean_dec(v_macroStack_1694_);
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v_msgData_1693_);
return v___x_1700_;
}
else
{
if (lean_obj_tag(v_macroStack_1694_) == 0)
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1701_, 0, v_msgData_1693_);
return v___x_1701_;
}
else
{
lean_object* v_head_1702_; lean_object* v_after_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1718_; 
v_head_1702_ = lean_ctor_get(v_macroStack_1694_, 0);
lean_inc(v_head_1702_);
v_after_1703_ = lean_ctor_get(v_head_1702_, 1);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_head_1702_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; 
v_unused_1719_ = lean_ctor_get(v_head_1702_, 0);
lean_dec(v_unused_1719_);
v___x_1705_ = v_head_1702_;
v_isShared_1706_ = v_isSharedCheck_1718_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_after_1703_);
lean_dec(v_head_1702_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1718_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1707_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_1706_ == 0)
{
lean_ctor_set_tag(v___x_1705_, 7);
lean_ctor_set(v___x_1705_, 1, v___x_1707_);
lean_ctor_set(v___x_1705_, 0, v_msgData_1693_);
v___x_1709_ = v___x_1705_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_msgData_1693_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v_msgData_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1710_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
v___x_1711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = l_Lean_MessageData_ofSyntax(v_after_1703_);
v___x_1713_ = l_Lean_indentD(v___x_1712_);
v_msgData_1714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1714_, 0, v___x_1711_);
lean_ctor_set(v_msgData_1714_, 1, v___x_1713_);
v___x_1715_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_1714_, v_macroStack_1694_);
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
return v___x_1716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___boxed(lean_object* v_msgData_1720_, lean_object* v_macroStack_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_1720_, v_macroStack_1721_, v___y_1722_);
lean_dec_ref(v___y_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(lean_object* v_msg_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_ref_1733_; lean_object* v___x_1734_; lean_object* v_a_1735_; lean_object* v_macroStack_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1747_; 
v_ref_1733_ = lean_ctor_get(v___y_1730_, 5);
v___x_1734_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_1725_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref(v___x_1734_);
v_macroStack_1736_ = lean_ctor_get(v___y_1726_, 1);
lean_inc_n(v_macroStack_1736_, 2);
v___x_1737_ = l_Lean_Elab_getBetterRef(v_ref_1733_, v_macroStack_1736_);
v___x_1738_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_a_1735_, v_macroStack_1736_, v___y_1730_);
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1747_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1747_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1737_);
lean_ctor_set(v___x_1743_, 1, v_a_1739_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 1);
lean_ctor_set(v___x_1741_, 0, v___x_1743_);
v___x_1745_ = v___x_1741_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg___boxed(lean_object* v_msg_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(lean_object* v_ref_1757_, lean_object* v_msg_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_fileName_1766_; lean_object* v_fileMap_1767_; lean_object* v_options_1768_; lean_object* v_currRecDepth_1769_; lean_object* v_maxRecDepth_1770_; lean_object* v_ref_1771_; lean_object* v_currNamespace_1772_; lean_object* v_openDecls_1773_; lean_object* v_initHeartbeats_1774_; lean_object* v_maxHeartbeats_1775_; lean_object* v_quotContext_1776_; lean_object* v_currMacroScope_1777_; uint8_t v_diag_1778_; lean_object* v_cancelTk_x3f_1779_; uint8_t v_suppressElabErrors_1780_; lean_object* v_inheritedTraceOptions_1781_; lean_object* v_ref_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_fileName_1766_ = lean_ctor_get(v___y_1763_, 0);
v_fileMap_1767_ = lean_ctor_get(v___y_1763_, 1);
v_options_1768_ = lean_ctor_get(v___y_1763_, 2);
v_currRecDepth_1769_ = lean_ctor_get(v___y_1763_, 3);
v_maxRecDepth_1770_ = lean_ctor_get(v___y_1763_, 4);
v_ref_1771_ = lean_ctor_get(v___y_1763_, 5);
v_currNamespace_1772_ = lean_ctor_get(v___y_1763_, 6);
v_openDecls_1773_ = lean_ctor_get(v___y_1763_, 7);
v_initHeartbeats_1774_ = lean_ctor_get(v___y_1763_, 8);
v_maxHeartbeats_1775_ = lean_ctor_get(v___y_1763_, 9);
v_quotContext_1776_ = lean_ctor_get(v___y_1763_, 10);
v_currMacroScope_1777_ = lean_ctor_get(v___y_1763_, 11);
v_diag_1778_ = lean_ctor_get_uint8(v___y_1763_, sizeof(void*)*14);
v_cancelTk_x3f_1779_ = lean_ctor_get(v___y_1763_, 12);
v_suppressElabErrors_1780_ = lean_ctor_get_uint8(v___y_1763_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1781_ = lean_ctor_get(v___y_1763_, 13);
v_ref_1782_ = l_Lean_replaceRef(v_ref_1757_, v_ref_1771_);
lean_inc_ref(v_inheritedTraceOptions_1781_);
lean_inc(v_cancelTk_x3f_1779_);
lean_inc(v_currMacroScope_1777_);
lean_inc(v_quotContext_1776_);
lean_inc(v_maxHeartbeats_1775_);
lean_inc(v_initHeartbeats_1774_);
lean_inc(v_openDecls_1773_);
lean_inc(v_currNamespace_1772_);
lean_inc(v_maxRecDepth_1770_);
lean_inc(v_currRecDepth_1769_);
lean_inc_ref(v_options_1768_);
lean_inc_ref(v_fileMap_1767_);
lean_inc_ref(v_fileName_1766_);
v___x_1783_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1783_, 0, v_fileName_1766_);
lean_ctor_set(v___x_1783_, 1, v_fileMap_1767_);
lean_ctor_set(v___x_1783_, 2, v_options_1768_);
lean_ctor_set(v___x_1783_, 3, v_currRecDepth_1769_);
lean_ctor_set(v___x_1783_, 4, v_maxRecDepth_1770_);
lean_ctor_set(v___x_1783_, 5, v_ref_1782_);
lean_ctor_set(v___x_1783_, 6, v_currNamespace_1772_);
lean_ctor_set(v___x_1783_, 7, v_openDecls_1773_);
lean_ctor_set(v___x_1783_, 8, v_initHeartbeats_1774_);
lean_ctor_set(v___x_1783_, 9, v_maxHeartbeats_1775_);
lean_ctor_set(v___x_1783_, 10, v_quotContext_1776_);
lean_ctor_set(v___x_1783_, 11, v_currMacroScope_1777_);
lean_ctor_set(v___x_1783_, 12, v_cancelTk_x3f_1779_);
lean_ctor_set(v___x_1783_, 13, v_inheritedTraceOptions_1781_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*14, v_diag_1778_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*14 + 1, v_suppressElabErrors_1780_);
v___x_1784_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___x_1783_, v___y_1764_);
lean_dec_ref(v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1785_, lean_object* v_msg_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_1785_, v_msg_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v_ref_1785_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(lean_object* v_x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; lean_object* v_env_1805_; lean_object* v_options_1806_; lean_object* v_currRecDepth_1807_; lean_object* v_maxRecDepth_1808_; lean_object* v_ref_1809_; lean_object* v_currNamespace_1810_; lean_object* v_openDecls_1811_; lean_object* v_quotContext_1812_; lean_object* v_currMacroScope_1813_; lean_object* v___x_1814_; lean_object* v_nextMacroScope_1815_; lean_object* v___f_1816_; lean_object* v___f_1817_; lean_object* v___f_1818_; lean_object* v___f_1819_; lean_object* v___f_1820_; lean_object* v_methods_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1804_ = lean_st_ref_get(v___y_1802_);
v_env_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc_ref_n(v_env_1805_, 4);
lean_dec(v___x_1804_);
v_options_1806_ = lean_ctor_get(v___y_1801_, 2);
v_currRecDepth_1807_ = lean_ctor_get(v___y_1801_, 3);
v_maxRecDepth_1808_ = lean_ctor_get(v___y_1801_, 4);
v_ref_1809_ = lean_ctor_get(v___y_1801_, 5);
v_currNamespace_1810_ = lean_ctor_get(v___y_1801_, 6);
v_openDecls_1811_ = lean_ctor_get(v___y_1801_, 7);
v_quotContext_1812_ = lean_ctor_get(v___y_1801_, 10);
v_currMacroScope_1813_ = lean_ctor_get(v___y_1801_, 11);
v___x_1814_ = lean_st_ref_get(v___y_1802_);
v_nextMacroScope_1815_ = lean_ctor_get(v___x_1814_, 1);
lean_inc(v_nextMacroScope_1815_);
lean_dec(v___x_1814_);
v___f_1816_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1816_, 0, v_env_1805_);
v___f_1817_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1817_, 0, v_env_1805_);
lean_inc_n(v_openDecls_1811_, 2);
lean_inc_n(v_currNamespace_1810_, 3);
v___f_1818_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1818_, 0, v_env_1805_);
lean_closure_set(v___f_1818_, 1, v_currNamespace_1810_);
lean_closure_set(v___f_1818_, 2, v_openDecls_1811_);
v___f_1819_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1819_, 0, v_currNamespace_1810_);
lean_inc_ref(v_options_1806_);
v___f_1820_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1820_, 0, v_env_1805_);
lean_closure_set(v___f_1820_, 1, v_options_1806_);
lean_closure_set(v___f_1820_, 2, v_currNamespace_1810_);
lean_closure_set(v___f_1820_, 3, v_openDecls_1811_);
v_methods_1821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1821_, 0, v___f_1816_);
lean_ctor_set(v_methods_1821_, 1, v___f_1819_);
lean_ctor_set(v_methods_1821_, 2, v___f_1817_);
lean_ctor_set(v_methods_1821_, 3, v___f_1818_);
lean_ctor_set(v_methods_1821_, 4, v___f_1820_);
lean_inc(v_ref_1809_);
lean_inc(v_maxRecDepth_1808_);
lean_inc(v_currRecDepth_1807_);
lean_inc(v_currMacroScope_1813_);
lean_inc(v_quotContext_1812_);
v___x_1822_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1822_, 0, v_methods_1821_);
lean_ctor_set(v___x_1822_, 1, v_quotContext_1812_);
lean_ctor_set(v___x_1822_, 2, v_currMacroScope_1813_);
lean_ctor_set(v___x_1822_, 3, v_currRecDepth_1807_);
lean_ctor_set(v___x_1822_, 4, v_maxRecDepth_1808_);
lean_ctor_set(v___x_1822_, 5, v_ref_1809_);
v___x_1823_ = lean_box(0);
v___x_1824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1824_, 0, v_nextMacroScope_1815_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
lean_ctor_set(v___x_1824_, 2, v___x_1823_);
v___x_1825_ = lean_apply_2(v_x_1796_, v___x_1822_, v___x_1824_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v_a_1827_; lean_object* v_macroScope_1828_; lean_object* v_traceMsgs_1829_; lean_object* v_expandedMacroDecls_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 1);
lean_inc(v_a_1826_);
v_a_1827_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1827_);
lean_dec_ref(v___x_1825_);
v_macroScope_1828_ = lean_ctor_get(v_a_1826_, 0);
lean_inc(v_macroScope_1828_);
v_traceMsgs_1829_ = lean_ctor_get(v_a_1826_, 1);
lean_inc(v_traceMsgs_1829_);
v_expandedMacroDecls_1830_ = lean_ctor_get(v_a_1826_, 2);
lean_inc(v_expandedMacroDecls_1830_);
lean_dec(v_a_1826_);
v___x_1831_ = lean_box(0);
v___x_1832_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_expandedMacroDecls_1830_, v___x_1831_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v___x_1833_; lean_object* v_env_1834_; lean_object* v_ngen_1835_; lean_object* v_auxDeclNGen_1836_; lean_object* v_traceState_1837_; lean_object* v_cache_1838_; lean_object* v_messages_1839_; lean_object* v_infoState_1840_; lean_object* v_snapshotTasks_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1867_; 
lean_dec_ref(v___x_1832_);
v___x_1833_ = lean_st_ref_take(v___y_1802_);
v_env_1834_ = lean_ctor_get(v___x_1833_, 0);
v_ngen_1835_ = lean_ctor_get(v___x_1833_, 2);
v_auxDeclNGen_1836_ = lean_ctor_get(v___x_1833_, 3);
v_traceState_1837_ = lean_ctor_get(v___x_1833_, 4);
v_cache_1838_ = lean_ctor_get(v___x_1833_, 5);
v_messages_1839_ = lean_ctor_get(v___x_1833_, 6);
v_infoState_1840_ = lean_ctor_get(v___x_1833_, 7);
v_snapshotTasks_1841_ = lean_ctor_get(v___x_1833_, 8);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1867_ == 0)
{
lean_object* v_unused_1868_; 
v_unused_1868_ = lean_ctor_get(v___x_1833_, 1);
lean_dec(v_unused_1868_);
v___x_1843_ = v___x_1833_;
v_isShared_1844_ = v_isSharedCheck_1867_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_snapshotTasks_1841_);
lean_inc(v_infoState_1840_);
lean_inc(v_messages_1839_);
lean_inc(v_cache_1838_);
lean_inc(v_traceState_1837_);
lean_inc(v_auxDeclNGen_1836_);
lean_inc(v_ngen_1835_);
lean_inc(v_env_1834_);
lean_dec(v___x_1833_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1867_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v_macroScope_1828_);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_env_1834_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_macroScope_1828_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_ngen_1835_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_auxDeclNGen_1836_);
lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_traceState_1837_);
lean_ctor_set(v_reuseFailAlloc_1866_, 5, v_cache_1838_);
lean_ctor_set(v_reuseFailAlloc_1866_, 6, v_messages_1839_);
lean_ctor_set(v_reuseFailAlloc_1866_, 7, v_infoState_1840_);
lean_ctor_set(v_reuseFailAlloc_1866_, 8, v_snapshotTasks_1841_);
v___x_1846_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_st_ref_set(v___y_1802_, v___x_1846_);
v___x_1848_ = l_List_reverse___redArg(v_traceMsgs_1829_);
v___x_1849_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v___x_1848_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v___x_1849_, 0);
lean_dec(v_unused_1857_);
v___x_1851_ = v___x_1849_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_dec(v___x_1849_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v_a_1827_);
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1827_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_a_1827_);
v_a_1858_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1849_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1849_);
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
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_traceMsgs_1829_);
lean_dec(v_macroScope_1828_);
lean_dec(v_a_1827_);
v_a_1869_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1832_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1832_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1877_; 
v_a_1877_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1825_);
if (lean_obj_tag(v_a_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v_a_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v_a_1878_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_a_1878_);
v_a_1879_ = lean_ctor_get(v_a_1877_, 1);
lean_inc_ref(v_a_1879_);
lean_dec_ref(v_a_1877_);
v___x_1880_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0));
v___x_1881_ = lean_string_dec_eq(v_a_1879_, v___x_1880_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_a_1879_);
v___x_1883_ = l_Lean_MessageData_ofFormat(v___x_1882_);
v___x_1884_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_a_1878_, v___x_1883_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v_a_1878_);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; 
lean_dec_ref(v_a_1879_);
v___x_1885_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_a_1878_);
return v___x_1885_;
}
}
else
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v___x_1886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___boxed(lean_object* v_x_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(lean_object* v_t_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; lean_object* v_infoState_1900_; uint8_t v_enabled_1901_; 
v___x_1899_ = lean_st_ref_get(v___y_1897_);
v_infoState_1900_ = lean_ctor_get(v___x_1899_, 7);
lean_inc_ref(v_infoState_1900_);
lean_dec(v___x_1899_);
v_enabled_1901_ = lean_ctor_get_uint8(v_infoState_1900_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1900_);
if (v_enabled_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec_ref(v_t_1896_);
v___x_1902_ = lean_box(0);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; lean_object* v_infoState_1905_; lean_object* v_env_1906_; lean_object* v_nextMacroScope_1907_; lean_object* v_ngen_1908_; lean_object* v_auxDeclNGen_1909_; lean_object* v_traceState_1910_; lean_object* v_cache_1911_; lean_object* v_messages_1912_; lean_object* v_snapshotTasks_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1935_; 
v___x_1904_ = lean_st_ref_take(v___y_1897_);
v_infoState_1905_ = lean_ctor_get(v___x_1904_, 7);
v_env_1906_ = lean_ctor_get(v___x_1904_, 0);
v_nextMacroScope_1907_ = lean_ctor_get(v___x_1904_, 1);
v_ngen_1908_ = lean_ctor_get(v___x_1904_, 2);
v_auxDeclNGen_1909_ = lean_ctor_get(v___x_1904_, 3);
v_traceState_1910_ = lean_ctor_get(v___x_1904_, 4);
v_cache_1911_ = lean_ctor_get(v___x_1904_, 5);
v_messages_1912_ = lean_ctor_get(v___x_1904_, 6);
v_snapshotTasks_1913_ = lean_ctor_get(v___x_1904_, 8);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1915_ = v___x_1904_;
v_isShared_1916_ = v_isSharedCheck_1935_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_snapshotTasks_1913_);
lean_inc(v_infoState_1905_);
lean_inc(v_messages_1912_);
lean_inc(v_cache_1911_);
lean_inc(v_traceState_1910_);
lean_inc(v_auxDeclNGen_1909_);
lean_inc(v_ngen_1908_);
lean_inc(v_nextMacroScope_1907_);
lean_inc(v_env_1906_);
lean_dec(v___x_1904_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1935_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
uint8_t v_enabled_1917_; lean_object* v_assignment_1918_; lean_object* v_lazyAssignment_1919_; lean_object* v_trees_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1934_; 
v_enabled_1917_ = lean_ctor_get_uint8(v_infoState_1905_, sizeof(void*)*3);
v_assignment_1918_ = lean_ctor_get(v_infoState_1905_, 0);
v_lazyAssignment_1919_ = lean_ctor_get(v_infoState_1905_, 1);
v_trees_1920_ = lean_ctor_get(v_infoState_1905_, 2);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_infoState_1905_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1922_ = v_infoState_1905_;
v_isShared_1923_ = v_isSharedCheck_1934_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_trees_1920_);
lean_inc(v_lazyAssignment_1919_);
lean_inc(v_assignment_1918_);
lean_dec(v_infoState_1905_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1934_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = l_Lean_PersistentArray_push___redArg(v_trees_1920_, v_t_1896_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 2, v___x_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_assignment_1918_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_lazyAssignment_1919_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v___x_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1933_, sizeof(void*)*3, v_enabled_1917_);
v___x_1926_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1928_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 7, v___x_1926_);
v___x_1928_ = v___x_1915_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_env_1906_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_nextMacroScope_1907_);
lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_ngen_1908_);
lean_ctor_set(v_reuseFailAlloc_1932_, 3, v_auxDeclNGen_1909_);
lean_ctor_set(v_reuseFailAlloc_1932_, 4, v_traceState_1910_);
lean_ctor_set(v_reuseFailAlloc_1932_, 5, v_cache_1911_);
lean_ctor_set(v_reuseFailAlloc_1932_, 6, v_messages_1912_);
lean_ctor_set(v_reuseFailAlloc_1932_, 7, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1932_, 8, v_snapshotTasks_1913_);
v___x_1928_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = lean_st_ref_set(v___y_1897_, v___x_1928_);
v___x_1930_ = lean_box(0);
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
return v___x_1931_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg___boxed(lean_object* v_t_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_1936_, v___y_1937_);
lean_dec(v___y_1937_);
return v_res_1939_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = lean_unsigned_to_nat(32u);
v___x_1941_ = lean_mk_empty_array_with_capacity(v___x_1940_);
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
return v___x_1942_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1(void){
_start:
{
size_t v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1943_ = ((size_t)5ULL);
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = lean_unsigned_to_nat(32u);
v___x_1946_ = lean_mk_empty_array_with_capacity(v___x_1945_);
v___x_1947_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0);
v___x_1948_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v___x_1946_);
lean_ctor_set(v___x_1948_, 2, v___x_1944_);
lean_ctor_set(v___x_1948_, 3, v___x_1944_);
lean_ctor_set_usize(v___x_1948_, 4, v___x_1943_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(lean_object* v_t_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; lean_object* v_infoState_1958_; uint8_t v_enabled_1959_; 
v___x_1957_ = lean_st_ref_get(v___y_1955_);
v_infoState_1958_ = lean_ctor_get(v___x_1957_, 7);
lean_inc_ref(v_infoState_1958_);
lean_dec(v___x_1957_);
v_enabled_1959_ = lean_ctor_get_uint8(v_infoState_1958_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1958_);
if (v_enabled_1959_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec_ref(v_t_1949_);
v___x_1960_ = lean_box(0);
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1962_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1);
v___x_1963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1963_, 0, v_t_1949_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v___x_1963_, v___y_1955_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___boxed(lean_object* v_t_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v_t_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(lean_object* v_info_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_info_1974_);
v___x_1983_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_1982_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1___boxed(lean_object* v_info_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v_info_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1992_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(uint8_t v___y_2000_, uint8_t v_suppressElabErrors_2001_, lean_object* v_x_2002_){
_start:
{
if (lean_obj_tag(v_x_2002_) == 1)
{
lean_object* v_pre_2003_; 
v_pre_2003_ = lean_ctor_get(v_x_2002_, 0);
switch(lean_obj_tag(v_pre_2003_))
{
case 1:
{
lean_object* v_pre_2004_; 
v_pre_2004_ = lean_ctor_get(v_pre_2003_, 0);
switch(lean_obj_tag(v_pre_2004_))
{
case 0:
{
lean_object* v_str_2005_; lean_object* v_str_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_str_2005_ = lean_ctor_get(v_x_2002_, 1);
v_str_2006_ = lean_ctor_get(v_pre_2003_, 1);
v___x_2007_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0));
v___x_2008_ = lean_string_dec_eq(v_str_2006_, v___x_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1));
v___x_2010_ = lean_string_dec_eq(v_str_2006_, v___x_2009_);
if (v___x_2010_ == 0)
{
return v___y_2000_;
}
else
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2));
v___x_2012_ = lean_string_dec_eq(v_str_2005_, v___x_2011_);
if (v___x_2012_ == 0)
{
return v___y_2000_;
}
else
{
return v_suppressElabErrors_2001_;
}
}
}
else
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3));
v___x_2014_ = lean_string_dec_eq(v_str_2005_, v___x_2013_);
if (v___x_2014_ == 0)
{
return v___y_2000_;
}
else
{
return v_suppressElabErrors_2001_;
}
}
}
case 1:
{
lean_object* v_pre_2015_; 
v_pre_2015_ = lean_ctor_get(v_pre_2004_, 0);
if (lean_obj_tag(v_pre_2015_) == 0)
{
lean_object* v_str_2016_; lean_object* v_str_2017_; lean_object* v_str_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v_str_2016_ = lean_ctor_get(v_x_2002_, 1);
v_str_2017_ = lean_ctor_get(v_pre_2003_, 1);
v_str_2018_ = lean_ctor_get(v_pre_2004_, 1);
v___x_2019_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4));
v___x_2020_ = lean_string_dec_eq(v_str_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
return v___y_2000_;
}
else
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5));
v___x_2022_ = lean_string_dec_eq(v_str_2017_, v___x_2021_);
if (v___x_2022_ == 0)
{
return v___y_2000_;
}
else
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6));
v___x_2024_ = lean_string_dec_eq(v_str_2016_, v___x_2023_);
if (v___x_2024_ == 0)
{
return v___y_2000_;
}
else
{
return v_suppressElabErrors_2001_;
}
}
}
}
else
{
return v___y_2000_;
}
}
default: 
{
return v___y_2000_;
}
}
}
case 0:
{
lean_object* v_str_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_str_2025_ = lean_ctor_get(v_x_2002_, 1);
v___x_2026_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0));
v___x_2027_ = lean_string_dec_eq(v_str_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
return v___y_2000_;
}
else
{
return v_suppressElabErrors_2001_;
}
}
default: 
{
return v___y_2000_;
}
}
}
else
{
return v___y_2000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v___y_2028_, lean_object* v_suppressElabErrors_2029_, lean_object* v_x_2030_){
_start:
{
uint8_t v___y_21544__boxed_2031_; uint8_t v_suppressElabErrors_boxed_2032_; uint8_t v_res_2033_; lean_object* v_r_2034_; 
v___y_21544__boxed_2031_ = lean_unbox(v___y_2028_);
v_suppressElabErrors_boxed_2032_ = lean_unbox(v_suppressElabErrors_2029_);
v_res_2033_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(v___y_21544__boxed_2031_, v_suppressElabErrors_boxed_2032_, v_x_2030_);
lean_dec(v_x_2030_);
v_r_2034_ = lean_box(v_res_2033_);
return v_r_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(lean_object* v_ref_2035_, lean_object* v_msgData_2036_, uint8_t v_severity_2037_, uint8_t v_isSilent_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___y_2045_; uint8_t v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2081_; uint8_t v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; uint8_t v___y_2086_; uint8_t v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2106_; uint8_t v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; uint8_t v___y_2111_; uint8_t v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2117_; lean_object* v___y_2118_; uint8_t v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; uint8_t v___y_2122_; uint8_t v___y_2123_; uint8_t v___x_2128_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; uint8_t v___y_2134_; uint8_t v___y_2135_; uint8_t v___y_2136_; uint8_t v___y_2138_; uint8_t v___x_2153_; 
v___x_2128_ = 2;
v___x_2153_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2037_, v___x_2128_);
if (v___x_2153_ == 0)
{
v___y_2138_ = v___x_2153_;
goto v___jp_2137_;
}
else
{
uint8_t v___x_2154_; 
lean_inc_ref(v_msgData_2036_);
v___x_2154_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2036_);
v___y_2138_ = v___x_2154_;
goto v___jp_2137_;
}
v___jp_2044_:
{
lean_object* v___x_2054_; lean_object* v_currNamespace_2055_; lean_object* v_openDecls_2056_; lean_object* v_env_2057_; lean_object* v_nextMacroScope_2058_; lean_object* v_ngen_2059_; lean_object* v_auxDeclNGen_2060_; lean_object* v_traceState_2061_; lean_object* v_cache_2062_; lean_object* v_messages_2063_; lean_object* v_infoState_2064_; lean_object* v_snapshotTasks_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2079_; 
v___x_2054_ = lean_st_ref_take(v___y_2053_);
v_currNamespace_2055_ = lean_ctor_get(v___y_2052_, 6);
v_openDecls_2056_ = lean_ctor_get(v___y_2052_, 7);
v_env_2057_ = lean_ctor_get(v___x_2054_, 0);
v_nextMacroScope_2058_ = lean_ctor_get(v___x_2054_, 1);
v_ngen_2059_ = lean_ctor_get(v___x_2054_, 2);
v_auxDeclNGen_2060_ = lean_ctor_get(v___x_2054_, 3);
v_traceState_2061_ = lean_ctor_get(v___x_2054_, 4);
v_cache_2062_ = lean_ctor_get(v___x_2054_, 5);
v_messages_2063_ = lean_ctor_get(v___x_2054_, 6);
v_infoState_2064_ = lean_ctor_get(v___x_2054_, 7);
v_snapshotTasks_2065_ = lean_ctor_get(v___x_2054_, 8);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2067_ = v___x_2054_;
v_isShared_2068_ = v_isSharedCheck_2079_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_snapshotTasks_2065_);
lean_inc(v_infoState_2064_);
lean_inc(v_messages_2063_);
lean_inc(v_cache_2062_);
lean_inc(v_traceState_2061_);
lean_inc(v_auxDeclNGen_2060_);
lean_inc(v_ngen_2059_);
lean_inc(v_nextMacroScope_2058_);
lean_inc(v_env_2057_);
lean_dec(v___x_2054_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2079_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
lean_inc(v_openDecls_2056_);
lean_inc(v_currNamespace_2055_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_currNamespace_2055_);
lean_ctor_set(v___x_2069_, 1, v_openDecls_2056_);
v___x_2070_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___y_2049_);
lean_inc_ref(v___y_2047_);
lean_inc_ref(v___y_2050_);
v___x_2071_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2071_, 0, v___y_2050_);
lean_ctor_set(v___x_2071_, 1, v___y_2045_);
lean_ctor_set(v___x_2071_, 2, v___y_2048_);
lean_ctor_set(v___x_2071_, 3, v___y_2047_);
lean_ctor_set(v___x_2071_, 4, v___x_2070_);
lean_ctor_set_uint8(v___x_2071_, sizeof(void*)*5, v___y_2046_);
lean_ctor_set_uint8(v___x_2071_, sizeof(void*)*5 + 1, v___y_2051_);
lean_ctor_set_uint8(v___x_2071_, sizeof(void*)*5 + 2, v_isSilent_2038_);
v___x_2072_ = l_Lean_MessageLog_add(v___x_2071_, v_messages_2063_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 6, v___x_2072_);
v___x_2074_ = v___x_2067_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_env_2057_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_nextMacroScope_2058_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_ngen_2059_);
lean_ctor_set(v_reuseFailAlloc_2078_, 3, v_auxDeclNGen_2060_);
lean_ctor_set(v_reuseFailAlloc_2078_, 4, v_traceState_2061_);
lean_ctor_set(v_reuseFailAlloc_2078_, 5, v_cache_2062_);
lean_ctor_set(v_reuseFailAlloc_2078_, 6, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2078_, 7, v_infoState_2064_);
lean_ctor_set(v_reuseFailAlloc_2078_, 8, v_snapshotTasks_2065_);
v___x_2074_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_st_ref_set(v___y_2053_, v___x_2074_);
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
}
}
v___jp_2080_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2104_; 
v___x_2089_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2036_);
v___x_2090_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v___x_2089_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2104_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2104_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_inc_ref_n(v___y_2085_, 2);
v___x_2095_ = l_Lean_FileMap_toPosition(v___y_2085_, v___y_2083_);
lean_dec(v___y_2083_);
v___x_2096_ = l_Lean_FileMap_toPosition(v___y_2085_, v___y_2088_);
lean_dec(v___y_2088_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
v___x_2098_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
if (v___y_2086_ == 0)
{
lean_del_object(v___x_2093_);
lean_dec_ref(v___y_2081_);
v___y_2045_ = v___x_2095_;
v___y_2046_ = v___y_2082_;
v___y_2047_ = v___x_2098_;
v___y_2048_ = v___x_2097_;
v___y_2049_ = v_a_2091_;
v___y_2050_ = v___y_2084_;
v___y_2051_ = v___y_2087_;
v___y_2052_ = v___y_2041_;
v___y_2053_ = v___y_2042_;
goto v___jp_2044_;
}
else
{
uint8_t v___x_2099_; 
lean_inc(v_a_2091_);
v___x_2099_ = l_Lean_MessageData_hasTag(v___y_2081_, v_a_2091_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
lean_dec_ref(v___x_2097_);
lean_dec_ref(v___x_2095_);
lean_dec(v_a_2091_);
v___x_2100_ = lean_box(0);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2100_);
v___x_2102_ = v___x_2093_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
else
{
lean_del_object(v___x_2093_);
v___y_2045_ = v___x_2095_;
v___y_2046_ = v___y_2082_;
v___y_2047_ = v___x_2098_;
v___y_2048_ = v___x_2097_;
v___y_2049_ = v_a_2091_;
v___y_2050_ = v___y_2084_;
v___y_2051_ = v___y_2087_;
v___y_2052_ = v___y_2041_;
v___y_2053_ = v___y_2042_;
goto v___jp_2044_;
}
}
}
}
v___jp_2105_:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_Syntax_getTailPos_x3f(v___y_2110_, v___y_2107_);
lean_dec(v___y_2110_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_inc(v___y_2113_);
v___y_2081_ = v___y_2106_;
v___y_2082_ = v___y_2107_;
v___y_2083_ = v___y_2113_;
v___y_2084_ = v___y_2108_;
v___y_2085_ = v___y_2109_;
v___y_2086_ = v___y_2112_;
v___y_2087_ = v___y_2111_;
v___y_2088_ = v___y_2113_;
goto v___jp_2080_;
}
else
{
lean_object* v_val_2115_; 
v_val_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_val_2115_);
lean_dec_ref(v___x_2114_);
v___y_2081_ = v___y_2106_;
v___y_2082_ = v___y_2107_;
v___y_2083_ = v___y_2113_;
v___y_2084_ = v___y_2108_;
v___y_2085_ = v___y_2109_;
v___y_2086_ = v___y_2112_;
v___y_2087_ = v___y_2111_;
v___y_2088_ = v_val_2115_;
goto v___jp_2080_;
}
}
v___jp_2116_:
{
lean_object* v_ref_2124_; lean_object* v___x_2125_; 
v_ref_2124_ = l_Lean_replaceRef(v_ref_2035_, v___y_2118_);
v___x_2125_ = l_Lean_Syntax_getPos_x3f(v_ref_2124_, v___y_2119_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_unsigned_to_nat(0u);
v___y_2106_ = v___y_2117_;
v___y_2107_ = v___y_2119_;
v___y_2108_ = v___y_2120_;
v___y_2109_ = v___y_2121_;
v___y_2110_ = v_ref_2124_;
v___y_2111_ = v___y_2123_;
v___y_2112_ = v___y_2122_;
v___y_2113_ = v___x_2126_;
goto v___jp_2105_;
}
else
{
lean_object* v_val_2127_; 
v_val_2127_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_val_2127_);
lean_dec_ref(v___x_2125_);
v___y_2106_ = v___y_2117_;
v___y_2107_ = v___y_2119_;
v___y_2108_ = v___y_2120_;
v___y_2109_ = v___y_2121_;
v___y_2110_ = v_ref_2124_;
v___y_2111_ = v___y_2123_;
v___y_2112_ = v___y_2122_;
v___y_2113_ = v_val_2127_;
goto v___jp_2105_;
}
}
v___jp_2129_:
{
if (v___y_2136_ == 0)
{
v___y_2117_ = v___y_2131_;
v___y_2118_ = v___y_2130_;
v___y_2119_ = v___y_2135_;
v___y_2120_ = v___y_2132_;
v___y_2121_ = v___y_2133_;
v___y_2122_ = v___y_2134_;
v___y_2123_ = v_severity_2037_;
goto v___jp_2116_;
}
else
{
v___y_2117_ = v___y_2131_;
v___y_2118_ = v___y_2130_;
v___y_2119_ = v___y_2135_;
v___y_2120_ = v___y_2132_;
v___y_2121_ = v___y_2133_;
v___y_2122_ = v___y_2134_;
v___y_2123_ = v___x_2128_;
goto v___jp_2116_;
}
}
v___jp_2137_:
{
if (v___y_2138_ == 0)
{
lean_object* v_fileName_2139_; lean_object* v_fileMap_2140_; lean_object* v_options_2141_; lean_object* v_ref_2142_; uint8_t v_suppressElabErrors_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; uint8_t v___x_2147_; uint8_t v___x_2148_; 
v_fileName_2139_ = lean_ctor_get(v___y_2041_, 0);
v_fileMap_2140_ = lean_ctor_get(v___y_2041_, 1);
v_options_2141_ = lean_ctor_get(v___y_2041_, 2);
v_ref_2142_ = lean_ctor_get(v___y_2041_, 5);
v_suppressElabErrors_2143_ = lean_ctor_get_uint8(v___y_2041_, sizeof(void*)*14 + 1);
v___x_2144_ = lean_box(v___y_2138_);
v___x_2145_ = lean_box(v_suppressElabErrors_2143_);
v___f_2146_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2146_, 0, v___x_2144_);
lean_closure_set(v___f_2146_, 1, v___x_2145_);
v___x_2147_ = 1;
v___x_2148_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2037_, v___x_2147_);
if (v___x_2148_ == 0)
{
v___y_2130_ = v_ref_2142_;
v___y_2131_ = v___f_2146_;
v___y_2132_ = v_fileName_2139_;
v___y_2133_ = v_fileMap_2140_;
v___y_2134_ = v_suppressElabErrors_2143_;
v___y_2135_ = v___y_2138_;
v___y_2136_ = v___x_2148_;
goto v___jp_2129_;
}
else
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = l_Lean_warningAsError;
v___x_2150_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_options_2141_, v___x_2149_);
v___y_2130_ = v_ref_2142_;
v___y_2131_ = v___f_2146_;
v___y_2132_ = v_fileName_2139_;
v___y_2133_ = v_fileMap_2140_;
v___y_2134_ = v_suppressElabErrors_2143_;
v___y_2135_ = v___y_2138_;
v___y_2136_ = v___x_2150_;
goto v___jp_2129_;
}
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
lean_dec_ref(v_msgData_2036_);
v___x_2151_ = lean_box(0);
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___boxed(lean_object* v_ref_2155_, lean_object* v_msgData_2156_, lean_object* v_severity_2157_, lean_object* v_isSilent_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
uint8_t v_severity_boxed_2164_; uint8_t v_isSilent_boxed_2165_; lean_object* v_res_2166_; 
v_severity_boxed_2164_ = lean_unbox(v_severity_2157_);
v_isSilent_boxed_2165_ = lean_unbox(v_isSilent_2158_);
v_res_2166_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2155_, v_msgData_2156_, v_severity_boxed_2164_, v_isSilent_boxed_2165_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v_ref_2155_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(lean_object* v_ref_2167_, lean_object* v_msgData_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
uint8_t v___x_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = 2;
v___x_2177_ = 0;
v___x_2178_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2167_, v_msgData_2168_, v___x_2176_, v___x_2177_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5___boxed(lean_object* v_ref_2179_, lean_object* v_msgData_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v_ref_2179_, v_msgData_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v_ref_2179_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(lean_object* v_ref_2189_, lean_object* v_msgData_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
uint8_t v___x_2198_; uint8_t v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = 1;
v___x_2199_ = 0;
v___x_2200_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2189_, v_msgData_2190_, v___x_2198_, v___x_2199_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4___boxed(lean_object* v_ref_2201_, lean_object* v_msgData_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v_ref_2201_, v_msgData_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v_ref_2201_);
return v_res_2210_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0));
v___x_2213_ = l_Lean_stringToMessageData(v___x_2212_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2));
v___x_2216_ = l_Lean_stringToMessageData(v___x_2215_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4));
v___x_2219_ = l_Lean_stringToMessageData(v___x_2218_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12));
v___x_2231_ = l_Lean_stringToMessageData(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14));
v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16));
v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(lean_object* v_stx_2238_, lean_object* v_expType_x3f_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
uint8_t v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; uint8_t v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v_fst_2340_; lean_object* v_snd_2341_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; uint8_t v___y_2369_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
lean_inc(v_stx_2238_);
v___x_2387_ = l_Lean_Syntax_getKind(v_stx_2238_);
v___x_2388_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_2386_, v___x_2387_);
lean_dec(v___x_2387_);
if (lean_obj_tag(v___x_2388_) == 1)
{
lean_object* v_val_2389_; lean_object* v_fst_2390_; lean_object* v_snd_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2422_; 
v_val_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_val_2389_);
lean_dec_ref(v___x_2388_);
v_fst_2390_ = lean_ctor_get(v_val_2389_, 0);
v_snd_2391_ = lean_ctor_get(v_val_2389_, 1);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_val_2389_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2393_ = v_val_2389_;
v_isShared_2394_ = v_isSharedCheck_2422_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_snd_2391_);
lean_inc(v_fst_2390_);
lean_dec(v_val_2389_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2422_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v_env_2396_; uint8_t v___x_2397_; uint8_t v___x_2398_; 
v___x_2395_ = lean_st_ref_get(v_a_2245_);
v_env_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc_ref(v_env_2396_);
lean_dec(v___x_2395_);
v___x_2397_ = 1;
lean_inc(v_snd_2391_);
v___x_2398_ = l_Lean_Environment_contains(v_env_2396_, v_snd_2391_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2402_; 
lean_dec(v_expType_x3f_2239_);
lean_dec(v_stx_2238_);
v___x_2399_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11);
v___x_2400_ = l_Lean_MessageData_ofName(v_snd_2391_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set_tag(v___x_2393_, 7);
lean_ctor_set(v___x_2393_, 1, v___x_2400_);
lean_ctor_set(v___x_2393_, 0, v___x_2399_);
v___x_2402_ = v___x_2393_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
v___x_2403_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15);
v___x_2406_ = l_Lean_MessageData_ofName(v_fst_2390_);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = l_Lean_MessageData_hint_x27(v___x_2409_);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2404_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v___x_2411_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
else
{
lean_del_object(v___x_2393_);
lean_dec(v_snd_2391_);
lean_dec(v_fst_2390_);
v___y_2376_ = v_a_2240_;
v___y_2377_ = v_a_2241_;
v___y_2378_ = v_a_2242_;
v___y_2379_ = v_a_2243_;
v___y_2380_ = v_a_2244_;
v___y_2381_ = v_a_2245_;
goto v___jp_2375_;
}
}
}
else
{
lean_dec(v___x_2388_);
v___y_2376_ = v_a_2240_;
v___y_2377_ = v_a_2241_;
v___y_2378_ = v_a_2242_;
v___y_2379_ = v_a_2243_;
v___y_2380_ = v_a_2244_;
v___y_2381_ = v_a_2245_;
goto v___jp_2375_;
}
v___jp_2247_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___boxed), 3, 1);
lean_closure_set(v___x_2255_, 0, v_stx_2238_);
v___x_2256_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v___x_2255_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2258_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref(v___x_2256_);
v___x_2258_ = l_Lean_Elab_Term_elabTerm(v_a_2257_, v_expType_x3f_2239_, v___y_2248_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
return v___x_2258_;
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_expType_x3f_2239_);
v_a_2259_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2256_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2256_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
v___jp_2267_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v_partialId_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2331_; 
v___x_2277_ = l_Lean_Syntax_getNumArgs(v___y_2276_);
v___x_2278_ = lean_unsigned_to_nat(2u);
v___x_2279_ = lean_nat_sub(v___x_2277_, v___x_2278_);
lean_dec(v___x_2277_);
v_partialId_2280_ = l_Lean_Syntax_getArg(v___y_2276_, v___x_2279_);
lean_dec(v___x_2279_);
v___x_2281_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___y_2276_);
lean_ctor_set(v___x_2281_, 1, v_partialId_2280_);
v___x_2282_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v___x_2281_, v___y_2271_, v___y_2268_, v___y_2275_, v___y_2269_, v___y_2270_, v___y_2274_);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2331_ == 0)
{
lean_object* v_unused_2332_; 
v_unused_2332_ = lean_ctor_get(v___x_2282_, 0);
lean_dec(v_unused_2332_);
v___x_2284_ = v___x_2282_;
v_isShared_2285_ = v_isSharedCheck_2331_;
goto v_resetjp_2283_;
}
else
{
lean_dec(v___x_2282_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2331_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2286_ = l_Lean_Syntax_getId(v___y_2272_);
v___x_2287_ = lean_erase_macro_scopes(v___x_2286_);
lean_inc(v___x_2287_);
lean_inc(v___y_2272_);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___y_2272_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set_tag(v___x_2284_, 6);
lean_ctor_set(v___x_2284_, 0, v___x_2288_);
v___x_2290_ = v___x_2284_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v_a_2293_; 
v___x_2291_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_2290_, v___y_2271_, v___y_2268_, v___y_2275_, v___y_2269_, v___y_2270_, v___y_2274_);
lean_dec_ref(v___x_2291_);
v___x_2292_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v___x_2287_, v___y_2274_);
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref(v___x_2292_);
if (lean_obj_tag(v_a_2293_) == 1)
{
lean_object* v_val_2294_; lean_object* v_metadata_2295_; lean_object* v_removedVersion_x3f_2296_; 
v_val_2294_ = lean_ctor_get(v_a_2293_, 0);
lean_inc(v_val_2294_);
lean_dec_ref(v_a_2293_);
v_metadata_2295_ = lean_ctor_get(v_val_2294_, 1);
lean_inc_ref(v_metadata_2295_);
lean_dec(v_val_2294_);
v_removedVersion_x3f_2296_ = lean_ctor_get(v_metadata_2295_, 2);
lean_inc(v_removedVersion_x3f_2296_);
lean_dec_ref(v_metadata_2295_);
if (lean_obj_tag(v_removedVersion_x3f_2296_) == 1)
{
lean_object* v_val_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_val_2297_ = lean_ctor_get(v_removedVersion_x3f_2296_, 0);
lean_inc(v_val_2297_);
lean_dec_ref(v_removedVersion_x3f_2296_);
v___x_2298_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1);
v___x_2299_ = l_Lean_MessageData_ofName(v___x_2287_);
v___x_2300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3);
v___x_2302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2300_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = l_Lean_stringToMessageData(v_val_2297_);
v___x_2304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2302_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5);
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v___y_2272_, v___x_2306_, v___y_2271_, v___y_2268_, v___y_2275_, v___y_2269_, v___y_2270_, v___y_2274_);
lean_dec(v___y_2272_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_dec_ref(v___x_2307_);
v___y_2248_ = v___y_2273_;
v___y_2249_ = v___y_2271_;
v___y_2250_ = v___y_2268_;
v___y_2251_ = v___y_2275_;
v___y_2252_ = v___y_2269_;
v___y_2253_ = v___y_2270_;
v___y_2254_ = v___y_2274_;
goto v___jp_2247_;
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec(v_expType_x3f_2239_);
lean_dec(v_stx_2238_);
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
else
{
lean_dec(v_removedVersion_x3f_2296_);
lean_dec(v___x_2287_);
lean_dec(v___y_2272_);
v___y_2248_ = v___y_2273_;
v___y_2249_ = v___y_2271_;
v___y_2250_ = v___y_2268_;
v___y_2251_ = v___y_2275_;
v___y_2252_ = v___y_2269_;
v___y_2253_ = v___y_2270_;
v___y_2254_ = v___y_2274_;
goto v___jp_2247_;
}
}
else
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_dec(v_a_2293_);
v___x_2316_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7);
v___x_2317_ = l_Lean_MessageData_ofName(v___x_2287_);
v___x_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9, &l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9_once, _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v___y_2272_, v___x_2320_, v___y_2271_, v___y_2268_, v___y_2275_, v___y_2269_, v___y_2270_, v___y_2274_);
lean_dec(v___y_2272_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_dec_ref(v___x_2321_);
v___y_2248_ = v___y_2273_;
v___y_2249_ = v___y_2271_;
v___y_2250_ = v___y_2268_;
v___y_2251_ = v___y_2275_;
v___y_2252_ = v___y_2269_;
v___y_2253_ = v___y_2270_;
v___y_2254_ = v___y_2274_;
goto v___jp_2247_;
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v_expType_x3f_2239_);
lean_dec(v_stx_2238_);
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
}
}
v___jp_2333_:
{
lean_object* v___x_2342_; uint8_t v___x_2343_; uint8_t v___x_2344_; 
v___x_2342_ = l_Lean_Syntax_getNumArgs(v_stx_2238_);
v___x_2343_ = lean_nat_dec_eq(v___x_2342_, v_snd_2341_);
v___x_2344_ = 1;
if (v___x_2343_ == 0)
{
lean_dec(v___x_2342_);
lean_inc(v_stx_2238_);
v___y_2268_ = v___y_2334_;
v___y_2269_ = v___y_2335_;
v___y_2270_ = v___y_2336_;
v___y_2271_ = v___y_2337_;
v___y_2272_ = v_fst_2340_;
v___y_2273_ = v___x_2344_;
v___y_2274_ = v___y_2339_;
v___y_2275_ = v___y_2338_;
v___y_2276_ = v_stx_2238_;
goto v___jp_2267_;
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2345_ = l_Lean_Syntax_getArgs(v_stx_2238_);
v___x_2346_ = lean_unsigned_to_nat(1u);
v___x_2347_ = lean_nat_sub(v___x_2342_, v___x_2346_);
lean_dec(v___x_2342_);
v___x_2348_ = lean_unsigned_to_nat(0u);
v___x_2349_ = l_Array_toSubarray___redArg(v___x_2345_, v___x_2348_, v___x_2347_);
v___x_2350_ = l_Subarray_copy___redArg(v___x_2349_);
lean_inc(v_stx_2238_);
v___x_2351_ = l_Lean_Syntax_setArgs(v_stx_2238_, v___x_2350_);
v___y_2268_ = v___y_2334_;
v___y_2269_ = v___y_2335_;
v___y_2270_ = v___y_2336_;
v___y_2271_ = v___y_2337_;
v___y_2272_ = v_fst_2340_;
v___y_2273_ = v___x_2344_;
v___y_2274_ = v___y_2339_;
v___y_2275_ = v___y_2338_;
v___y_2276_ = v___x_2351_;
goto v___jp_2267_;
}
}
v___jp_2352_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = lean_unsigned_to_nat(2u);
v___x_2360_ = l_Lean_Syntax_getArg(v_stx_2238_, v___x_2359_);
v___x_2361_ = lean_unsigned_to_nat(5u);
v___y_2334_ = v___y_2353_;
v___y_2335_ = v___y_2354_;
v___y_2336_ = v___y_2355_;
v___y_2337_ = v___y_2356_;
v___y_2338_ = v___y_2358_;
v___y_2339_ = v___y_2357_;
v_fst_2340_ = v___x_2360_;
v_snd_2341_ = v___x_2361_;
goto v___jp_2333_;
}
v___jp_2362_:
{
if (v___y_2369_ == 0)
{
lean_object* v___x_2370_; uint8_t v___x_2371_; 
v___x_2370_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
lean_inc(v_stx_2238_);
v___x_2371_ = l_Lean_Syntax_isOfKind(v_stx_2238_, v___x_2370_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2372_ = lean_unsigned_to_nat(1u);
v___x_2373_ = l_Lean_Syntax_getArg(v_stx_2238_, v___x_2372_);
v___x_2374_ = lean_unsigned_to_nat(4u);
v___y_2334_ = v___y_2363_;
v___y_2335_ = v___y_2364_;
v___y_2336_ = v___y_2365_;
v___y_2337_ = v___y_2366_;
v___y_2338_ = v___y_2368_;
v___y_2339_ = v___y_2367_;
v_fst_2340_ = v___x_2373_;
v_snd_2341_ = v___x_2374_;
goto v___jp_2333_;
}
else
{
v___y_2353_ = v___y_2363_;
v___y_2354_ = v___y_2364_;
v___y_2355_ = v___y_2365_;
v___y_2356_ = v___y_2366_;
v___y_2357_ = v___y_2367_;
v___y_2358_ = v___y_2368_;
goto v___jp_2352_;
}
}
else
{
v___y_2353_ = v___y_2363_;
v___y_2354_ = v___y_2364_;
v___y_2355_ = v___y_2365_;
v___y_2356_ = v___y_2366_;
v___y_2357_ = v___y_2367_;
v___y_2358_ = v___y_2368_;
goto v___jp_2352_;
}
}
v___jp_2375_:
{
lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
lean_inc(v_stx_2238_);
v___x_2383_ = l_Lean_Syntax_isOfKind(v_stx_2238_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
lean_inc(v_stx_2238_);
v___x_2385_ = l_Lean_Syntax_isOfKind(v_stx_2238_, v___x_2384_);
v___y_2363_ = v___y_2377_;
v___y_2364_ = v___y_2379_;
v___y_2365_ = v___y_2380_;
v___y_2366_ = v___y_2376_;
v___y_2367_ = v___y_2381_;
v___y_2368_ = v___y_2378_;
v___y_2369_ = v___x_2385_;
goto v___jp_2362_;
}
else
{
v___y_2363_ = v___y_2377_;
v___y_2364_ = v___y_2379_;
v___y_2365_ = v___y_2380_;
v___y_2366_ = v___y_2376_;
v___y_2367_ = v___y_2381_;
v___y_2368_ = v___y_2378_;
v___y_2369_ = v___x_2383_;
goto v___jp_2362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed(lean_object* v_stx_2423_, lean_object* v_expType_x3f_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(v_stx_2423_, v_expType_x3f_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(lean_object* v_00_u03b1_2433_, lean_object* v_x_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_2434_, v___y_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2438_, lean_object* v_x_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(v_00_u03b1_2438_, v_x_2439_, v___y_2440_, v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec_ref(v_x_2439_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(lean_object* v_00_u03b1_2443_, lean_object* v_ref_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_2444_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___boxed(lean_object* v_00_u03b1_2453_, lean_object* v_ref_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(v_00_u03b1_2453_, v_ref_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(lean_object* v_00_u03b1_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(v_00_u03b1_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(lean_object* v_00_u03b1_2481_, lean_object* v_x_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___boxed(lean_object* v_00_u03b1_2491_, lean_object* v_x_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(v_00_u03b1_2491_, v_x_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(lean_object* v_t_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_2501_, v___y_2507_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___boxed(lean_object* v_t_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(v_t_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(lean_object* v_00_u03b2_2519_, lean_object* v_m_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_2520_, v_a_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___boxed(lean_object* v_00_u03b2_2523_, lean_object* v_m_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(v_00_u03b2_2523_, v_m_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_m_2524_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(lean_object* v_00_u03b1_2527_, lean_object* v_msg_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___boxed(lean_object* v_00_u03b1_2537_, lean_object* v_msg_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(v_00_u03b1_2537_, v_msg_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(lean_object* v_cls_2547_, lean_object* v_msg_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_2547_, v_msg_2548_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___boxed(lean_object* v_cls_2557_, lean_object* v_msg_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(v_cls_2557_, v_msg_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(lean_object* v_as_2567_, lean_object* v_as_x27_2568_, lean_object* v_b_2569_, lean_object* v_a_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_2568_, v_b_2569_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___boxed(lean_object* v_as_2579_, lean_object* v_as_x27_2580_, lean_object* v_b_2581_, lean_object* v_a_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(v_as_2579_, v_as_x27_2580_, v_b_2581_, v_a_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v_as_2579_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(lean_object* v_00_u03b1_2591_, lean_object* v_ref_2592_, lean_object* v_msg_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_2592_, v_msg_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2602_, lean_object* v_ref_2603_, lean_object* v_msg_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(v_00_u03b1_2602_, v_ref_2603_, v_msg_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v_ref_2603_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(lean_object* v_ref_2613_, lean_object* v_msgData_2614_, uint8_t v_severity_2615_, uint8_t v_isSilent_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_2613_, v_msgData_2614_, v_severity_2615_, v_isSilent_2616_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___boxed(lean_object* v_ref_2625_, lean_object* v_msgData_2626_, lean_object* v_severity_2627_, lean_object* v_isSilent_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
uint8_t v_severity_boxed_2636_; uint8_t v_isSilent_boxed_2637_; lean_object* v_res_2638_; 
v_severity_boxed_2636_ = lean_unbox(v_severity_2627_);
v_isSilent_boxed_2637_ = lean_unbox(v_isSilent_2628_);
v_res_2638_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(v_ref_2625_, v_msgData_2626_, v_severity_boxed_2636_, v_isSilent_boxed_2637_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v_ref_2625_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(lean_object* v_00_u03b2_2639_, lean_object* v_a_2640_, lean_object* v_x_2641_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_2640_, v_x_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___boxed(lean_object* v_00_u03b2_2643_, lean_object* v_a_2644_, lean_object* v_x_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(v_00_u03b2_2643_, v_a_2644_, v_x_2645_);
lean_dec(v_x_2645_);
lean_dec(v_a_2644_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(lean_object* v_msgData_2647_, lean_object* v_macroStack_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_2647_, v_macroStack_2648_, v___y_2653_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___boxed(lean_object* v_msgData_2657_, lean_object* v_macroStack_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(v_msgData_2657_, v_macroStack_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
return v_res_2666_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(lean_object* v_00_u03b2_2667_, lean_object* v_x_2668_, lean_object* v_x_2669_){
_start:
{
uint8_t v___x_2670_; 
v___x_2670_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_2668_, v_x_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___boxed(lean_object* v_00_u03b2_2671_, lean_object* v_x_2672_, lean_object* v_x_2673_){
_start:
{
uint8_t v_res_2674_; lean_object* v_r_2675_; 
v_res_2674_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(v_00_u03b2_2671_, v_x_2672_, v_x_2673_);
lean_dec_ref(v_x_2673_);
lean_dec_ref(v_x_2672_);
v_r_2675_ = lean_box(v_res_2674_);
return v_r_2675_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(lean_object* v_00_u03b2_2676_, lean_object* v_x_2677_, size_t v_x_2678_, lean_object* v_x_2679_){
_start:
{
uint8_t v___x_2680_; 
v___x_2680_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_2677_, v_x_2678_, v_x_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___boxed(lean_object* v_00_u03b2_2681_, lean_object* v_x_2682_, lean_object* v_x_2683_, lean_object* v_x_2684_){
_start:
{
size_t v_x_22594__boxed_2685_; uint8_t v_res_2686_; lean_object* v_r_2687_; 
v_x_22594__boxed_2685_ = lean_unbox_usize(v_x_2683_);
lean_dec(v_x_2683_);
v_res_2686_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(v_00_u03b2_2681_, v_x_2682_, v_x_22594__boxed_2685_, v_x_2684_);
lean_dec_ref(v_x_2684_);
lean_dec_ref(v_x_2682_);
v_r_2687_ = lean_box(v_res_2686_);
return v_r_2687_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(lean_object* v_00_u03b2_2688_, lean_object* v_keys_2689_, lean_object* v_vals_2690_, lean_object* v_heq_2691_, lean_object* v_i_2692_, lean_object* v_k_2693_){
_start:
{
uint8_t v___x_2694_; 
v___x_2694_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_2689_, v_i_2692_, v_k_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___boxed(lean_object* v_00_u03b2_2695_, lean_object* v_keys_2696_, lean_object* v_vals_2697_, lean_object* v_heq_2698_, lean_object* v_i_2699_, lean_object* v_k_2700_){
_start:
{
uint8_t v_res_2701_; lean_object* v_r_2702_; 
v_res_2701_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(v_00_u03b2_2695_, v_keys_2696_, v_vals_2697_, v_heq_2698_, v_i_2699_, v_k_2700_);
lean_dec_ref(v_k_2700_);
lean_dec_ref(v_vals_2697_);
lean_dec_ref(v_keys_2696_);
v_r_2702_ = lean_box(v_res_2701_);
return v_r_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1(){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2711_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2712_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3));
v___x_2713_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2714_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2715_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2711_, v___x_2712_, v___x_2713_, v___x_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___boxed(lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3(){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2719_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2720_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5));
v___x_2721_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2722_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2723_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2719_, v___x_2720_, v___x_2721_, v___x_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3___boxed(lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5(){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2727_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2728_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7));
v___x_2729_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2730_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2731_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2727_, v___x_2728_, v___x_2729_, v___x_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5___boxed(lean_object* v_a_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7(){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2735_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2736_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9));
v___x_2737_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2738_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2739_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2735_, v___x_2736_, v___x_2737_, v___x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7___boxed(lean_object* v_a_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9(){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2743_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2744_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11));
v___x_2745_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2746_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2747_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2743_, v___x_2744_, v___x_2745_, v___x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9___boxed(lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11(){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2751_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2752_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13));
v___x_2753_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2));
v___x_2754_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed), 9, 0);
v___x_2755_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2751_, v___x_2752_, v___x_2753_, v___x_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11___boxed(lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
return v_res_2757_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2758_ = lean_box(0);
v___x_2759_ = l_Lean_Elab_abortTermExceptionId;
v___x_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
lean_ctor_set(v___x_2760_, 1, v___x_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg(){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = lean_obj_once(&l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0);
v___x_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___boxed(lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0(lean_object* v_00_u03b1_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___boxed(lean_object* v_00_u03b1_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0(v_00_u03b1_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(lean_object* v_t_2784_, lean_object* v_tp_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v___x_2793_; uint8_t v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
lean_inc_ref(v_tp_2785_);
v___x_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2793_, 0, v_tp_2785_);
v___x_2794_ = 1;
v___x_2795_ = lean_box(0);
v___x_2796_ = l_Lean_Elab_Term_elabTermEnsuringType(v_t_2784_, v___x_2793_, v___x_2794_, v___x_2794_, v___x_2795_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; uint8_t v___x_2805_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref(v___x_2796_);
v___x_2805_ = l_Lean_Expr_hasSyntheticSorry(v_a_2797_);
if (v___x_2805_ == 0)
{
v___y_2799_ = v_a_2788_;
v___y_2800_ = v_a_2789_;
v___y_2801_ = v_a_2790_;
v___y_2802_ = v_a_2791_;
goto v___jp_2798_;
}
else
{
lean_object* v___x_2806_; 
v___x_2806_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_dec_ref(v___x_2806_);
v___y_2799_ = v_a_2788_;
v___y_2800_ = v_a_2789_;
v___y_2801_ = v_a_2790_;
v___y_2802_ = v_a_2791_;
goto v___jp_2798_;
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v_a_2797_);
lean_dec_ref(v_tp_2785_);
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2806_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
v___jp_2798_:
{
uint8_t v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = 1;
v___x_2804_ = l_Lean_Meta_evalExpr___redArg(v_tp_2785_, v_a_2797_, v___x_2803_, v___x_2794_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
return v___x_2804_;
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec_ref(v_tp_2785_);
v_a_2815_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2796_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2796_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___boxed(lean_object* v_t_2823_, lean_object* v_tp_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_2823_, v_tp_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg(){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
v___x_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg___boxed(lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(lean_object* v_00_u03b1_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___boxed(lean_object* v_00_u03b1_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(v_00_u03b1_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(lean_object* v___y_2848_){
_start:
{
lean_object* v___x_2850_; lean_object* v_env_2851_; lean_object* v___x_2852_; lean_object* v_mainModule_2853_; lean_object* v___x_2854_; 
v___x_2850_ = lean_st_ref_get(v___y_2848_);
v_env_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc_ref(v_env_2851_);
lean_dec(v___x_2850_);
v___x_2852_ = l_Lean_Environment_header(v_env_2851_);
lean_dec_ref(v_env_2851_);
v_mainModule_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_mainModule_2853_);
lean_dec_ref(v___x_2852_);
v___x_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2854_, 0, v_mainModule_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___boxed(lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_2855_);
lean_dec(v___y_2855_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___boxed(lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(lean_object* v_t_2866_, lean_object* v___x_2867_, lean_object* v_x_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_2866_, v___x_2867_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed(lean_object* v_t_2877_, lean_object* v___x_2878_, lean_object* v_x_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(v_t_2877_, v___x_2878_, v_x_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec_ref(v_x_2879_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(lean_object* v_msgData_2888_, lean_object* v_macroStack_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v___x_2892_; lean_object* v_scopes_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v_opts_2896_; lean_object* v___x_2897_; uint8_t v___x_2898_; 
v___x_2892_ = lean_st_ref_get(v___y_2890_);
v_scopes_2893_ = lean_ctor_get(v___x_2892_, 2);
lean_inc(v_scopes_2893_);
lean_dec(v___x_2892_);
v___x_2894_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2895_ = l_List_head_x21___redArg(v___x_2894_, v_scopes_2893_);
lean_dec(v_scopes_2893_);
v_opts_2896_ = lean_ctor_get(v___x_2895_, 1);
lean_inc_ref(v_opts_2896_);
lean_dec(v___x_2895_);
v___x_2897_ = l_Lean_Elab_pp_macroStack;
v___x_2898_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_2896_, v___x_2897_);
lean_dec_ref(v_opts_2896_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec(v_macroStack_2889_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v_msgData_2888_);
return v___x_2899_;
}
else
{
if (lean_obj_tag(v_macroStack_2889_) == 0)
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2900_, 0, v_msgData_2888_);
return v___x_2900_;
}
else
{
lean_object* v_head_2901_; lean_object* v_after_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2917_; 
v_head_2901_ = lean_ctor_get(v_macroStack_2889_, 0);
lean_inc(v_head_2901_);
v_after_2902_ = lean_ctor_get(v_head_2901_, 1);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_head_2901_);
if (v_isSharedCheck_2917_ == 0)
{
lean_object* v_unused_2918_; 
v_unused_2918_ = lean_ctor_get(v_head_2901_, 0);
lean_dec(v_unused_2918_);
v___x_2904_ = v_head_2901_;
v_isShared_2905_ = v_isSharedCheck_2917_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_after_2902_);
lean_dec(v_head_2901_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2917_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2906_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
if (v_isShared_2905_ == 0)
{
lean_ctor_set_tag(v___x_2904_, 7);
lean_ctor_set(v___x_2904_, 1, v___x_2906_);
lean_ctor_set(v___x_2904_, 0, v_msgData_2888_);
v___x_2908_ = v___x_2904_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_msgData_2888_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v_msgData_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2909_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = l_Lean_MessageData_ofSyntax(v_after_2902_);
v___x_2912_ = l_Lean_indentD(v___x_2911_);
v_msgData_2913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2913_, 0, v___x_2910_);
lean_ctor_set(v_msgData_2913_, 1, v___x_2912_);
v___x_2914_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_2913_, v_macroStack_2889_);
v___x_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
return v___x_2915_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg___boxed(lean_object* v_msgData_2919_, lean_object* v_macroStack_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_msgData_2919_, v_macroStack_2920_, v___y_2921_);
lean_dec(v___y_2921_);
return v_res_2923_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2924_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0);
v___x_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
return v___x_2926_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2927_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1);
v___x_2928_ = lean_unsigned_to_nat(0u);
v___x_2929_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
lean_ctor_set(v___x_2929_, 2, v___x_2928_);
lean_ctor_set(v___x_2929_, 3, v___x_2928_);
lean_ctor_set(v___x_2929_, 4, v___x_2927_);
lean_ctor_set(v___x_2929_, 5, v___x_2927_);
lean_ctor_set(v___x_2929_, 6, v___x_2927_);
lean_ctor_set(v___x_2929_, 7, v___x_2927_);
lean_ctor_set(v___x_2929_, 8, v___x_2927_);
lean_ctor_set(v___x_2929_, 9, v___x_2927_);
return v___x_2929_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2930_ = lean_unsigned_to_nat(32u);
v___x_2931_ = lean_mk_empty_array_with_capacity(v___x_2930_);
v___x_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
return v___x_2932_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4(void){
_start:
{
size_t v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2933_ = ((size_t)5ULL);
v___x_2934_ = lean_unsigned_to_nat(0u);
v___x_2935_ = lean_unsigned_to_nat(32u);
v___x_2936_ = lean_mk_empty_array_with_capacity(v___x_2935_);
v___x_2937_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3);
v___x_2938_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v___x_2936_);
lean_ctor_set(v___x_2938_, 2, v___x_2934_);
lean_ctor_set(v___x_2938_, 3, v___x_2934_);
lean_ctor_set_usize(v___x_2938_, 4, v___x_2933_);
return v___x_2938_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2939_ = lean_box(1);
v___x_2940_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4);
v___x_2941_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1);
v___x_2942_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2940_);
lean_ctor_set(v___x_2942_, 2, v___x_2939_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(lean_object* v_msgData_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; lean_object* v_env_2947_; lean_object* v___x_2948_; lean_object* v_scopes_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v_opts_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2946_ = lean_st_ref_get(v___y_2944_);
v_env_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc_ref(v_env_2947_);
lean_dec(v___x_2946_);
v___x_2948_ = lean_st_ref_get(v___y_2944_);
v_scopes_2949_ = lean_ctor_get(v___x_2948_, 2);
lean_inc(v_scopes_2949_);
lean_dec(v___x_2948_);
v___x_2950_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2951_ = l_List_head_x21___redArg(v___x_2950_, v_scopes_2949_);
lean_dec(v_scopes_2949_);
v_opts_2952_ = lean_ctor_get(v___x_2951_, 1);
lean_inc_ref(v_opts_2952_);
lean_dec(v___x_2951_);
v___x_2953_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2);
v___x_2954_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5);
v___x_2955_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2955_, 0, v_env_2947_);
lean_ctor_set(v___x_2955_, 1, v___x_2953_);
lean_ctor_set(v___x_2955_, 2, v___x_2954_);
lean_ctor_set(v___x_2955_, 3, v_opts_2952_);
v___x_2956_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
lean_ctor_set(v___x_2956_, 1, v_msgData_2943_);
v___x_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___boxed(lean_object* v_msgData_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msgData_2958_, v___y_2959_);
lean_dec(v___y_2959_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(lean_object* v_msg_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lean_Elab_Command_getRef___redArg(v___y_2963_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v_macroStack_2968_; lean_object* v___x_2969_; lean_object* v_a_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2981_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref(v___x_2966_);
v_macroStack_2968_ = lean_ctor_get(v___y_2963_, 4);
v___x_2969_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msg_2962_, v___y_2964_);
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref(v___x_2969_);
lean_inc_n(v_macroStack_2968_, 2);
v___x_2971_ = l_Lean_Elab_getBetterRef(v_a_2967_, v_macroStack_2968_);
lean_dec(v_a_2967_);
v___x_2972_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_a_2970_, v_macroStack_2968_, v___y_2964_);
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_2981_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2981_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2979_; 
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2971_);
lean_ctor_set(v___x_2977_, 1, v_a_2973_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set_tag(v___x_2975_, 1);
lean_ctor_set(v___x_2975_, 0, v___x_2977_);
v___x_2979_ = v___x_2975_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec_ref(v_msg_2962_);
v_a_2982_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2966_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2966_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg___boxed(lean_object* v_msg_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(lean_object* v_ref_2995_, lean_object* v_msg_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_Elab_Command_getRef___redArg(v___y_2997_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v_fileName_3002_; lean_object* v_fileMap_3003_; lean_object* v_currRecDepth_3004_; lean_object* v_cmdPos_3005_; lean_object* v_macroStack_3006_; lean_object* v_quotContext_x3f_3007_; lean_object* v_currMacroScope_3008_; lean_object* v_snap_x3f_3009_; lean_object* v_cancelTk_x3f_3010_; uint8_t v_suppressElabErrors_3011_; lean_object* v_ref_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref(v___x_3000_);
v_fileName_3002_ = lean_ctor_get(v___y_2997_, 0);
v_fileMap_3003_ = lean_ctor_get(v___y_2997_, 1);
v_currRecDepth_3004_ = lean_ctor_get(v___y_2997_, 2);
v_cmdPos_3005_ = lean_ctor_get(v___y_2997_, 3);
v_macroStack_3006_ = lean_ctor_get(v___y_2997_, 4);
v_quotContext_x3f_3007_ = lean_ctor_get(v___y_2997_, 5);
v_currMacroScope_3008_ = lean_ctor_get(v___y_2997_, 6);
v_snap_x3f_3009_ = lean_ctor_get(v___y_2997_, 8);
v_cancelTk_x3f_3010_ = lean_ctor_get(v___y_2997_, 9);
v_suppressElabErrors_3011_ = lean_ctor_get_uint8(v___y_2997_, sizeof(void*)*10);
v_ref_3012_ = l_Lean_replaceRef(v_ref_2995_, v_a_3001_);
lean_dec(v_a_3001_);
lean_inc(v_cancelTk_x3f_3010_);
lean_inc(v_snap_x3f_3009_);
lean_inc(v_currMacroScope_3008_);
lean_inc(v_quotContext_x3f_3007_);
lean_inc(v_macroStack_3006_);
lean_inc(v_cmdPos_3005_);
lean_inc(v_currRecDepth_3004_);
lean_inc_ref(v_fileMap_3003_);
lean_inc_ref(v_fileName_3002_);
v___x_3013_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3013_, 0, v_fileName_3002_);
lean_ctor_set(v___x_3013_, 1, v_fileMap_3003_);
lean_ctor_set(v___x_3013_, 2, v_currRecDepth_3004_);
lean_ctor_set(v___x_3013_, 3, v_cmdPos_3005_);
lean_ctor_set(v___x_3013_, 4, v_macroStack_3006_);
lean_ctor_set(v___x_3013_, 5, v_quotContext_x3f_3007_);
lean_ctor_set(v___x_3013_, 6, v_currMacroScope_3008_);
lean_ctor_set(v___x_3013_, 7, v_ref_3012_);
lean_ctor_set(v___x_3013_, 8, v_snap_x3f_3009_);
lean_ctor_set(v___x_3013_, 9, v_cancelTk_x3f_3010_);
lean_ctor_set_uint8(v___x_3013_, sizeof(void*)*10, v_suppressElabErrors_3011_);
v___x_3014_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_2996_, v___x_3013_, v___y_2998_);
lean_dec_ref(v___x_3013_);
return v___x_3014_;
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v_msg_2996_);
v_a_3015_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3000_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3000_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg___boxed(lean_object* v_ref_3023_, lean_object* v_msg_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_ref_3023_, v_msg_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v_ref_3023_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(lean_object* v_cls_3029_, lean_object* v_msg_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_Elab_Command_getRef___redArg(v___y_3031_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3036_; lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3083_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref(v___x_3034_);
v___x_3036_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msg_3030_, v___y_3032_);
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3039_ = v___x_3036_;
v_isShared_3040_ = v_isSharedCheck_3083_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3036_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3083_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3041_; lean_object* v_traceState_3042_; lean_object* v_env_3043_; lean_object* v_messages_3044_; lean_object* v_scopes_3045_; lean_object* v_usedQuotCtxts_3046_; lean_object* v_nextMacroScope_3047_; lean_object* v_maxRecDepth_3048_; lean_object* v_ngen_3049_; lean_object* v_auxDeclNGen_3050_; lean_object* v_infoState_3051_; lean_object* v_snapshotTasks_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3082_; 
v___x_3041_ = lean_st_ref_take(v___y_3032_);
v_traceState_3042_ = lean_ctor_get(v___x_3041_, 9);
v_env_3043_ = lean_ctor_get(v___x_3041_, 0);
v_messages_3044_ = lean_ctor_get(v___x_3041_, 1);
v_scopes_3045_ = lean_ctor_get(v___x_3041_, 2);
v_usedQuotCtxts_3046_ = lean_ctor_get(v___x_3041_, 3);
v_nextMacroScope_3047_ = lean_ctor_get(v___x_3041_, 4);
v_maxRecDepth_3048_ = lean_ctor_get(v___x_3041_, 5);
v_ngen_3049_ = lean_ctor_get(v___x_3041_, 6);
v_auxDeclNGen_3050_ = lean_ctor_get(v___x_3041_, 7);
v_infoState_3051_ = lean_ctor_get(v___x_3041_, 8);
v_snapshotTasks_3052_ = lean_ctor_get(v___x_3041_, 10);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3054_ = v___x_3041_;
v_isShared_3055_ = v_isSharedCheck_3082_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_snapshotTasks_3052_);
lean_inc(v_traceState_3042_);
lean_inc(v_infoState_3051_);
lean_inc(v_auxDeclNGen_3050_);
lean_inc(v_ngen_3049_);
lean_inc(v_maxRecDepth_3048_);
lean_inc(v_nextMacroScope_3047_);
lean_inc(v_usedQuotCtxts_3046_);
lean_inc(v_scopes_3045_);
lean_inc(v_messages_3044_);
lean_inc(v_env_3043_);
lean_dec(v___x_3041_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3082_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
uint64_t v_tid_3056_; lean_object* v_traces_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3081_; 
v_tid_3056_ = lean_ctor_get_uint64(v_traceState_3042_, sizeof(void*)*1);
v_traces_3057_ = lean_ctor_get(v_traceState_3042_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v_traceState_3042_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3059_ = v_traceState_3042_;
v_isShared_3060_ = v_isSharedCheck_3081_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_traces_3057_);
lean_dec(v_traceState_3042_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3081_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; double v___x_3062_; uint8_t v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3071_; 
v___x_3061_ = lean_box(0);
v___x_3062_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
v___x_3063_ = 0;
v___x_3064_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_3065_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3065_, 0, v_cls_3029_);
lean_ctor_set(v___x_3065_, 1, v___x_3061_);
lean_ctor_set(v___x_3065_, 2, v___x_3064_);
lean_ctor_set_float(v___x_3065_, sizeof(void*)*3, v___x_3062_);
lean_ctor_set_float(v___x_3065_, sizeof(void*)*3 + 8, v___x_3062_);
lean_ctor_set_uint8(v___x_3065_, sizeof(void*)*3 + 16, v___x_3063_);
v___x_3066_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2));
v___x_3067_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3065_);
lean_ctor_set(v___x_3067_, 1, v_a_3037_);
lean_ctor_set(v___x_3067_, 2, v___x_3066_);
v___x_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3068_, 0, v_a_3035_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = l_Lean_PersistentArray_push___redArg(v_traces_3057_, v___x_3068_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3069_);
v___x_3071_ = v___x_3059_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3069_);
lean_ctor_set_uint64(v_reuseFailAlloc_3080_, sizeof(void*)*1, v_tid_3056_);
v___x_3071_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
lean_object* v___x_3073_; 
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 9, v___x_3071_);
v___x_3073_ = v___x_3054_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_env_3043_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_messages_3044_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_scopes_3045_);
lean_ctor_set(v_reuseFailAlloc_3079_, 3, v_usedQuotCtxts_3046_);
lean_ctor_set(v_reuseFailAlloc_3079_, 4, v_nextMacroScope_3047_);
lean_ctor_set(v_reuseFailAlloc_3079_, 5, v_maxRecDepth_3048_);
lean_ctor_set(v_reuseFailAlloc_3079_, 6, v_ngen_3049_);
lean_ctor_set(v_reuseFailAlloc_3079_, 7, v_auxDeclNGen_3050_);
lean_ctor_set(v_reuseFailAlloc_3079_, 8, v_infoState_3051_);
lean_ctor_set(v_reuseFailAlloc_3079_, 9, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3079_, 10, v_snapshotTasks_3052_);
v___x_3073_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
v___x_3074_ = lean_st_ref_set(v___y_3032_, v___x_3073_);
v___x_3075_ = lean_box(0);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3075_);
v___x_3077_ = v___x_3039_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref(v_msg_3030_);
lean_dec(v_cls_3029_);
v_a_3084_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3034_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3034_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___boxed(lean_object* v_cls_3092_, lean_object* v_msg_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(v_cls_3092_, v_msg_3093_, v___y_3094_, v___y_3095_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(lean_object* v_mod_3098_, uint8_t v_isMeta_3099_, lean_object* v_hint_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v___x_3104_; lean_object* v_env_3105_; uint8_t v_isExporting_3106_; lean_object* v___x_3107_; lean_object* v_env_3108_; lean_object* v___x_3109_; lean_object* v_entry_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___y_3115_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3104_ = lean_st_ref_get(v___y_3102_);
v_env_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc_ref(v_env_3105_);
lean_dec(v___x_3104_);
v_isExporting_3106_ = lean_ctor_get_uint8(v_env_3105_, sizeof(void*)*8);
lean_dec_ref(v_env_3105_);
v___x_3107_ = lean_st_ref_get(v___y_3102_);
v_env_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc_ref(v_env_3108_);
lean_dec(v___x_3107_);
v___x_3109_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
lean_inc(v_mod_3098_);
v_entry_3110_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3110_, 0, v_mod_3098_);
lean_ctor_set_uint8(v_entry_3110_, sizeof(void*)*1, v_isExporting_3106_);
lean_ctor_set_uint8(v_entry_3110_, sizeof(void*)*1 + 1, v_isMeta_3099_);
v___x_3111_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3112_ = lean_box(1);
v___x_3113_ = lean_box(0);
v___x_3141_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3109_, v___x_3111_, v_env_3108_, v___x_3112_, v___x_3113_);
v___x_3142_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_3141_, v_entry_3110_);
lean_dec(v___x_3141_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v_scopes_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v_opts_3149_; uint8_t v_hasTrace_3150_; 
v___x_3143_ = l_Lean_inheritedTraceOptions;
v___x_3144_ = lean_st_ref_get(v___x_3143_);
v___x_3145_ = lean_st_ref_get(v___y_3102_);
v_scopes_3146_ = lean_ctor_get(v___x_3145_, 2);
lean_inc(v_scopes_3146_);
lean_dec(v___x_3145_);
v___x_3147_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3148_ = l_List_head_x21___redArg(v___x_3147_, v_scopes_3146_);
lean_dec(v_scopes_3146_);
v_opts_3149_ = lean_ctor_get(v___x_3148_, 1);
lean_inc_ref(v_opts_3149_);
lean_dec(v___x_3148_);
v_hasTrace_3150_ = lean_ctor_get_uint8(v_opts_3149_, sizeof(void*)*1);
if (v_hasTrace_3150_ == 0)
{
lean_dec_ref(v_opts_3149_);
lean_dec(v___x_3144_);
lean_dec(v_hint_3100_);
lean_dec(v_mod_3098_);
v___y_3115_ = v___y_3102_;
goto v___jp_3114_;
}
else
{
lean_object* v_cls_3151_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v_cls_3151_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8));
v___x_3171_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
v___x_3172_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_3144_, v_opts_3149_, v___x_3171_);
lean_dec_ref(v_opts_3149_);
lean_dec(v___x_3144_);
if (v___x_3172_ == 0)
{
lean_dec(v_hint_3100_);
lean_dec(v_mod_3098_);
v___y_3115_ = v___y_3102_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3173_; lean_object* v___y_3175_; 
v___x_3173_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
if (v_isExporting_3106_ == 0)
{
lean_object* v___x_3182_; 
v___x_3182_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21));
v___y_3175_ = v___x_3182_;
goto v___jp_3174_;
}
else
{
lean_object* v___x_3183_; 
v___x_3183_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22));
v___y_3175_ = v___x_3183_;
goto v___jp_3174_;
}
v___jp_3174_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_inc_ref(v___y_3175_);
v___x_3176_ = l_Lean_stringToMessageData(v___y_3175_);
v___x_3177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3173_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18);
v___x_3179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
if (v_isMeta_3099_ == 0)
{
lean_object* v___x_3180_; 
v___x_3180_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19));
v___y_3158_ = v___x_3179_;
v___y_3159_ = v___x_3180_;
goto v___jp_3157_;
}
else
{
lean_object* v___x_3181_; 
v___x_3181_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20));
v___y_3158_ = v___x_3179_;
v___y_3159_ = v___x_3181_;
goto v___jp_3157_;
}
}
}
v___jp_3152_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___y_3153_);
lean_ctor_set(v___x_3155_, 1, v___y_3154_);
v___x_3156_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(v_cls_3151_, v___x_3155_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_dec_ref(v___x_3156_);
v___y_3115_ = v___y_3102_;
goto v___jp_3114_;
}
else
{
lean_dec_ref(v_entry_3110_);
return v___x_3156_;
}
}
v___jp_3157_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; uint8_t v___x_3166_; 
lean_inc_ref(v___y_3159_);
v___x_3160_ = l_Lean_stringToMessageData(v___y_3159_);
v___x_3161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___y_3158_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
v___x_3163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = l_Lean_MessageData_ofName(v_mod_3098_);
v___x_3165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3163_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = l_Lean_Name_isAnonymous(v_hint_3100_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
v___x_3168_ = l_Lean_MessageData_ofName(v_hint_3100_);
v___x_3169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3167_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___y_3153_ = v___x_3165_;
v___y_3154_ = v___x_3169_;
goto v___jp_3152_;
}
else
{
lean_object* v___x_3170_; 
lean_dec(v_hint_3100_);
v___x_3170_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13);
v___y_3153_ = v___x_3165_;
v___y_3154_ = v___x_3170_;
goto v___jp_3152_;
}
}
}
}
else
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
lean_dec_ref(v_entry_3110_);
lean_dec(v_hint_3100_);
lean_dec(v_mod_3098_);
v___x_3184_ = lean_box(0);
v___x_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
return v___x_3185_;
}
v___jp_3114_:
{
lean_object* v___x_3116_; lean_object* v_toEnvExtension_3117_; lean_object* v_env_3118_; lean_object* v_messages_3119_; lean_object* v_scopes_3120_; lean_object* v_usedQuotCtxts_3121_; lean_object* v_nextMacroScope_3122_; lean_object* v_maxRecDepth_3123_; lean_object* v_ngen_3124_; lean_object* v_auxDeclNGen_3125_; lean_object* v_infoState_3126_; lean_object* v_traceState_3127_; lean_object* v_snapshotTasks_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3140_; 
v___x_3116_ = lean_st_ref_take(v___y_3115_);
v_toEnvExtension_3117_ = lean_ctor_get(v___x_3111_, 0);
v_env_3118_ = lean_ctor_get(v___x_3116_, 0);
v_messages_3119_ = lean_ctor_get(v___x_3116_, 1);
v_scopes_3120_ = lean_ctor_get(v___x_3116_, 2);
v_usedQuotCtxts_3121_ = lean_ctor_get(v___x_3116_, 3);
v_nextMacroScope_3122_ = lean_ctor_get(v___x_3116_, 4);
v_maxRecDepth_3123_ = lean_ctor_get(v___x_3116_, 5);
v_ngen_3124_ = lean_ctor_get(v___x_3116_, 6);
v_auxDeclNGen_3125_ = lean_ctor_get(v___x_3116_, 7);
v_infoState_3126_ = lean_ctor_get(v___x_3116_, 8);
v_traceState_3127_ = lean_ctor_get(v___x_3116_, 9);
v_snapshotTasks_3128_ = lean_ctor_get(v___x_3116_, 10);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3130_ = v___x_3116_;
v_isShared_3131_ = v_isSharedCheck_3140_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_snapshotTasks_3128_);
lean_inc(v_traceState_3127_);
lean_inc(v_infoState_3126_);
lean_inc(v_auxDeclNGen_3125_);
lean_inc(v_ngen_3124_);
lean_inc(v_maxRecDepth_3123_);
lean_inc(v_nextMacroScope_3122_);
lean_inc(v_usedQuotCtxts_3121_);
lean_inc(v_scopes_3120_);
lean_inc(v_messages_3119_);
lean_inc(v_env_3118_);
lean_dec(v___x_3116_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3140_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v_asyncMode_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
v_asyncMode_3132_ = lean_ctor_get(v_toEnvExtension_3117_, 2);
v___x_3133_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3111_, v_env_3118_, v_entry_3110_, v_asyncMode_3132_, v___x_3113_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3133_);
v___x_3135_ = v___x_3130_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_messages_3119_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_scopes_3120_);
lean_ctor_set(v_reuseFailAlloc_3139_, 3, v_usedQuotCtxts_3121_);
lean_ctor_set(v_reuseFailAlloc_3139_, 4, v_nextMacroScope_3122_);
lean_ctor_set(v_reuseFailAlloc_3139_, 5, v_maxRecDepth_3123_);
lean_ctor_set(v_reuseFailAlloc_3139_, 6, v_ngen_3124_);
lean_ctor_set(v_reuseFailAlloc_3139_, 7, v_auxDeclNGen_3125_);
lean_ctor_set(v_reuseFailAlloc_3139_, 8, v_infoState_3126_);
lean_ctor_set(v_reuseFailAlloc_3139_, 9, v_traceState_3127_);
lean_ctor_set(v_reuseFailAlloc_3139_, 10, v_snapshotTasks_3128_);
v___x_3135_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = lean_st_ref_set(v___y_3115_, v___x_3135_);
v___x_3137_ = lean_box(0);
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1___boxed(lean_object* v_mod_3186_, lean_object* v_isMeta_3187_, lean_object* v_hint_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
uint8_t v_isMeta_boxed_3192_; lean_object* v_res_3193_; 
v_isMeta_boxed_3192_ = lean_unbox(v_isMeta_3187_);
v_res_3193_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_mod_3186_, v_isMeta_boxed_3192_, v_hint_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(lean_object* v___x_3194_, lean_object* v_declName_3195_, lean_object* v_as_3196_, size_t v_sz_3197_, size_t v_i_3198_, lean_object* v_b_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
uint8_t v___x_3203_; 
v___x_3203_ = lean_usize_dec_lt(v_i_3198_, v_sz_3197_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; 
lean_dec(v_declName_3195_);
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v_b_3199_);
return v___x_3204_;
}
else
{
lean_object* v___x_3205_; lean_object* v_modules_3206_; lean_object* v___x_3207_; lean_object* v_a_3208_; lean_object* v___x_3209_; lean_object* v_toImport_3210_; lean_object* v_module_3211_; uint8_t v___x_3212_; lean_object* v___x_3213_; 
v___x_3205_ = l_Lean_Environment_header(v___x_3194_);
v_modules_3206_ = lean_ctor_get(v___x_3205_, 3);
lean_inc_ref(v_modules_3206_);
lean_dec_ref(v___x_3205_);
v___x_3207_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3208_ = lean_array_uget_borrowed(v_as_3196_, v_i_3198_);
v___x_3209_ = lean_array_get(v___x_3207_, v_modules_3206_, v_a_3208_);
lean_dec_ref(v_modules_3206_);
v_toImport_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc_ref(v_toImport_3210_);
lean_dec(v___x_3209_);
v_module_3211_ = lean_ctor_get(v_toImport_3210_, 0);
lean_inc(v_module_3211_);
lean_dec_ref(v_toImport_3210_);
v___x_3212_ = 0;
lean_inc(v_declName_3195_);
v___x_3213_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_3211_, v___x_3212_, v_declName_3195_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3214_; size_t v___x_3215_; size_t v___x_3216_; 
lean_dec_ref(v___x_3213_);
v___x_3214_ = lean_box(0);
v___x_3215_ = ((size_t)1ULL);
v___x_3216_ = lean_usize_add(v_i_3198_, v___x_3215_);
v_i_3198_ = v___x_3216_;
v_b_3199_ = v___x_3214_;
goto _start;
}
else
{
lean_dec(v_declName_3195_);
return v___x_3213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2___boxed(lean_object* v___x_3218_, lean_object* v_declName_3219_, lean_object* v_as_3220_, lean_object* v_sz_3221_, lean_object* v_i_3222_, lean_object* v_b_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
size_t v_sz_boxed_3227_; size_t v_i_boxed_3228_; lean_object* v_res_3229_; 
v_sz_boxed_3227_ = lean_unbox_usize(v_sz_3221_);
lean_dec(v_sz_3221_);
v_i_boxed_3228_ = lean_unbox_usize(v_i_3222_);
lean_dec(v_i_3222_);
v_res_3229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v___x_3218_, v_declName_3219_, v_as_3220_, v_sz_boxed_3227_, v_i_boxed_3228_, v_b_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec_ref(v_as_3220_);
lean_dec_ref(v___x_3218_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(lean_object* v_declName_3230_, uint8_t v_isMeta_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v___x_3235_; lean_object* v_env_3239_; lean_object* v___y_3241_; lean_object* v___x_3254_; 
v___x_3235_ = lean_st_ref_get(v___y_3233_);
v_env_3239_ = lean_ctor_get(v___x_3235_, 0);
lean_inc_ref(v_env_3239_);
lean_dec(v___x_3235_);
v___x_3254_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3239_, v_declName_3230_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_dec_ref(v_env_3239_);
lean_dec(v_declName_3230_);
goto v___jp_3236_;
}
else
{
lean_object* v_val_3255_; lean_object* v___x_3256_; lean_object* v_modules_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v_val_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_val_3255_);
lean_dec_ref(v___x_3254_);
v___x_3256_ = l_Lean_Environment_header(v_env_3239_);
v_modules_3257_ = lean_ctor_get(v___x_3256_, 3);
lean_inc_ref(v_modules_3257_);
lean_dec_ref(v___x_3256_);
v___x_3258_ = lean_array_get_size(v_modules_3257_);
v___x_3259_ = lean_nat_dec_lt(v_val_3255_, v___x_3258_);
if (v___x_3259_ == 0)
{
lean_dec_ref(v_modules_3257_);
lean_dec(v_val_3255_);
lean_dec_ref(v_env_3239_);
lean_dec(v_declName_3230_);
goto v___jp_3236_;
}
else
{
lean_object* v___x_3260_; lean_object* v_env_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___y_3265_; 
v___x_3260_ = lean_st_ref_get(v___y_3233_);
v_env_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc_ref(v_env_3261_);
lean_dec(v___x_3260_);
v___x_3262_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2);
v___x_3263_ = lean_array_fget(v_modules_3257_, v_val_3255_);
lean_dec(v_val_3255_);
lean_dec_ref(v_modules_3257_);
if (v_isMeta_3231_ == 0)
{
lean_dec_ref(v_env_3261_);
v___y_3265_ = v_isMeta_3231_;
goto v___jp_3264_;
}
else
{
uint8_t v___x_3276_; 
lean_inc(v_declName_3230_);
v___x_3276_ = l_Lean_isMarkedMeta(v_env_3261_, v_declName_3230_);
if (v___x_3276_ == 0)
{
v___y_3265_ = v_isMeta_3231_;
goto v___jp_3264_;
}
else
{
uint8_t v___x_3277_; 
v___x_3277_ = 0;
v___y_3265_ = v___x_3277_;
goto v___jp_3264_;
}
}
v___jp_3264_:
{
lean_object* v_toImport_3266_; lean_object* v_module_3267_; lean_object* v___x_3268_; 
v_toImport_3266_ = lean_ctor_get(v___x_3263_, 0);
lean_inc_ref(v_toImport_3266_);
lean_dec(v___x_3263_);
v_module_3267_ = lean_ctor_get(v_toImport_3266_, 0);
lean_inc(v_module_3267_);
lean_dec_ref(v_toImport_3266_);
lean_inc(v_declName_3230_);
v___x_3268_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_3267_, v___y_3265_, v_declName_3230_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
lean_dec_ref(v___x_3268_);
v___x_3269_ = l_Lean_indirectModUseExt;
v___x_3270_ = lean_box(1);
v___x_3271_ = lean_box(0);
lean_inc_ref(v_env_3239_);
v___x_3272_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3262_, v___x_3269_, v_env_3239_, v___x_3270_, v___x_3271_);
v___x_3273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_3272_, v_declName_3230_);
lean_dec(v___x_3272_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3));
v___y_3241_ = v___x_3274_;
goto v___jp_3240_;
}
else
{
lean_object* v_val_3275_; 
v_val_3275_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_val_3275_);
lean_dec_ref(v___x_3273_);
v___y_3241_ = v_val_3275_;
goto v___jp_3240_;
}
}
else
{
lean_dec_ref(v_env_3239_);
lean_dec(v_declName_3230_);
return v___x_3268_;
}
}
}
}
v___jp_3236_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = lean_box(0);
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
return v___x_3238_;
}
v___jp_3240_:
{
lean_object* v___x_3242_; size_t v_sz_3243_; size_t v___x_3244_; lean_object* v___x_3245_; 
v___x_3242_ = lean_box(0);
v_sz_3243_ = lean_array_size(v___y_3241_);
v___x_3244_ = ((size_t)0ULL);
v___x_3245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v_env_3239_, v_declName_3230_, v___y_3241_, v_sz_3243_, v___x_3244_, v___x_3242_, v___y_3232_, v___y_3233_);
lean_dec_ref(v___y_3241_);
lean_dec_ref(v_env_3239_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v___x_3245_, 0);
lean_dec(v_unused_3253_);
v___x_3247_ = v___x_3245_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_dec(v___x_3245_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 0, v___x_3242_);
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3242_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
else
{
return v___x_3245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1___boxed(lean_object* v_declName_3278_, lean_object* v_isMeta_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
uint8_t v_isMeta_boxed_3283_; lean_object* v_res_3284_; 
v_isMeta_boxed_3283_ = lean_unbox(v_isMeta_3279_);
v_res_3284_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v_declName_3278_, v_isMeta_boxed_3283_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
return v_res_3284_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3));
v___x_3294_ = l_Lean_stringToMessageData(v___x_3293_);
return v___x_3294_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28));
v___x_3296_ = l_Lean_stringToMessageData(v___x_3295_);
return v___x_3296_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6));
v___x_3299_ = l_Lean_stringToMessageData(v___x_3298_);
return v___x_3299_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8));
v___x_3302_ = l_Lean_stringToMessageData(v___x_3301_);
return v___x_3302_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10));
v___x_3305_ = l_Lean_stringToMessageData(v___x_3304_);
return v___x_3305_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11);
v___x_3307_ = l_Lean_MessageData_note(v___x_3306_);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13));
v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_box(0);
v___x_3317_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3318_ = l_Lean_mkConst(v___x_3317_, v___x_3316_);
return v___x_3318_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19(void){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3320_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18));
v___x_3321_ = l_Lean_stringToMessageData(v___x_3320_);
return v___x_3321_;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20));
v___x_3324_ = l_Lean_stringToMessageData(v___x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(lean_object* v_x_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_){
_start:
{
lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3378_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2));
lean_inc(v_x_3325_);
v___x_3379_ = l_Lean_Syntax_isOfKind(v_x_3325_, v___x_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; 
lean_dec(v_x_3325_);
v___x_3380_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3380_;
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; 
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = l_Lean_Syntax_getArg(v_x_3325_, v___x_3381_);
v___x_3383_ = lean_unsigned_to_nat(1u);
v___x_3384_ = l_Lean_Syntax_matchesNull(v___x_3382_, v___x_3383_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3385_; 
lean_dec(v_x_3325_);
v___x_3385_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3385_;
}
else
{
lean_object* v___x_3386_; lean_object* v_id_3387_; lean_object* v___y_3389_; lean_object* v___y_3390_; uint8_t v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___x_3427_; uint8_t v___x_3428_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; 
v___x_3386_ = lean_unsigned_to_nat(2u);
v_id_3387_ = l_Lean_Syntax_getArg(v_x_3325_, v___x_3386_);
v___x_3427_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58));
lean_inc(v_id_3387_);
v___x_3428_ = l_Lean_Syntax_isOfKind(v_id_3387_, v___x_3427_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3456_; 
lean_dec(v_id_3387_);
lean_dec(v_x_3325_);
v___x_3456_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
return v___x_3456_;
}
else
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Lean_Elab_Command_getRef___redArg(v_a_3326_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3459_; lean_object* v_fileName_3460_; lean_object* v_fileMap_3461_; lean_object* v_currRecDepth_3462_; lean_object* v_cmdPos_3463_; lean_object* v_macroStack_3464_; lean_object* v_quotContext_x3f_3465_; lean_object* v_currMacroScope_3466_; lean_object* v_snap_x3f_3467_; lean_object* v_cancelTk_x3f_3468_; uint8_t v_suppressElabErrors_3469_; lean_object* v_env_3470_; lean_object* v_cmd_3471_; lean_object* v___x_3472_; lean_object* v_t_3473_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v_ref_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref(v___x_3457_);
v___x_3459_ = lean_st_ref_get(v_a_3327_);
v_fileName_3460_ = lean_ctor_get(v_a_3326_, 0);
v_fileMap_3461_ = lean_ctor_get(v_a_3326_, 1);
v_currRecDepth_3462_ = lean_ctor_get(v_a_3326_, 2);
v_cmdPos_3463_ = lean_ctor_get(v_a_3326_, 3);
v_macroStack_3464_ = lean_ctor_get(v_a_3326_, 4);
v_quotContext_x3f_3465_ = lean_ctor_get(v_a_3326_, 5);
v_currMacroScope_3466_ = lean_ctor_get(v_a_3326_, 6);
v_snap_x3f_3467_ = lean_ctor_get(v_a_3326_, 8);
v_cancelTk_x3f_3468_ = lean_ctor_get(v_a_3326_, 9);
v_suppressElabErrors_3469_ = lean_ctor_get_uint8(v_a_3326_, sizeof(void*)*10);
v_env_3470_ = lean_ctor_get(v___x_3459_, 0);
lean_inc_ref(v_env_3470_);
lean_dec(v___x_3459_);
v_cmd_3471_ = l_Lean_Syntax_getArg(v_x_3325_, v___x_3383_);
v___x_3472_ = lean_unsigned_to_nat(3u);
v_t_3473_ = l_Lean_Syntax_getArg(v_x_3325_, v___x_3472_);
lean_dec(v_x_3325_);
v_ref_3499_ = l_Lean_replaceRef(v_cmd_3471_, v_a_3458_);
lean_dec(v_a_3458_);
lean_dec(v_cmd_3471_);
lean_inc(v_cancelTk_x3f_3468_);
lean_inc(v_snap_x3f_3467_);
lean_inc(v_currMacroScope_3466_);
lean_inc(v_quotContext_x3f_3465_);
lean_inc(v_macroStack_3464_);
lean_inc(v_cmdPos_3463_);
lean_inc(v_currRecDepth_3462_);
lean_inc_ref(v_fileMap_3461_);
lean_inc_ref(v_fileName_3460_);
v___x_3500_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3500_, 0, v_fileName_3460_);
lean_ctor_set(v___x_3500_, 1, v_fileMap_3461_);
lean_ctor_set(v___x_3500_, 2, v_currRecDepth_3462_);
lean_ctor_set(v___x_3500_, 3, v_cmdPos_3463_);
lean_ctor_set(v___x_3500_, 4, v_macroStack_3464_);
lean_ctor_set(v___x_3500_, 5, v_quotContext_x3f_3465_);
lean_ctor_set(v___x_3500_, 6, v_currMacroScope_3466_);
lean_ctor_set(v___x_3500_, 7, v_ref_3499_);
lean_ctor_set(v___x_3500_, 8, v_snap_x3f_3467_);
lean_ctor_set(v___x_3500_, 9, v_cancelTk_x3f_3468_);
lean_ctor_set_uint8(v___x_3500_, sizeof(void*)*10, v_suppressElabErrors_3469_);
v___x_3501_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3502_ = l_Lean_Environment_contains(v_env_3470_, v___x_3501_, v___x_3428_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
lean_dec(v_t_3473_);
lean_dec(v_id_3387_);
v___x_3503_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21);
v___x_3504_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v___x_3503_, v___x_3500_, v_a_3327_);
lean_dec_ref(v___x_3500_);
return v___x_3504_;
}
else
{
v___y_3475_ = v___x_3500_;
v___y_3476_ = v_a_3327_;
goto v___jp_3474_;
}
v___jp_3474_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16));
v___x_3478_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v___x_3477_, v___x_3428_, v___y_3475_, v___y_3476_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v___x_3479_; lean_object* v___f_3480_; lean_object* v___x_3481_; 
lean_dec_ref(v___x_3478_);
v___x_3479_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17);
v___f_3480_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed), 10, 2);
lean_closure_set(v___f_3480_, 0, v_t_3473_);
lean_closure_set(v___f_3480_, 1, v___x_3479_);
v___x_3481_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_3480_, v___y_3475_, v___y_3476_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref(v___x_3481_);
v___x_3483_ = l_Lean_TSyntax_getId(v_id_3387_);
v___x_3484_ = l_Lean_Name_isAnonymous(v___x_3483_);
if (v___x_3484_ == 0)
{
v___y_3445_ = v___x_3483_;
v___y_3446_ = v_a_3482_;
v___y_3447_ = v___y_3475_;
v___y_3448_ = v___y_3476_;
goto v___jp_3444_;
}
else
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
lean_dec(v___x_3483_);
lean_dec(v_a_3482_);
v___x_3485_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19);
lean_inc(v_id_3387_);
v___x_3486_ = l_Lean_MessageData_ofSyntax(v_id_3387_);
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3485_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
v___x_3489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3487_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_3387_, v___x_3489_, v___y_3475_, v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v_id_3387_);
return v___x_3490_;
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec_ref(v___y_3475_);
lean_dec(v_id_3387_);
v_a_3491_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3481_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3481_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
else
{
lean_dec_ref(v___y_3475_);
lean_dec(v_t_3473_);
lean_dec(v_id_3387_);
return v___x_3478_;
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v_id_3387_);
lean_dec(v_x_3325_);
v_a_3505_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3457_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3457_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
v___jp_3388_:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Lean_Syntax_getTailPos_x3f(v_id_3387_, v___y_3391_);
lean_dec(v_id_3387_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_inc(v___y_3395_);
v___y_3330_ = v___y_3390_;
v___y_3331_ = v___y_3389_;
v___y_3332_ = v___y_3392_;
v___y_3333_ = v___y_3394_;
v___y_3334_ = v___y_3393_;
v___y_3335_ = v___y_3395_;
v___y_3336_ = v___y_3395_;
goto v___jp_3329_;
}
else
{
lean_object* v_val_3397_; 
v_val_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_val_3397_);
lean_dec_ref(v___x_3396_);
v___y_3330_ = v___y_3390_;
v___y_3331_ = v___y_3389_;
v___y_3332_ = v___y_3392_;
v___y_3333_ = v___y_3394_;
v___y_3334_ = v___y_3393_;
v___y_3335_ = v___y_3395_;
v___y_3336_ = v_val_3397_;
goto v___jp_3329_;
}
}
v___jp_3398_:
{
lean_object* v_fileMap_3403_; uint8_t v___x_3404_; lean_object* v___x_3405_; 
v_fileMap_3403_ = lean_ctor_get(v___y_3401_, 1);
lean_inc_ref(v_fileMap_3403_);
v___x_3404_ = 0;
v___x_3405_ = l_Lean_Syntax_getPos_x3f(v_id_3387_, v___x_3404_);
if (lean_obj_tag(v___x_3405_) == 0)
{
v___y_3389_ = v_fileMap_3403_;
v___y_3390_ = v___y_3399_;
v___y_3391_ = v___x_3404_;
v___y_3392_ = v___y_3401_;
v___y_3393_ = v___y_3402_;
v___y_3394_ = v___y_3400_;
v___y_3395_ = v___x_3381_;
goto v___jp_3388_;
}
else
{
lean_object* v_val_3406_; 
v_val_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_val_3406_);
lean_dec_ref(v___x_3405_);
v___y_3389_ = v_fileMap_3403_;
v___y_3390_ = v___y_3399_;
v___y_3391_ = v___x_3404_;
v___y_3392_ = v___y_3401_;
v___y_3393_ = v___y_3402_;
v___y_3394_ = v___y_3400_;
v___y_3395_ = v_val_3406_;
goto v___jp_3388_;
}
}
v___jp_3407_:
{
lean_object* v___x_3412_; lean_object* v_env_3413_; lean_object* v___x_3414_; lean_object* v_toEnvExtension_3415_; lean_object* v_asyncMode_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3412_ = lean_st_ref_get(v___y_3411_);
v_env_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc_ref(v_env_3413_);
lean_dec(v___x_3412_);
v___x_3414_ = l_Lean_errorExplanationExt;
v_toEnvExtension_3415_ = lean_ctor_get(v___x_3414_, 0);
v_asyncMode_3416_ = lean_ctor_get(v_toEnvExtension_3415_, 2);
v___x_3417_ = lean_box(1);
v___x_3418_ = lean_box(0);
v___x_3419_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3417_, v___x_3414_, v_env_3413_, v_asyncMode_3416_, v___x_3418_);
v___x_3420_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v___y_3408_, v___x_3419_);
lean_dec(v___x_3419_);
if (v___x_3420_ == 0)
{
v___y_3399_ = v___y_3408_;
v___y_3400_ = v___y_3409_;
v___y_3401_ = v___y_3410_;
v___y_3402_ = v___y_3411_;
goto v___jp_3398_;
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
lean_dec_ref(v___y_3409_);
v___x_3421_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4);
v___x_3422_ = l_Lean_MessageData_ofName(v___y_3408_);
v___x_3423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
v___x_3425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3423_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_3387_, v___x_3425_, v___y_3410_, v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v_id_3387_);
return v___x_3426_;
}
}
v___jp_3429_:
{
lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3434_ = l_Lean_Name_getNumParts(v___y_3430_);
v___x_3435_ = lean_nat_dec_eq(v___x_3434_, v___x_3386_);
lean_dec(v___x_3434_);
if (v___x_3435_ == 0)
{
if (v___x_3428_ == 0)
{
v___y_3408_ = v___y_3430_;
v___y_3409_ = v___y_3431_;
v___y_3410_ = v___y_3432_;
v___y_3411_ = v___y_3433_;
goto v___jp_3407_;
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_dec_ref(v___y_3431_);
v___x_3436_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
v___x_3437_ = l_Lean_MessageData_ofName(v___y_3430_);
v___x_3438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3436_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9);
v___x_3440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3438_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
v___x_3441_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12);
v___x_3442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3440_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
v___x_3443_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_3387_, v___x_3442_, v___y_3432_, v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v_id_3387_);
return v___x_3443_;
}
}
else
{
v___y_3408_ = v___y_3430_;
v___y_3409_ = v___y_3431_;
v___y_3410_ = v___y_3432_;
v___y_3411_ = v___y_3433_;
goto v___jp_3407_;
}
}
v___jp_3444_:
{
uint8_t v___x_3449_; 
v___x_3449_ = l_Lean_Name_hasMacroScopes(v___y_3445_);
if (v___x_3449_ == 0)
{
v___y_3430_ = v___y_3445_;
v___y_3431_ = v___y_3446_;
v___y_3432_ = v___y_3447_;
v___y_3433_ = v___y_3448_;
goto v___jp_3429_;
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
v___x_3450_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
lean_inc(v_id_3387_);
v___x_3451_ = l_Lean_MessageData_ofSyntax(v_id_3387_);
v___x_3452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3450_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = lean_obj_once(&l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14, &l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14_once, _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_3387_, v___x_3454_, v___y_3447_, v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v_id_3387_);
return v___x_3455_;
}
}
}
}
v___jp_3329_:
{
lean_object* v___x_3337_; lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3377_; 
lean_dec_ref(v___y_3332_);
v___x_3337_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_3334_);
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3377_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3377_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v_env_3343_; lean_object* v_messages_3344_; lean_object* v_scopes_3345_; lean_object* v_usedQuotCtxts_3346_; lean_object* v_nextMacroScope_3347_; lean_object* v_maxRecDepth_3348_; lean_object* v_ngen_3349_; lean_object* v_auxDeclNGen_3350_; lean_object* v_infoState_3351_; lean_object* v_traceState_3352_; lean_object* v_snapshotTasks_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3376_; 
v___x_3342_ = lean_st_ref_take(v___y_3334_);
v_env_3343_ = lean_ctor_get(v___x_3342_, 0);
v_messages_3344_ = lean_ctor_get(v___x_3342_, 1);
v_scopes_3345_ = lean_ctor_get(v___x_3342_, 2);
v_usedQuotCtxts_3346_ = lean_ctor_get(v___x_3342_, 3);
v_nextMacroScope_3347_ = lean_ctor_get(v___x_3342_, 4);
v_maxRecDepth_3348_ = lean_ctor_get(v___x_3342_, 5);
v_ngen_3349_ = lean_ctor_get(v___x_3342_, 6);
v_auxDeclNGen_3350_ = lean_ctor_get(v___x_3342_, 7);
v_infoState_3351_ = lean_ctor_get(v___x_3342_, 8);
v_traceState_3352_ = lean_ctor_get(v___x_3342_, 9);
v_snapshotTasks_3353_ = lean_ctor_get(v___x_3342_, 10);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3355_ = v___x_3342_;
v_isShared_3356_ = v_isSharedCheck_3376_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_snapshotTasks_3353_);
lean_inc(v_traceState_3352_);
lean_inc(v_infoState_3351_);
lean_inc(v_auxDeclNGen_3350_);
lean_inc(v_ngen_3349_);
lean_inc(v_maxRecDepth_3348_);
lean_inc(v_nextMacroScope_3347_);
lean_inc(v_usedQuotCtxts_3346_);
lean_inc(v_scopes_3345_);
lean_inc(v_messages_3344_);
lean_inc(v_env_3343_);
lean_dec(v___x_3342_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3376_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v_toEnvExtension_3358_; lean_object* v_asyncMode_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3357_ = l_Lean_errorExplanationExt;
v_toEnvExtension_3358_ = lean_ctor_get(v___x_3357_, 0);
v_asyncMode_3359_ = lean_ctor_get(v_toEnvExtension_3358_, 2);
v___x_3360_ = l_Lean_DeclarationRange_ofStringPositions(v___y_3331_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec(v___y_3335_);
v___x_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3361_, 0, v_a_3338_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
v___x_3363_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1));
v___x_3364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v___y_3333_);
lean_ctor_set(v___x_3364_, 2, v___x_3362_);
v___x_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___y_3330_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = lean_box(0);
v___x_3367_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3357_, v_env_3343_, v___x_3365_, v_asyncMode_3359_, v___x_3366_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3367_);
v___x_3369_ = v___x_3355_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3375_, 1, v_messages_3344_);
lean_ctor_set(v_reuseFailAlloc_3375_, 2, v_scopes_3345_);
lean_ctor_set(v_reuseFailAlloc_3375_, 3, v_usedQuotCtxts_3346_);
lean_ctor_set(v_reuseFailAlloc_3375_, 4, v_nextMacroScope_3347_);
lean_ctor_set(v_reuseFailAlloc_3375_, 5, v_maxRecDepth_3348_);
lean_ctor_set(v_reuseFailAlloc_3375_, 6, v_ngen_3349_);
lean_ctor_set(v_reuseFailAlloc_3375_, 7, v_auxDeclNGen_3350_);
lean_ctor_set(v_reuseFailAlloc_3375_, 8, v_infoState_3351_);
lean_ctor_set(v_reuseFailAlloc_3375_, 9, v_traceState_3352_);
lean_ctor_set(v_reuseFailAlloc_3375_, 10, v_snapshotTasks_3353_);
v___x_3369_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3373_; 
v___x_3370_ = lean_st_ref_set(v___y_3334_, v___x_3369_);
v___x_3371_ = lean_box(0);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3371_);
v___x_3373_ = v___x_3340_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed(lean_object* v_x_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(v_x_3513_, v_a_3514_, v_a_3515_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(lean_object* v_00_u03b1_3518_, lean_object* v_ref_3519_, lean_object* v_msg_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_ref_3519_, v_msg_3520_, v___y_3521_, v___y_3522_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___boxed(lean_object* v_00_u03b1_3525_, lean_object* v_ref_3526_, lean_object* v_msg_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(v_00_u03b1_3525_, v_ref_3526_, v_msg_3527_, v___y_3528_, v___y_3529_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v_ref_3526_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6(lean_object* v_msgData_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msgData_3532_, v___y_3534_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___boxed(lean_object* v_msgData_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6(v_msgData_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(lean_object* v_00_u03b1_3542_, lean_object* v_msg_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_3543_, v___y_3544_, v___y_3545_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___boxed(lean_object* v_00_u03b1_3548_, lean_object* v_msg_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(v_00_u03b1_3548_, v_msg_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7(lean_object* v_msgData_3554_, lean_object* v_macroStack_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_msgData_3554_, v_macroStack_3555_, v___y_3557_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___boxed(lean_object* v_msgData_3560_, lean_object* v_macroStack_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7(v_msgData_3560_, v_macroStack_3561_, v___y_3562_, v___y_3563_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1(){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3573_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3574_ = ((lean_object*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2));
v___x_3575_ = ((lean_object*)(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1));
v___x_3576_ = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed), 4, 0);
v___x_3577_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3573_, v___x_3574_, v___x_3575_, v___x_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___boxed(lean_object* v_a_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
return v_res_3579_;
}
}
lean_object* runtime_initialize_Lean_Widget_UserWidget(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ErrorExplanation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
